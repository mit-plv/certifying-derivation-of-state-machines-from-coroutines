{-# LANGUAGE ScopedTypeVariables, OverloadedStrings #-}

import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Network.Socket
import qualified Network.Socket.ByteString as SB
import Data.ByteString.Builder
import Network.TLS
import qualified Network.TLS.Internal as I
import Crypto.Random
import qualified Crypto.PubKey.RSA as RSA
import qualified Crypto.Hash.Algorithms as A
import qualified Crypto.PubKey.RSA.PSS as RSA
import TLS
import Encrypt
import Data.IORef
import Helper

main :: IO ()
main = withSocketsDo $ do
  ms <- newIORef $ fromInteger 0
  sock <- socket AF_INET Stream 0
  bind sock (SockAddrInet 8001 iNADDR_ANY)  
  listen sock 2
  (s,_) <- accept sock
  core s (Left ()) RecvClientHello ms (unsafeCoerce 1) 
--  ehs <- recvHandshakes s
  --SB.sendAll s $ C.pack "this is a dummy message"
--  case ehs of
    --Right hs -> print hs

core sock x ef ms (r::Any) = do
  case doHandshake_step x ef (unsafeCoerce r) of
    Right res ->
      case res of
        Just (((msgs,hashed),cv@(I.CertVerify13 _ sig)), pub) -> do
          putStrLn "messages:"
          print $ msgs
          putStrLn "\nhashed:"
          print hashed
          putStrLn "\ncertverify:"
          print cv 
          putStrLn "\nverify:"
          print $ RSA.verify (RSA.defaultPSSParams A.SHA384) pub (makeTarget hashed) sig
          putStrLn "\nDone"
        _ -> putStrLn "Done"
    Left (next, Nothing) -> core sock next RecvClientHello ms (unsafeCoerce 0) 
    Left (next, Just (ExistT e a)) ->
      case e of
        RecvClientHello -> do
          putStrLn "receive"
          ch <- recvClientHello sock
          core sock next RecvClientHello ms (unsafeCoerce ch) 
        RecvFinished -> do
          fin <- recvFinished sock (unsafeCoerce a)
          core sock next RecvFinished ms (unsafeCoerce fin)
        RecvCCS -> do
          recvCCS sock
          core sock next RecvCCS ms (unsafeCoerce ())
        GetRandomBytes -> do
          v <- (getRandomBytes (unsafeCoerce a) :: IO B.ByteString)
          core sock next GetRandomBytes ms (unsafeCoerce v)
        SendPacket -> do
          putStrLn "send"
          let (pkt,m) = unsafeCoerce a :: (I.Packet13, Maybe ((TLS.Hash,TLS.Cipher),B.ByteString))
          let encoded =
                case pkt of
                  I.Handshake13 [hs] -> I.encodeHandshake13 hs
                  I.ChangeCipherSpec13 -> I.encodeChangeCipherSpec
          bs <- encodePacket13 (pkt,m) ms
          print pkt
          putStrLn ""
          case bs of
            Right b -> do
              SB.sendAll sock b
              core sock next SendPacket ms (unsafeCoerce encoded)
        GenKeys ->
          genKeys >>= core sock next GenKeys ms . unsafeCoerce 
        GroupGetPubShared ->
          I.groupGetPubShared (unsafeCoerce a) >>= core sock next GroupGetPubShared ms . unsafeCoerce

recvBytes :: Socket -> Int -> IO B.ByteString
recvBytes sock n = B.concat <$> loop n
  where loop 0 = return []
        loop left = do
          r <- (SB.recv sock left:: IO B.ByteString)
          if B.null r
            then return []
            else (r:) <$> loop (left - B.length r)

recvClientHello sock = do
  ehss <- recvHandshakes sock Nothing
  case ehss of
    Right [ch@(I.ClientHello13 ver cRandom session cipherIDs exts)] -> do
      putStr $ show ch ++ "\n"
      return (Build_ClientHelloMsg session exts cipherIDs, I.encodeHandshake13 ch)

recvFinished :: Socket -> Maybe ((TLS.Hash,TLS.Cipher), B.ByteString) -> IO B.ByteString
recvFinished sock m = do
  ehss <- recvHandshakes sock m
  case ehss of
    Right [I.Finished13 dat] ->
      return dat
    Left e -> do
      print e
      return ""

recvCCS :: Socket -> IO ()
recvCCS sock = do
  erecord <- recvRecord sock Nothing
  case erecord of
    Right (I.Record ProtocolType_ChangeCipherSpec _ _) -> return ()
    _ -> putStrLn "error"

recvHandshakes :: Socket -> Maybe ((TLS.Hash,TLS.Cipher), B.ByteString) ->  IO (Either TLSError [I.Handshake13])
recvHandshakes sock m = do
  erecord <- recvRecord sock m
  case erecord of
    Left err -> return $ Left err
    Right (I.Record ProtocolType_Handshake ver fragment) ->
        return $ I.decodeHandshakes13 $ I.fragmentGetBytes fragment


recvRecord :: Socket -> Maybe ((TLS.Hash,TLS.Cipher), B.ByteString) -> IO (Either TLSError (I.Record I.Plaintext))
recvRecord sock m = recvBytes sock 5 >>= recvLengthE . I.decodeHeader
  where recvLengthE = either (return . Left) recvLength
        recvLength header@(Header _ _ readlen)
          | readlen > 16384 + 256 = return $ Left maximumSizeExceeded
          | otherwise = do
                bs <- recvBytes sock (fromIntegral readlen)
                case m of
                  Nothing ->
                    case I.runRecordM (I.decodeRecordM header bs) newRecordOptions I.newRecordState of
                            Left err -> return $ Left err
                            Right (a,_) -> return $ Right a
                  Just ((h,cipher),secret) ->
                    let bulk    = cipherBulk cipher
                        keySize = bulkKeySize bulk
                        ivSize  = max 8 (bulkIVSize bulk + bulkExplicitIV bulk)
                        key = I.hkdfExpandLabel h secret "key" "" keySize
                        iv  = I.hkdfExpandLabel h secret "iv"  "" ivSize
                        cst = I.CryptState {
                            I.cstKey       = bulkInit bulk BulkDecrypt key
                          , I.cstIV        = iv
                          , I.cstMacSecret = secret
                          }
                        rst = I.RecordState {
                            I.stCryptState  = cst
                          , I.stMacState    = I.MacState { I.msSequence = 0 }
                          , I.stCipher      = Just cipher
                          , I.stCompression = nullCompression
                          }
                    in
                    case I.runRecordM (I.decodeRecordM header bs) newRecordOptions rst of
                            Left err -> return $ Left err
                            Right (a,_) -> return $ Right a

maximumSizeExceeded :: TLSError
maximumSizeExceeded = Error_Protocol ("record exceeding maximum size", True, RecordOverflow)


genKeys :: IO (RSA.PublicKey, RSA.PrivateKey)
genKeys = RSA.generate 256 0x10001
