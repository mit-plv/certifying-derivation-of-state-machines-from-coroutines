{-# LANGUAGE ScopedTypeVariables #-}

import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Network.Socket
import qualified Network.Socket.ByteString as SB
import Network.TLS
import qualified Network.TLS.Internal as I
import Crypto.Random
import TLS

main :: IO ()
main = withSocketsDo $ do
  sock <- socket AF_INET Stream 0
  bind sock (SockAddrInet 8001 iNADDR_ANY)  
  listen sock 2
  (s,_) <- accept sock
  core s (Left ()) RecvClientHello (unsafeCoerce 1)
--  ehs <- recvHandshakes s
  --SB.sendAll s $ C.pack "this is a dummy message"
--  case ehs of
    --Right hs -> print hs

core sock x ef (r::Any) = do
  case doHandshake_step x ef (unsafeCoerce r) of
    Right res -> putStrLn "done"
    Left (next, Nothing) -> core sock next RecvClientHello (unsafeCoerce 0)
    Left (next, Just (ExistT e a)) ->
      case e of
        RecvClientHello ->
          putStrLn "receive" >> recvClientHello sock >>= core sock next RecvClientHello . unsafeCoerce
        GetRandomBytes -> do
          putStrLn "getrandom"
          v <- (getRandomBytes (unsafeCoerce a) :: IO B.ByteString)
          putStrLn "getrandom finished"
          core sock next GetRandomBytes (unsafeCoerce v)
        SendPacket -> do
          putStrLn "send"
          bs <- encodePacket13 $ unsafeCoerce a
          print (unsafeCoerce a :: I.Packet13)
          putStrLn "\n"
          case bs of
            Right b ->
              SB.sendAll sock b
          core sock next SendPacket $ unsafeCoerce ()

recvBytes :: Socket -> Int -> IO B.ByteString
recvBytes sock n = B.concat <$> loop n
  where loop 0 = return []
        loop left = do
          r <- (SB.recv sock left:: IO B.ByteString)
          if B.null r
            then return []
            else (r:) <$> loop (left - B.length r)

recvClientHello sock = do
  ehss <- recvHandshakes sock
  case ehss of
    Right [I.ClientHello13 ver cRandom session cipherIDs exts] ->
      return $ Build_ClientHelloMsg session exts cipherIDs

recvHandshakes :: Socket -> IO (Either TLSError [I.Handshake13])
recvHandshakes sock = do
  erecord <- recvRecord sock
  case erecord of
    Left err -> return $ Left err
    Right (I.Record ProtocolType_Handshake ver fragment) ->
        return $ I.decodeHandshakes13 $ I.fragmentGetBytes fragment

recvRecord :: Socket -> IO (Either TLSError (I.Record I.Plaintext))
recvRecord sock = recvBytes sock 5 >>= recvLengthE . I.decodeHeader
  where recvLengthE = either (return . Left) recvLength
        recvLength header@(Header _ _ readlen)
          | readlen > 16384 + 256 = return $ Left maximumSizeExceeded
          | otherwise = do
                bs <- recvBytes sock (fromIntegral readlen)
                case I.runRecordM (I.decodeRecordM header bs) newRecordOptions I.newRecordState of
                        Left err -> return $ Left err
                        Right (a,_) -> return $ Right a

newRecordOptions = I.RecordOptions { I.recordVersion = TLS13, I.recordTLS13 = True }

maximumSizeExceeded :: TLSError
maximumSizeExceeded = Error_Protocol ("record exceeding maximum size", True, RecordOverflow)


encodePacket13 :: I.Packet13 -> IO (Either TLSError B.ByteString)
encodePacket13 pkt = do
    let pt = I.contentType pkt
        mkRecord bs = I.Record pt TLS12 (I.fragmentPlaintext bs)
        records = map mkRecord $ packetToFragments 16384 pkt
    fmap B.concat <$> I.forEitherM records encodeRecord

prepareRecord :: I.RecordM a -> IO (Either TLSError a)
prepareRecord rm = case I.runRecordM rm newRecordOptions I.newRecordState of
                        Left err -> return $ Left err
                        Right (a,_) -> return $ Right a

encodeRecord :: I.Record I.Plaintext -> IO (Either TLSError B.ByteString)
encodeRecord = prepareRecord . I.encodeRecordM

packetToFragments :: Int -> I.Packet13 -> [B.ByteString]
packetToFragments len (I.Handshake13 hss)  =
    I.getChunks len $ B.concat $ map I.encodeHandshake13 hss
packetToFragments _   (I.Alert13 a)        = [I.encodeAlerts a]
packetToFragments _   (I.AppData13 x)      = [x]
packetToFragments _   I.ChangeCipherSpec13 = [I.encodeChangeCipherSpec]

