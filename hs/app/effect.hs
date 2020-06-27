{-# LANGUAGE ScopedTypeVariables, OverloadedStrings #-}

import System.Environment
import Control.Monad
import Control.Concurrent
import Data.IORef
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
  args <- getArgs
  ecred <- credentialLoadX509 (args !! 0) (args !! 1)
  newAccepts <- newIORef []
  received <- newEmptyMVar
  case ecred of
    Right (cert,priv) -> do
      sock <- socket AF_INET Stream 0
      bind sock (SockAddrInet 8001 iNADDR_ANY)  
      listen sock 2
      forkIO (core [] (Left (((((),1000), 1000), cert), priv)) NewAccept (unsafeCoerce ()) newAccepts received)
      forever $ do
        (s,a) <- accept sock
        modifyIORef newAccepts ((s,show a):)
        print a
        putStrLn ""
--        forkFinally (core s (Left (((), cert), priv)) RecvClientHello (unsafeCoerce 1)) (const $ close s)
    Left s ->
      putStrLn s

core sock x ef (r::Any) newAccepts received = do
  case main_loop_step x ef r of
    Right res -> do
      print res
      putStrLn "\nDone"
      forM_ sock (\(_,s) -> close s)
    Left (next, Nothing) -> core sock next NewAccept (unsafeCoerce ()) newAccepts received
    Left (next, Just (ExistT e a)) ->
      case e of
        NewAccept -> do
          l <- readIORef newAccepts
          case l of
            [] -> threadDelay 100000 >> core sock next NewAccept (unsafeCoerce Nothing) newAccepts received
            (s,adr):l' -> do
              writeIORef newAccepts l'
              putStrLn $ "accepted" ++ show adr
              core ((adr,s):sock) next NewAccept (unsafeCoerce (Just adr)) newAccepts received
        Receive -> do
          r <- tryTakeMVar received
          case r of
            Just (adr,p) ->
              case p of
                _ -> putStrLn $ "received " ++ show adr
            _ -> return ()
          core sock next Receive (unsafeCoerce r) newAccepts received
        Perform -> do
          let (adr,ea) = unsafeCoerce a :: (String, Args_tls')
          putStrLn $ "perform " ++ show ea ++ show adr
          case ea of
            (Left (Left (Left (Left (Right a'))))) -> do
              putStrLn "RecvData"
              let ms = lookup adr sock
              case ms of
                Just s -> do
                  forkIO $ SB.recv s 65536 >>= \ch -> putMVar received (adr,Left (Left (Right ch)))
                  return ()
                Nothing -> error "no socket"
            (Left (Left (Left (Left (Left (Right a')))))) ->
              putStrLn "GetRandomBytes" >> getRandomBytes a' >>= \(v::B.ByteString) -> forkIO (putMVar received (adr, Left (Left (Right v)))) >> return ()
            (Left (Left (Left (Left (Left (Left (a'))))))) ->
              case lookup adr sock of
                Just s -> do
                  putStrLn "SendPacket"
                  let (pkt,m) = a' :: (I.Packet13, Maybe (((TLS.Hash,TLS.Cipher),B.ByteString),Int))
                  let encoded =
                        case pkt of
                          I.Handshake13 [hs] -> I.encodeHandshake13 hs
                          I.ChangeCipherSpec13 -> I.encodeChangeCipherSpec
                  bs <- encodePacket13 (pkt,m)
                  case bs of
                    Right b -> do
                      forkIO $ SB.sendAll s b >> putMVar received (adr, Left (Left (Right encoded)))
                      return ()
            (Left (Left (Left (Right a')))) ->
              I.groupGetPubShared a' >>= \p -> forkIO (putMVar received (adr,(Left (Left (Left (Left p)))))) >> return ()
            (Left (Left (Right a'))) ->
              makeCertVerify a' >>= \c -> forkIO (putMVar received (adr,(Left $ Left $ Left $ Right c))) >> return ()
          core sock next Perform (unsafeCoerce ()) newAccepts received

recvBytes :: Socket -> Int -> IO B.ByteString
recvBytes sock n = B.concat <$> loop n
  where loop 0 = return []
        loop left = do
          r <- (SB.recv sock left:: IO B.ByteString)
          if B.null r
            then return []
            else (r:) <$> loop (left - B.length r)

--recvClientHello sock = do
--  ehss <- recvHandshakes sock Nothing
--  case ehss of
--    Right [ch@(I.ClientHello13 ver cRandom session cipherIDs exts)] -> do
--      putStr $ show ch ++ "\n"
--      return (Build_ClientHelloMsg session exts cipherIDs, I.encodeHandshake13 ch)

recvFinished :: Socket -> Maybe ((TLS.Hash,TLS.Cipher), B.ByteString) -> IO B.ByteString
recvFinished sock m = do
  ehss <- recvHandshakes sock m
  case ehss of
    Right [I.Finished13 dat] ->
      return dat
    Left e -> do
      print e
      return ""

recvAppData :: Socket -> Maybe ((TLS.Hash, TLS.Cipher), B.ByteString) -> IO B.ByteString
recvAppData sock m = do
  ehss <- recvRecord sock m
  case ehss of
    Right (I.Record ProtocolType_AppData _ dat) ->
      return (I.fragmentGetBytes dat)
    x -> do
      print x
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
    Right p -> print p >> return (Right [])

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
