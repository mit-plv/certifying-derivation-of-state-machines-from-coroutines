{-# LANGUAGE ScopedTypeVariables, OverloadedStrings #-}

import System.Environment
import Control.Monad
import Control.Concurrent
import Data.IORef
import Data.List
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
      bind sock (SockAddrInet 4433 iNADDR_ANY)  
      listen sock 2
      forkIO (core [] (Left ((((((),100000), 100000), 100000), cert), priv)) Receive (unsafeCoerce ()) newAccepts received )
      forever $ do
        (s,a) <- accept sock
        modifyIORef newAccepts $ \l -> (s,show a):l
        putStrLn (show a)
    Left s ->
      putStrLn s

core sock x ef (r::Any) newAccepts received = do
  case main_loop_step x ef r of
    Right res -> do
      print res
      putStrLn "\nDone"
      forM_ sock (\(_,s) -> close s)
    Left (next, Nothing) -> core sock next Skip (unsafeCoerce ()) newAccepts received 
    Left (next, Just (ExistT e a)) ->
      case e of
        Skip -> core sock next Skip (unsafeCoerce ()) newAccepts received 
        Accept -> do
          l <- readIORef newAccepts
          case l of
            [] -> threadDelay 10000 >> core sock next Accept (unsafeCoerce Nothing) newAccepts received 
            (s,adr):l' -> do
              writeIORef newAccepts l'
              putStrLn $ " accepted" ++ show adr
              core ((adr,s):sock) next Accept (unsafeCoerce (Just adr)) newAccepts received 
        Receive -> do
          r <- tryTakeMVar received
          case r of
            (Just (adr,p)) ->
              case lookup adr sock of
                Just _ -> do
                  --putStrLn $ " received " ++ show adr
                  core sock next Receive (unsafeCoerce r) newAccepts received 
                Nothing -> do
                  --putStrLn $ " received but not found " ++ show adr
                  core sock next Receive (unsafeCoerce Nothing) newAccepts received 
            Nothing -> core sock next Receive (unsafeCoerce Nothing) newAccepts received 
        Perform -> do
          let (adr,ea) = unsafeCoerce a :: (String, Args_tls)
          --putStrLn $ " perform " ++ show adr
          case ea of
            RecvData a' -> do
              putStrLn "RecvData"
              case lookup adr sock of
                Just s -> do
                  forkIO $ do
                    ch <- SB.recv s (16384 + 256)
                    putStrLn $ show $ toLazyByteString $ byteStringHex ch
                    putMVar received (adr, FromRecvData ch)
                  return ()
                Nothing -> error "no socket"
            GetRandomBytes a' ->
              putStrLn (if a' == 0 then "Skip" else "GetRandomBytes") >> (if a' == 0 then return "" else getRandomBytes a') >>= \(v::B.ByteString) -> forkIO (putMVar received (adr, FromGetRandomBytes v)) >> return ()
            SendData a' ->
              case lookup adr sock of
                Just s -> do
                  let (pkt,m) = a' :: (I.Packet13, Maybe (((TLS.Hash,TLS.Cipher),B.ByteString),Int))
                  putStrLn $ "SendPacket " ++ show pkt
                  let encoded =
                        case pkt of
                          I.Handshake13 [hs] -> I.encodeHandshake13 hs
                          I.ChangeCipherSpec13 -> I.encodeChangeCipherSpec
                  bs <- encodePacket13 (pkt,m)
                  case bs of
                    Right b -> do
                          forkIO $ SB.sendAll s b >> (putMVar received (adr, FromSendPacket encoded))
                          return ()
            GroupGetPubShared a' ->
              I.groupGetPubShared a' >>= \p -> forkIO (putMVar received ((adr,(FromGroupGetPubShared p)))) >> return ()
            MakeCertVerify a' ->
              makeCertVerify a' >>= \c -> forkIO (putMVar received ((adr,(FromMakeCertVerify c)))) >> return ()
            CloseWith a' -> do
              putStrLn $ "Close" ++ show a'
              case lookup adr sock of
                Just s -> close s >> core (delete (adr,s) sock) next Perform (unsafeCoerce ()) newAccepts received
            GetCurrentTime a' -> do
              putStrLn "GetCurrentTime"              
              getCurrentTimeFromBase >>= \time -> forkIO (putMVar received ((adr,FromGetCurrentTime time))) >> return ()
              

          case ea of
            CloseWith _ -> return ()
            _ -> core sock next Perform (unsafeCoerce ()) newAccepts received 

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

recvHandshakes :: Socket -> Maybe ((TLS.Hash,TLS.Cipher), B.ByteString) ->  IO (Either I.TLSError [I.Handshake13])
recvHandshakes sock m = do
  erecord <- recvRecord sock m
  case erecord of
    Left err -> return $ Left err
    Right (I.Record ProtocolType_Handshake ver fragment) ->
        return $ I.decodeHandshakes13 $ I.fragmentGetBytes fragment
    Right p -> print p >> return (Right [])

recvRecord :: Socket -> Maybe ((TLS.Hash,TLS.Cipher), B.ByteString) -> IO (Either I.TLSError (I.Record I.Plaintext))
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

maximumSizeExceeded :: I.TLSError
maximumSizeExceeded = Error_Protocol ("record exceeding maximum size", True, RecordOverflow)


genKeys :: IO (RSA.PublicKey, RSA.PrivateKey)
genKeys = RSA.generate 256 0x10001
