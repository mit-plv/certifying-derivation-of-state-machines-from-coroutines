{-# LANGUAGE ScopedTypeVariables, OverloadedStrings #-}

import System.Environment
import Control.Monad
import Control.Concurrent
import Data.IORef
import Data.List
import System.Random
import qualified Data.Map as Map
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
  --newAccepts <- newIORef []
  newAccepts <- newEmptyMVar
  received <- newEmptyMVar
  case ecred of
    Right (cert,priv) -> do
      sock <- socket AF_INET Stream 0
      bind sock (SockAddrInet 4433 iNADDR_ANY)  
      listen sock 2
      forkIO (core Map.empty (Left ((((((),1000000), 1000000), 1000000), cert), priv)) Receive (unsafeCoerce ()) newAccepts received)
      forever $ do
        (s,a) <- accept sock
        ac <- tryTakeMVar newAccepts
        case ac of
          Nothing ->
            putMVar newAccepts (Left (s, show a))
          Just ac' -> do
            putMVar newAccepts (Left (s, show a))
            putStrLn (show a)
            putMVar newAccepts ac'
--        modifyIORef newAccepts $ \l -> (s,show a):l
    Left s ->
      putStrLn s

core sock x ef (r::Any) newAccepts received = do
  case main_loop_step x ef r of
    Right res -> do
      print res
      putStrLn "\nDone"
      forM_ sock (\s -> close s)
    Left (next, Nothing) -> core sock next Skip (unsafeCoerce ()) newAccepts received
    Left (next, Just (ExistT e a)) ->
      case e of
        Skip -> do
          core sock next Skip (unsafeCoerce ()) newAccepts received
        Accept -> do
          l <- takeMVar newAccepts
          case l of
            Left (s,adr) -> do
              putStrLn $ " accepted" ++ show adr
              x <- randomRIO (0,9) :: IO Int
              let adr' = show x ++ adr
              core (Map.insert adr' s sock) next Accept (unsafeCoerce (Just adr')) newAccepts received
            Right r -> do
              forkIO $ putMVar received r
              core sock next Accept (unsafeCoerce Nothing) newAccepts received
          --l <- readIORef newAccepts
          --case l of
          --  [] -> threadDelay 10000 >> core sock next Accept (unsafeCoerce Nothing) newAccepts received 
          --  (s,adr):l' -> do
          --    writeIORef newAccepts l'
          --    putStrLn $ " accepted" ++ show adr
          --    core ((adr,s):sock) next Accept (unsafeCoerce (Just adr)) newAccepts received 
        Receive -> do
          r <- takeMVar received
          case r of
            (adr,p) ->
              case Map.lookup adr sock of
                Just _ -> do
                  --putStrLn $ " received " ++ show adr
                  core sock next Receive (unsafeCoerce (Just r)) newAccepts received
                Nothing -> do
                  --putStrLn $ " received but not found " ++ show adr
                  core sock next Receive (unsafeCoerce Nothing) newAccepts received
            --Nothing -> core sock next Receive (unsafeCoerce Nothing) newAccepts received 
        Perform -> do
          let (adr,ea) = unsafeCoerce a :: (String, Args_tls)
          putStrLn $ " perform " ++ show adr
          case ea of
            RecvPacket _ -> do
              putStrLn "Start"
              forkIO (putMVar newAccepts (Right (adr, FromSetPSK)))
              core sock next Perform (unsafeCoerce FromSetPSK) newAccepts received
            RecvData a' -> do
              putStrLn "RecvData"
              let s = sock Map.! adr
              --case lookup adr sock of
                --Just s -> do
              forkIO $ do
                ch <- SB.recv s (16384 + 256)
                putStrLn $ show $ toLazyByteString $ byteStringHex ch
                putMVar newAccepts (Right (adr, FromRecvData ch))
              return ()
              --  Nothing -> error "no socket"
              core sock next Perform (unsafeCoerce FromSetPSK) newAccepts received
            GetRandomBytes a' -> do
              putStrLn (if a' == 0 then "Skip" else "GetRandomBytes")
              v <- if a' == 0 then return "" else getRandomBytes a'
              core sock next Perform (unsafeCoerce (FromGetRandomBytes v)) newAccepts received 
              --forkIO (putMVar newAccepts (Right (adr, FromGetRandomBytes v)))
              --core sock next Perform (unsafeCoerce ()) newAccepts received 
            SendData a' -> do
              let s = sock Map.! adr
              --case lookup adr sock of
              --  Just s -> do
              let (pkt,m) = a' :: (I.Packet13, Maybe (((TLS.Hash,TLS.Cipher),B.ByteString),Int))
              putStrLn $ "SendPacket " ++ show pkt
              let (sending,encoded) =
                    case pkt of
                      I.Handshake13 [hs] ->
                        case hs of
                          I.Finished13 _ -> (True, I.encodeHandshake13 hs)
                          _ -> (False, I.encodeHandshake13 hs)
                      I.ChangeCipherSpec13 -> (False, I.encodeChangeCipherSpec)
              bs <- encodePacket13 (pkt,m)
              case bs of
                Right b -> do
                  SB.sendAll s b
                  core sock next Perform (unsafeCoerce $ FromSendPacket encoded) newAccepts received
--                      case Map.lookup adr toSends of
--                        Just msg ->
--                          if sending then do
--                            let toSends' = Map.update (\_ -> Nothing) adr toSends
--                            --forkIO $ SB.sendAll s (B.append msg b) >> (putMVar newAccepts (Right (adr, FromSendPacket encoded)))
--                            SB.sendAll s (B.append msg b)
--                            core sock next Perform (unsafeCoerce $ FromSendPacket encoded) newAccepts received toSends'
--                          else do
--                            let toSends' = Map.update(\msg -> Just (B.append msg b)) adr toSends
--                            --forkIO $ putMVar newAccepts (Right (adr, FromSendPacket encoded))
--                            core sock next Perform (unsafeCoerce $ FromSendPacket encoded) newAccepts received toSends'
--                        Nothing -> do
--                          --forkIO $ SB.sendAll s b >> (putMVar newAccepts (Right (adr, FromSendPacket encoded)))
--                          SB.sendAll s b
--                          core sock next Perform (unsafeCoerce $ FromSendPacket encoded) newAccepts received toSends
            GroupGetPubShared a' -> do
              p <- I.groupGetPubShared a'
              --forkIO (putMVar newAccepts (Right (adr,(FromGroupGetPubShared p))))
              core sock next Perform (unsafeCoerce $ FromGroupGetPubShared p) newAccepts received 
            MakeCertVerify a' -> do
              c <- makeCertVerify a'
              --forkIO (putMVar newAccepts (Right (adr,(FromMakeCertVerify c))))
              core sock next Perform (unsafeCoerce $ FromMakeCertVerify c) newAccepts received 
            CloseWith a' -> do
              putStrLn $ "Close" ++ show a'
              let s = sock Map.! adr
              --case lookup adr sock of
              --  Just s ->
              close s >> core (Map.delete adr sock) next Perform (unsafeCoerce FromSetPSK) newAccepts received 
            GetCurrentTime a' -> do
              time <- getCurrentTimeFromBase
              putStrLn "GetCurrentTime"              
              --forkIO (putMVar newAccepts (Right (adr,FromGetCurrentTime time)))
              core sock next Perform (unsafeCoerce $ FromGetCurrentTime time) newAccepts received 

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
