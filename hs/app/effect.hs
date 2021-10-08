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
  newAccepts <- newIORef []
  --newAccepts <- newEmptyMVar
  received <- newEmptyMVar
  case ecred of
    Right (cert,priv) -> do
      sock <- socket AF_INET Stream 0
      bind sock (SockAddrInet 4433 iNADDR_ANY)  
      listen sock 2
      forkIO (core Map.empty (Left ((((((),1000000), 1000000), 1000000), cert), priv)) Receive (unsafeCoerce ()) newAccepts received)
      forever $ do
        (s,a) <- accept sock
        --ac <- tryTakeMVar newAccepts
        --case ac of
        --  Nothing ->
        --    putMVar newAccepts (Left (s, show a))
        --  Just ac' -> do
        --    putMVar newAccepts (Left (s, show a))
        --    putStrLn (show a)
        --    putMVar newAccepts ac'
        modifyIORef newAccepts $ \l -> (s,show a):l
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
--          l <- takeMVar newAccepts
--          case l of
--            Left (s,adr) -> do
----              putStrLn $ " accepted" ++ show adr
--              x <- randomRIO (0,9) :: IO Int
--              let adr' = show x ++ take 2 (reverse adr)
--              core (Map.insert adr' s sock) next Accept (unsafeCoerce (Just adr')) newAccepts received
--            Right r -> do
--              forkIO $ putMVar received r
--              core sock next Accept (unsafeCoerce Nothing) newAccepts received
          l <- readIORef newAccepts
          case l of
            [] -> threadDelay 10000 >> core sock next Accept (unsafeCoerce Nothing) newAccepts received 
            (s,adr):l' -> do
              writeIORef newAccepts l'
              --putStrLn $ " accepted" ++ show adr
              core (Map.insert adr s sock) next Accept (unsafeCoerce (Just adr)) newAccepts received 
        Receive -> do
          r <- tryTakeMVar received
          case r of
            Just (adr,p) ->
              core sock next Receive (unsafeCoerce r) newAccepts received
              --case Map.lookup adr sock of
              --  Just _ -> do
              --    --putStrLn $ " received " ++ show adr
              --    core sock next Receive (unsafeCoerce (Just r)) newAccepts received
              --  Nothing -> do
              --    --putStrLn $ " received but not found " ++ show adr
              --    core sock next Receive (unsafeCoerce Nothing) newAccepts received
            Nothing -> core sock next Receive (unsafeCoerce Nothing) newAccepts received 
        Perform -> do
          let (adr,ea) = unsafeCoerce a :: (String, Args_tls)
          --putStrLn $ " perform " ++ show adr
          case ea of
            RecvPacket _ -> do
              --putStrLn "Start"
              --forkIO (putMVar newAccepts (Right (adr, FromSetPSK)))
              forkIO $ putMVar received (adr, FromSetPSK)
              core sock next Perform (unsafeCoerce FromSetPSK) newAccepts received
            RecvData a' -> do
              --putStrLn "RecvData"
              let s = sock Map.! adr
              --case lookup adr sock of
                --Just s -> do
              forkIO $ do
                ch <- SB.recv s (16384 + 256)
                --putStrLn $ show $ toLazyByteString $ byteStringHex ch
                --putMVar newAccepts (Right (adr, FromRecvData ch))
                putMVar received (adr, FromRecvData ch)
              return ()
              --  Nothing -> error "no socket"
              core sock next Perform (unsafeCoerce FromSetPSK) newAccepts received
            GetRandomBytes a' -> do
              --putStrLn (if a' == 0 then "Skip" else "GetRandomBytes")
              v <- if a' == 0 then return "" else getRandomBytes a'
              core sock next Perform (unsafeCoerce (FromGetRandomBytes v)) newAccepts received 
              --forkIO (putMVar newAccepts (Right (adr, FromGetRandomBytes v)))
              --core sock next Perform (unsafeCoerce ()) newAccepts received 
            SendData a' -> do
              let s = sock Map.! adr
              --case lookup adr sock of
              --  Just s -> do
              let (pkt,m) = a' :: (I.Packet13, Maybe (((TLS.Hash,TLS.Cipher),B.ByteString),Int))
              --putStrLn $ "SendPacket " ++ show pkt
              let encoded =
                    case pkt of
                      I.Handshake13 [hs] -> I.encodeHandshake13 hs
                      I.ChangeCipherSpec13 -> I.encodeChangeCipherSpec
                      _ -> ""
              bs <- encodePacket13 (pkt,m)
              case bs of
                Right b -> do
                  SB.sendAll s b
                  core sock next Perform (unsafeCoerce $ FromSendPacket encoded) newAccepts received
            GroupGetPubShared a' -> do
              p <- I.groupGetPubShared a'
              --forkIO (putMVar newAccepts (Right (adr,(FromGroupGetPubShared p))))
              core sock next Perform (unsafeCoerce $ FromGroupGetPubShared p) newAccepts received 
            MakeCertVerify a' -> do
              c <- makeCertVerify a'
              --forkIO (putMVar newAccepts (Right (adr,(FromMakeCertVerify c))))
              core sock next Perform (unsafeCoerce $ FromMakeCertVerify c) newAccepts received 
            CloseWith a' -> do
              --putStrLn $ "Close" ++ show a'
              let s = sock Map.! adr
              --case lookup adr sock of
              --  Just s ->
              close s
              core (Map.delete adr sock) next Perform (unsafeCoerce FromSetPSK) newAccepts received 
            GetCurrentTime a' -> do
              time <- getCurrentTimeFromBase
              --putStrLn "GetCurrentTime"              
              --forkIO (putMVar newAccepts (Right (adr,FromGetCurrentTime time)))
              core sock next Perform (unsafeCoerce $ FromGetCurrentTime time) newAccepts received 
