import Network.Socket
import Network.TLS.Internal
import Network.TLS
import qualified Data.ByteString as B
import Test.Tasty
import Test.Tasty.QuickCheck
import Connection
import TLS

main :: IO ()
main = withSocketsDo $ do
  sock <- socket AF_INET Stream 0
  bind sock (SockAddrInet 8001 iNADDR_ANY)  
  listen sock 2
  (s,_) <- accept sock
  (_,param) <- generate arbitraryPairParams13
  ctx <- contextNewOnSocket s param
  core (Left ((),ctx)) RecvClientHello (unsafeCoerce 0)

recvClientHello ctx = do
  hss <- recvPacketHandshake ctx
  case hss of
    [ClientHello _ _ _ _ _ exts _] -> return exts

recvPacketHandshake :: TLS.Context -> IO [Handshake]
recvPacketHandshake ctx = do
    pkts <- recvPacket ctx
    case pkts of
        Right (Handshake l) -> return l

core x ef r = do
  case pickKeyShare_step x ef (unsafeCoerce r) of
    Right res -> print res >> putStrLn ""
    Left (next, Nothing) -> core next RecvClientHello (unsafeCoerce 0)
    Left (next, Just (ExistT e a)) ->
      case e of
        RecvClientHello -> recvClientHello (unsafeCoerce a) >>= core next RecvClientHello

