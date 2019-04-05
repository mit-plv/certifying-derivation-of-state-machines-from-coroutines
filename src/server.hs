import Network
import System.IO 
import Control.Exception
import Handshake
import Crypto.Saltine.Core.Box
import Crypto.Saltine.Class
import qualified Data.ByteString as BS

main :: IO ()
main = withSocketsDo $ do 
    hSetBuffering stdout NoBuffering
    server
    putStrLn "Connection closed."

coerce :: BS.ByteString -> [Integer]
coerce = map toInteger . BS.unpack

server :: IO ()
server = do
    sock <- listenOn (PortNumber 8001)
    (pk,sk) <- newKeypair
    core sock $ Left (((),coerce (encode pk)), coerce (encode sk))
    sClose sock

receive :: Socket -> IO Int
receive sock = do
    (h,host,port) <- accept sock
    hSetBuffering h LineBuffering
    msg <- hGetLine h           
    putStrLn $ "received: " ++ msg
    return $ read msg

core sock x = 
  case handshake_step x of
    Nothing -> putStrLn "End"
    Just (ExistT _ (e,next)) ->
      case e of
        GetE () -> receive sock >>= \n -> core sock (next $ unsafeCoerce n)
        PutE n -> putStrLn (show n) >> core sock (next $ unsafeCoerce ())
        ReadE () -> receive sock >>= \l -> core sock (next $ unsafeCoerce l)
        PrintE l -> putStrLn (show l) >> core sock (next $ unsafeCoerce ())
        GenKeyE _ -> newKeypair >>= \(sk,pk) -> core sock (next $ unsafeCoerce (coerce (encode sk) :: [Integer], coerce (encode pk) :: [Integer]))
