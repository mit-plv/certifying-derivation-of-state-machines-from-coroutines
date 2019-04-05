module Client where

import Network
import System.IO 

sendMessage msg = withSocketsDo $ do 
        hSetBuffering stdout NoBuffering 
        h <- connectTo "127.0.0.1" (PortNumber 8001)
        hSetBuffering h LineBuffering
        hPutStrLn h msg
        hClose h
