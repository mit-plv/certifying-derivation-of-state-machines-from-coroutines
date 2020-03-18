
import qualified Data.ByteString as B
import qualified Network.Socket
import Network.TLS
import Network.TLS.Inernal

recvBytes :: Socket -> Int -> IO ByteString
recvBytes sock n = B.concat <$> loop n
  where loop 0 = return []
    loop left = do
      r <- recv sock left
      if B.null r
        then return []
        else (r:) <$> loop (left - B.length r)

recvPacket :: Socket -> IO (Either TLSError [Handshake13])
recvPacket sock =
  erecord <- recvRecord sock
  case erecord of
    Left err -> return $ Left err
    Right (Record ProtocolType_Handshake ver fragment) ->
        decodeHandshakes13 fragment

recvRecord :: Socket -> IO (Either TLSError (Record Plaintext))
recvRecord sock = recvBytes sock 5 >>= either (return . Left) (recvLengthE . decodeHeader)
  where recvLengthE = either (return . Left) recvLength
        recvLength header@(Header _ _ readlen) =
          | readlen > 16384 + 256 = return $ Left maximumSizeExceeded
					| otherwise =
                bs <- recvBytes sock (fromIntegral readlen)
                case decodeRecordM header bs of
                        Left err -> return $ Left err
                        Right (a,_) -> return $ Right a

maximumSizeExceeded :: TLSError
maximumSizeExceeded = Error_Protocol ("record exceeding maximum size", True, RecordOverflow)
