{-# LANGUAGE OverloadedStrings #-}
module Encrypt where

import Network.TLS
import Network.TLS.Internal
import qualified Data.ByteString as B
import Data.Word
import Data.IORef

encodePacket13 :: (Packet13, Maybe ((Hash,Cipher),B.ByteString)) -> IORef Word64 -> IO (Either TLSError B.ByteString)
encodePacket13 (pkt,encrypt) ms = do
    let pt = contentType pkt
        mkRecord bs = Record pt TLS12 (fragmentPlaintext bs)
        records = map mkRecord $ packetToFragments 16384 pkt
    fmap B.concat <$> forEitherM records (encodeRecord encrypt ms)

prepareRecord :: Maybe ((Hash,Cipher),B.ByteString) -> IORef Word64 -> RecordM a -> IO (Either TLSError a)
prepareRecord encrypt ms rm = do
  rst <-
        case encrypt of
          Nothing -> return newRecordState
          Just ((h,cipher),secret) -> do
            m <- readIORef ms
            let bulk    = cipherBulk cipher
                keySize = bulkKeySize bulk
                ivSize  = max 8 (bulkIVSize bulk + bulkExplicitIV bulk)
                key = hkdfExpandLabel h secret "key" "" keySize
                iv  = hkdfExpandLabel h secret "iv"  "" ivSize
                cst = CryptState {
                    cstKey       = bulkInit bulk BulkEncrypt key
                  , cstIV        = iv
                  , cstMacSecret = secret
                  }
                rst = RecordState {
                    stCryptState  = cst
                  , stMacState    = MacState { msSequence = m }
                  , stCipher      = Just cipher
                  , stCompression = nullCompression
                  }
            print rst
            putStrLn ""
            modifyIORef ms (fromInteger 1+)
            return rst
  case runRecordM rm newRecordOptions rst of
    Left err -> return $ Left err
    Right (a,_) -> return $ Right a

encodeRecord :: Maybe ((Hash,Cipher),B.ByteString) -> IORef Word64 -> Record Plaintext -> IO (Either TLSError B.ByteString)
encodeRecord cipher ms = prepareRecord cipher ms . encodeRecordM

packetToFragments :: Int -> Packet13 -> [B.ByteString]
packetToFragments len (Handshake13 hss)  =
    getChunks len $ B.concat $ map encodeHandshake13 hss
packetToFragments _   (Alert13 a)        = [encodeAlerts a]
packetToFragments _   (AppData13 x)      = [x]
packetToFragments _   ChangeCipherSpec13 = [encodeChangeCipherSpec]

newRecordOptions = RecordOptions { recordVersion = TLS13, recordTLS13 = True }
