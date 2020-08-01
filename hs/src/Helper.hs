{-# LANGUAGE BangPatterns, OverloadedStrings, FlexibleContexts #-}

module Helper where

import Network.TLS
import Network.TLS.Internal
import qualified Data.ByteString as B
import qualified Data.ByteArray as B (convert)
import Data.List
import Data.Maybe
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad.State.Strict
import qualified Data.X509 as X
import qualified Crypto.PubKey.RSA as RSA
import qualified Crypto.PubKey.RSA.PSS as PSS
import qualified Crypto.Hash.Algorithms as A
import qualified Crypto.Hash as H
import Certificate
import Encrypt (newRecordOptions)
import Debug.Trace
import Data.ByteString.Builder (toLazyByteString, byteStringHex)

sniExt :: ExtensionRaw
sniExt = ExtensionRaw extensionID_ServerName ""

packet2tinfo :: Packet13 -> Maybe TLS13TicketInfo
packet2tinfo (Handshake13 [NewSessionTicket13 life ageadd nonce sessid exts]) =
  Just $ TLS13TicketInfo { lifetime = life, ageAdd = ageadd, txrxTime = (fromIntegral 1000), estimatedRTT = Nothing }

makeCertVerify :: (((PubKey,PrivKey), (HashAndSignatureAlgorithm)), B.ByteString) -> IO Handshake13
makeCertVerify (((pub, priv), (h,sig)), msg) = do
  let params = signatureParams pub (Just (h,sig))
  r <- kxSign priv pub params (makeTarget msg)
  case r of
    Left err -> error ("sign faild: " ++ show err)
    Right signed -> return $ CertVerify13 (h,sig) signed

--makeCertVerify :: RSA.PrivateKey -> B.ByteString -> Handshake13
--makeCertVerify priv bs = 
--  let params = PSS.defaultPSSParams A.SHA384
--  in
--  case PSS.signWithSalt (B.replicate (PSS.pssSaltLength params) 0)  Nothing params priv (makeTarget bs) of
--    Right signed ->
--      CertVerify13 (HashIntrinsic, SignatureRSApssRSAeSHA384) signed

makeTarget :: B.ByteString -> B.ByteString
makeTarget hashValue = runPut $ do
    putBytes $ B.replicate 64 32
    putBytes ("TLS 1.3, server CertificateVerify" :: B.ByteString)
    putWord8 0
    putBytes hashValue

hashWith :: Hash -> [B.ByteString] -> B.ByteString
hashWith SHA1 bss = B.convert $ H.hashFinalize $ H.hashUpdates (H.hashInit :: H.Context H.SHA1) bss
hashWith MD5 bss = B.convert $ H.hashFinalize $ H.hashUpdates (H.hashInit :: H.Context H.MD5) bss
hashWith SHA224 bss = B.convert $ H.hashFinalize $ H.hashUpdates (H.hashInit :: H.Context H.SHA224) bss
hashWith SHA256 bss = B.convert $ H.hashFinalize $ H.hashUpdates (H.hashInit :: H.Context H.SHA256) bss
hashWith SHA384 bss = B.convert $ H.hashFinalize $ H.hashUpdates (H.hashInit :: H.Context H.SHA384) bss
hashWith SHA512 bss = B.convert $ H.hashFinalize $ H.hashUpdates (H.hashInit :: H.Context H.SHA512) bss

extensionLookup :: ExtensionID -> [ExtensionRaw] -> Maybe B.ByteString
extensionLookup toFind = fmap (\(ExtensionRaw _ content) -> content)
                       . find (\(ExtensionRaw eid _) -> eid == toFind)

supportedGroups' = [X25519,X448,P256,FFDHE3072,FFDHE4096,P384,FFDHE6144,FFDHE8192,P521,FFDHE2048]

serverGroups :: ([]) Group
serverGroups =
  supportedGroups'

defaultCertChain pubKey = X.CertificateChain [simpleX509 $ PubKeyRSA pubKey]

parseHandshakeRecord :: Maybe (GetContinuation (HandshakeType13, B.ByteString)) -> B.ByteString -> GetResult (HandshakeType13, B.ByteString)
parseHandshakeRecord mcont bs = fromMaybe decodeHandshakeRecord13 mcont bs

parseHandshake :: (HandshakeType13, B.ByteString) -> Either (AlertLevel, AlertDescription) Handshake13
parseHandshake (ty, bs) = either (Left . errorToAlert) Right $ decodeHandshake13 ty bs

errorToAlert :: TLSError -> (AlertLevel, AlertDescription)
errorToAlert (Error_Protocol (_, _, ad))   = (AlertLevel_Fatal, ad)
errorToAlert (Error_Packet_unexpected _ _) = (AlertLevel_Fatal, UnexpectedMessage)
errorToAlert (Error_Packet_Parsing _)      = (AlertLevel_Fatal, DecodeError)
errorToAlert _                             = (AlertLevel_Fatal, InternalError)

--decodeRecord :: Header -> Maybe (((Hash, Cipher), B.ByteString), Int) -> B.ByteString -> Either (AlertLevel, AlertDescription) Packet13
--decodeRecord mcont header m msg =
--  let rst =
--        case m of
--          Nothing -> newRecordState
--          Just (((h,cipher),secret), sn)->
--            let bulk    = cipherBulk cipher
--                keySize = bulkKeySize bulk
--                ivSize  = max 8 (bulkIVSize bulk + bulkExplicitIV bulk)
--                key = hkdfExpandLabel h secret "key" "" keySize
--                iv  = hkdfExpandLabel h secret "iv"  "" ivSize
--                cst = CryptState {
--                    cstKey       = bulkInit bulk BulkDecrypt key
--                  , cstIV        = iv
--                  , cstMacSecret = secret
--                  }
--            in
--            RecordState {
--                  stCryptState  = cst
--                , stMacState    = MacState { msSequence = fromIntegral sn }
--                , stCipher      = Just cipher
--                , stCompression = nullCompression
--                }
--  in
--  if B.length msg > 16384 then
--    Left (AlertLevel_Fatal, RecordOverflow)
--  else
--    case runRecordM (decodeRecordM' header msg) newRecordOptions rst of
--      Left err -> Left $ errorToAlert err
--      Right (a,_) ->
--        case recordToPacket a of
--          Right p -> Right p
--          Left err -> Left $ errorToAlert err

decodeRecord :: Header -> Maybe (((Hash, Cipher), B.ByteString), Int) -> B.ByteString -> Either AlertDescription (ProtocolType, B.ByteString)
decodeRecord header m msg =
  let rst =
        case m of
          Nothing -> newRecordState
          Just (((h,cipher),secret), sn)->
            let bulk    = cipherBulk cipher
                keySize = bulkKeySize bulk
                ivSize  = max 8 (bulkIVSize bulk + bulkExplicitIV bulk)
                key = hkdfExpandLabel h secret "key" "" keySize
                iv  = hkdfExpandLabel h secret "iv"  "" ivSize
                cst = CryptState {
                    cstKey       = bulkInit bulk BulkDecrypt key
                  , cstIV        = iv
                  , cstMacSecret = secret
                  }
            in
            RecordState {
                  stCryptState  = cst
                , stMacState    = MacState { msSequence = fromIntegral sn }
                , stCipher      = Just cipher
                , stCompression = nullCompression
                }
  in
  case runRecordM (decodeRecordM' header msg) newRecordOptions rst of
    Left err -> Left $ snd $ errorToAlert err
    Right (Record ty _ fragment,_) ->
      let bs = fragmentGetBytes fragment in
      if B.length bs > 16384 then
        Left RecordOverflow
      else
        Right (ty, fragmentGetBytes fragment)

decodeRecordM' :: Header -> B.ByteString -> RecordM (Record Plaintext)
decodeRecordM' header content = disengageRecord' erecord
   where
     erecord = rawToRecord header (fragmentCiphertext content)
    
disengageRecord' :: Record Ciphertext -> RecordM (Record Plaintext)
disengageRecord' = decryptRecord >=> uncompressRecord

decryptRecord :: Record Ciphertext -> RecordM (Record Compressed)
decryptRecord record@(Record ct ver fragment) = do
    st <- get
    case stCipher st of
        Nothing -> noDecryption
        _       -> do
            recOpts <- getRecordOptions
            let mver = recordVersion recOpts
            if recordTLS13 recOpts
                then decryptData13 mver (fragmentGetBytes fragment) st
                else onRecordFragment record $ fragmentUncipher $ \e ->
                        decryptData mver record e st
  where
    noDecryption = onRecordFragment record $ fragmentUncipher return
    decryptData13 mver e st
        | ct == ProtocolType_AppData = do
            inner <- decryptData mver record e st
            case unInnerPlaintext inner of
                Left message   -> throwError $ Error_Protocol (message, True, UnexpectedMessage)
                Right (ct', d) -> return $ Record ct' ver (fragmentCompressed d)
        | otherwise = throwError $ Error_Protocol ("not encrypted", True, UnexpectedMessage)
