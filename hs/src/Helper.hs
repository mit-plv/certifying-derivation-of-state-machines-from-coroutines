{-# LANGUAGE BangPatterns, OverloadedStrings #-}

module Helper where

import Network.TLS
import Network.TLS.Internal
import qualified Data.ByteString as B
import qualified Data.ByteArray as B (convert)
import Data.List
import Data.Maybe
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.X509 as X
import qualified Crypto.PubKey.RSA as RSA
import qualified Crypto.PubKey.RSA.PSS as PSS
import qualified Crypto.Hash.Algorithms as A
import qualified Crypto.Hash as H
import Certificate
import Encrypt (newRecordOptions)

sniExt :: ExtensionRaw
sniExt = ExtensionRaw extensionID_ServerName ""

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

supportedGroups' = [P256,P384,P521,X25519]

serverGroups :: ([]) Group
serverGroups =
  supportedGroups'

defaultCertChain pubKey = X.CertificateChain [simpleX509 $ PubKeyRSA pubKey]

recordToPacket :: Record Plaintext -> Maybe Packet13
recordToPacket (Record ProtocolType_ChangeCipherSpec _ _) = Just ChangeCipherSpec13
recordToPacket (Record ProtocolType_AppData _ fragment) = Just $ AppData13 $ fragmentGetBytes fragment
recordToPacket (Record ProtocolType_Handshake _ fragment) =
  case decodeHandshakes13 $ fragmentGetBytes fragment of
    Right a -> Just $ Handshake13 a
    Left _ -> Nothing

test :: IORef Bool
test = unsafePerformIO $ newIORef False

decodeRecord :: Header -> Maybe (((Hash, Cipher), B.ByteString), Int) -> B.ByteString -> Maybe Packet13
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
  case runRecordM (decodeRecordM header msg) newRecordOptions rst of
    Left _ -> unsafePerformIO (writeIORef test True >> readIORef test >>= \t -> if t then return Nothing else return Nothing)
    Right (a,_) -> recordToPacket a
    
