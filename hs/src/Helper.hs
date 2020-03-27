{-# LANGUAGE BangPatterns, OverloadedStrings #-}

module Helper where

import Network.TLS
import Network.TLS.Internal
import qualified Data.ByteString as B
import qualified Data.ByteArray as B (convert)
import Data.List
import Data.Maybe
import qualified Data.X509 as X
import qualified Crypto.PubKey.RSA as RSA
import qualified Crypto.PubKey.RSA.PSS as PSS
import qualified Crypto.Hash.Algorithms as A
import qualified Crypto.Hash as H
import Certificate

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
{-
extensionID_NegotiatedGroups :: ExtensionID
extensionID_NegotiatedGroups                    = 0xa -- RFC4492bis and TLS 1.3
extensionID_KeyShare :: ExtensionID
extensionID_KeyShare                            = 0x33 -- TLS 1.3


decodeNegotiatedGroups :: B.ByteString -> Maybe [Group]
decodeNegotiatedGroups =
    runGetMaybe (mapMaybe toEnumSafe16 <$> getWords16)

data KeyShare =
   Build_KeyShare Group B.ByteString
   deriving (Show)

kSgroup :: KeyShare -> Group
kSgroup k =
  case k of {
   Build_KeyShare kSgroup0 _ -> kSgroup0}

decodeKeyShare = runGetMaybe $ do
    len <- fromIntegral <$> getWord16
    grps <- getList len getKeyShare
    return (catMaybes grps)

getKeyShare :: Get (Int, Maybe KeyShare)
getKeyShare = do
    g <- getWord16
    l <- fromIntegral <$> getWord16
    key <- getBytes l
    let !len = l + 4
    case toEnumSafe16 g of
      Nothing  -> return (len, Nothing)
      Just grp -> return (len, Just (Build_KeyShare grp key))
-}
supportedGroups' = [P256,P384,P521,X25519]

serverGroups :: ([]) Group
serverGroups =
  supportedGroups'

defaultCertChain pubKey = X.CertificateChain [simpleX509 $ PubKeyRSA pubKey]
