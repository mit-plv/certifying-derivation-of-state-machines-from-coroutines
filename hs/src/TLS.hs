{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module TLS where

import qualified Network.TLS as T
import qualified Network.TLS.Internal as I
import qualified Data.ByteString as B
import qualified Data.ByteArray as BA
import qualified Helper
import qualified Data.X509 as X
import qualified Crypto.PubKey.RSA as RSA
import qualified Data.Char
import qualified Data.Word8
import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

prod_curry :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
prod_curry f p =
  case p of {
   (,) x y -> f x y}

data SigT a p =
   ExistT a p

hd_error :: (([]) a1) -> GHC.Base.Maybe a1
hd_error l =
  case l of {
   [] -> GHC.Base.Nothing;
   (:) x _ -> GHC.Base.Just x}

filter :: (a1 -> GHC.Base.Bool) -> (([]) a1) -> ([]) a1
filter f l =
  case l of {
   [] -> [];
   (:) x l0 ->
    case f x of {
     GHC.Base.True -> (:) x (filter f l0);
     GHC.Base.False -> filter f l0}}

find :: (a1 -> GHC.Base.Bool) -> (([]) a1) -> GHC.Base.Maybe a1
find f l =
  case l of {
   [] -> GHC.Base.Nothing;
   (:) x tl ->
    case f x of {
     GHC.Base.True -> GHC.Base.Just x;
     GHC.Base.False -> find f tl}}

sum_merge :: (a1 -> a3) -> (a2 -> a3) -> (Prelude.Either a1 a2) -> a3
sum_merge f g x =
  case x of {
   Prelude.Left a -> f a;
   Prelude.Right b -> g b}

type ByteString = B.ByteString

group_beq :: T.Group -> T.Group -> GHC.Base.Bool
group_beq = (GHC.Base.==)

ksGroup :: I.KeyShareEntry -> T.Group
ksGroup k =
  case k of {
   I.KeyShareEntry ksGroup0 _ -> ksGroup0}

ksData :: I.KeyShareEntry -> ByteString
ksData k =
  case k of {
   I.KeyShareEntry _ ksData0 -> ksData0}

type ExtensionRaw = I.ExtensionRaw

type Session = I.Session

type CipherID = T.CipherID

type Version = T.Version

data ClientHelloMsg =
   Build_ClientHelloMsg Session (([]) ExtensionRaw) (([]) CipherID)

chSession :: ClientHelloMsg -> Session
chSession c =
  case c of {
   Build_ClientHelloMsg chSession0 _ _ -> chSession0}

chExtension :: ClientHelloMsg -> ([]) ExtensionRaw
chExtension c =
  case c of {
   Build_ClientHelloMsg _ chExtension0 _ -> chExtension0}

chCiphers :: ClientHelloMsg -> ([]) CipherID
chCiphers c =
  case c of {
   Build_ClientHelloMsg _ _ chCiphers0 -> chCiphers0}

serverGroups :: ([]) T.Group
serverGroups = Helper.serverGroups

findKeyShare :: (([]) I.KeyShareEntry) -> (([]) T.Group) -> GHC.Base.Maybe
                I.KeyShareEntry
findKeyShare ks gs =
  case gs of {
   [] -> GHC.Base.Nothing;
   (:) g gs' ->
    case find (\k -> group_beq (ksGroup k) g) ks of {
     GHC.Base.Just k -> GHC.Base.Just k;
     GHC.Base.Nothing -> findKeyShare ks gs'}}

extension_KeyShare :: (([]) ExtensionRaw) -> GHC.Base.Maybe (([]) I.KeyShareEntry)
extension_KeyShare = (\exts -> case Helper.extensionLookup I.extensionID_KeyShare exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.KeyShareClientHello kses) -> GHC.Base.return kses})

type Handshake13 = I.Handshake13

type Packet13 = I.Packet13

type PublicKey = X.PubKey

type PrivateKey = X.PrivKey

type GroupPublic = I.GroupPublic

type GroupKey = I.GroupKey

type Hash = T.Hash

type Cipher = T.Cipher

type HashAndSignatureAlgorithm = I.HashAndSignatureAlgorithm

data Eff_tls =
   RecvClientHello
 | RecvFinished
 | RecvCCS
 | RecvAppData
 | GetRandomBytes
 | SendPacket
 | GroupGetPubShared
 | MakeCertVerify

type Args_tls = Any

type Rets_tls = Any

lift_tls :: Eff_tls -> (Rets_tls -> Prelude.Either a1 (GHC.Base.Maybe a2)) ->
            Eff_tls -> Rets_tls -> Prelude.Either a1 (GHC.Base.Maybe a2)
lift_tls e a e0 =
  case e of {
   RecvClientHello ->
    case e0 of {
     RecvClientHello -> a;
     _ -> (\_ -> Prelude.Right GHC.Base.Nothing)};
   RecvFinished ->
    case e0 of {
     RecvFinished -> a;
     _ -> (\_ -> Prelude.Right GHC.Base.Nothing)};
   RecvCCS ->
    case e0 of {
     RecvCCS -> a;
     _ -> (\_ -> Prelude.Right GHC.Base.Nothing)};
   RecvAppData ->
    case e0 of {
     RecvAppData -> a;
     _ -> (\_ -> Prelude.Right GHC.Base.Nothing)};
   GetRandomBytes ->
    case e0 of {
     GetRandomBytes -> a;
     _ -> (\_ -> Prelude.Right GHC.Base.Nothing)};
   SendPacket ->
    case e0 of {
     SendPacket -> a;
     _ -> (\_ -> Prelude.Right GHC.Base.Nothing)};
   GroupGetPubShared ->
    case e0 of {
     GroupGetPubShared -> a;
     _ -> (\_ -> Prelude.Right GHC.Base.Nothing)};
   MakeCertVerify ->
    case e0 of {
     MakeCertVerify -> a;
     _ -> (\_ -> Prelude.Right GHC.Base.Nothing)}}

cipherID_beq :: CipherID -> CipherID -> GHC.Base.Bool
cipherID_beq = (GHC.Base.==)

cipherID :: Cipher -> CipherID
cipherID = T.cipherID

cipherHash :: Cipher -> Hash
cipherHash = T.cipherHash

byteString_beq :: ByteString -> ByteString -> GHC.Base.Bool
byteString_beq = (GHC.Base.==)

extensionEncode_KeyShare :: I.KeyShareEntry -> ByteString
extensionEncode_KeyShare = (\ks -> I.extensionEncode (I.KeyShareServerHello ks))

extensionEncode_SupportedVersions :: Version -> ByteString
extensionEncode_SupportedVersions = (\v -> I.extensionEncode (I.SupportedVersionsServerHello v))

tLS13 :: Version
tLS13 = T.TLS13

extensionRaw_KeyShare :: ByteString -> ExtensionRaw
extensionRaw_KeyShare = I.ExtensionRaw I.extensionID_KeyShare

extensionRaw_SupportedVersions :: ByteString -> ExtensionRaw
extensionRaw_SupportedVersions = I.ExtensionRaw I.extensionID_SupportedVersions

handshake13 :: (([]) Handshake13) -> Packet13
handshake13 = I.Handshake13

serverHello13 :: ByteString -> Session -> CipherID -> (([]) ExtensionRaw) ->
                 Handshake13
serverHello13 = (\b -> I.ServerHello13 (I.ServerRandom {I.unServerRandom = b}))

changeCipherSpec :: Packet13
changeCipherSpec = I.ChangeCipherSpec13

extension_SignatureAlgorithms :: (([]) ExtensionRaw) -> ([])
                                 HashAndSignatureAlgorithm
extension_SignatureAlgorithms = (\exts -> case Helper.extensionLookup I.extensionID_SignatureAlgorithms exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.SignatureAlgorithms sas) -> sas })

type Certificate = X.Certificate

type CertificateChain = X.CertificateChain

getCertificates :: CertificateChain -> ([]) Certificate
getCertificates = \cch -> case cch of { X.CertificateChain certs -> Prelude.map X.getCertificate certs }

certificate13 :: ByteString -> CertificateChain -> (([]) (([]) ExtensionRaw)) ->
                 Handshake13
certificate13 = I.Certificate13

empty :: ByteString
empty = B.empty

ciphersuite_default :: ([]) Cipher
ciphersuite_default = I.ciphersuite_default

hashWith :: Hash -> (([]) ByteString) -> ByteString
hashWith = Helper.hashWith

encryptedExtensions13 :: (([]) ExtensionRaw) -> Handshake13
encryptedExtensions13 = I.EncryptedExtensions13

appData13 :: ByteString -> Packet13
appData13 = I.AppData13

type CryptoError = I.CryptoError

encodeGroupPublic :: GroupPublic -> ByteString
encodeGroupPublic = I.encodeGroupPublic

decodeGroupPublic :: T.Group -> ByteString -> Prelude.Either CryptoError GroupPublic
decodeGroupPublic = I.decodeGroupPublic

ba_convert :: GroupKey -> ByteString
ba_convert = BA.convert

hashDigestSize :: Hash -> GHC.Base.Int
hashDigestSize = I.hashDigestSize

type Word8 = Data.Word8.Word8

b_replicate :: GHC.Base.Int -> Word8 -> ByteString
b_replicate = B.replicate

w0 :: Word8
w0 = Data.Word8._nul

hkdfExtract :: Hash -> ByteString -> ByteString -> ByteString
hkdfExtract = I.hkdfExtract

hkdfExpandLabel :: Hash -> ByteString -> ByteString -> ByteString -> GHC.Base.Int ->
                   ByteString
hkdfExpandLabel = I.hkdfExpandLabel

s2b :: Prelude.String -> ByteString
s2b = (\s -> B.pack (Prelude.map (\c -> Prelude.fromIntegral (Data.Char.ord c)) s))

finished13 :: ByteString -> Handshake13
finished13 = I.Finished13

hmac :: Hash -> ByteString -> ByteString -> ByteString
hmac = I.hmac

inb :: (a1 -> a1 -> GHC.Base.Bool) -> a1 -> (([]) a1) -> GHC.Base.Bool
inb eqbA x l =
  case l of {
   [] -> GHC.Base.False;
   (:) y _ -> eqbA x y}

chooseCipher :: (([]) CipherID) -> (([]) Cipher) -> GHC.Base.Maybe Cipher
chooseCipher clientCipherIDs serverCiphers =
  hd_error
    (filter (\cipher -> inb cipherID_beq (cipherID cipher) clientCipherIDs)
      serverCiphers)

makeVerifyData :: Hash -> ByteString -> ByteString -> ByteString
makeVerifyData h key transcript =
  hmac h
    (hkdfExpandLabel h key
      (s2b ((:) 'f' ((:) 'i' ((:) 'n' ((:) 'i' ((:) 's' ((:) 'h' ((:) 'e' ((:) 'd'
        ([])))))))))) (s2b ([])) (hashDigestSize h)) transcript

isDigitalSignaturePair :: ((,) PublicKey PrivateKey) -> GHC.Base.Bool
isDigitalSignaturePair = I.isDigitalSignaturePair

signatureCompatible13 :: PublicKey -> HashAndSignatureAlgorithm -> GHC.Base.Bool
signatureCompatible13 = I.signatureCompatible13

certPubKey :: Certificate -> PublicKey
certPubKey = X.certPubKey

decideCredInfo' :: PrivateKey -> HashAndSignatureAlgorithm -> (([]) Certificate) ->
                   GHC.Base.Maybe ((,) PublicKey HashAndSignatureAlgorithm)
decideCredInfo' priv hashSig certs =
  case certs of {
   [] -> GHC.Base.Nothing;
   (:) cert rest ->
    let {pub = certPubKey cert} in
    case isDigitalSignaturePair ((,) pub priv) of {
     GHC.Base.True ->
      case signatureCompatible13 pub hashSig of {
       GHC.Base.True -> GHC.Base.Just ((,) pub hashSig);
       GHC.Base.False -> decideCredInfo' priv hashSig rest};
     GHC.Base.False -> decideCredInfo' priv hashSig rest}}

decideCredInfo :: PrivateKey -> (([]) Certificate) -> (([])
                  HashAndSignatureAlgorithm) -> GHC.Base.Maybe
                  ((,) PublicKey HashAndSignatureAlgorithm)
decideCredInfo priv certs hashSigs =
  case hashSigs of {
   [] -> GHC.Base.Nothing;
   (:) hashSig rest ->
    case decideCredInfo' priv hashSig certs of {
     GHC.Base.Just res -> GHC.Base.Just res;
     GHC.Base.Nothing -> decideCredInfo priv certs rest}}

doHandshake_step :: (Prelude.Either ((,) ((,) () CertificateChain) PrivateKey)
                    (Prelude.Either ((,) ((,) () CertificateChain) PrivateKey)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () CertificateChain) PrivateKey)
                    ((,) ClientHelloMsg ByteString)) Cipher) I.KeyShareEntry)
                    GroupPublic)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () CertificateChain) PrivateKey)
                    ((,) ClientHelloMsg ByteString)) Cipher) I.KeyShareEntry)
                    ((,) GroupPublic GroupKey))
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () CertificateChain) PrivateKey)
                    ((,) ClientHelloMsg ByteString)) Cipher) I.KeyShareEntry)
                    ((,) GroupPublic GroupKey)) ByteString)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () CertificateChain) PrivateKey)
                    ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () CertificateChain) PrivateKey)
                    ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () CertificateChain) PrivateKey)
                    ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString) ByteString)
                    ((,) PublicKey HashAndSignatureAlgorithm))
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () PrivateKey) ((,) ClientHelloMsg ByteString))
                    Cipher) ((,) GroupPublic GroupKey)) ByteString) ByteString)
                    ((,) PublicKey HashAndSignatureAlgorithm)) ByteString)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString) ByteString) ByteString)
                    Handshake13)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString) ByteString) ByteString)
                    ByteString)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString) ByteString) ByteString)
                    ByteString) ByteString)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString) ByteString) ByteString)
                    ByteString) ByteString)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString) ByteString) ByteString)
                    ByteString) ByteString) (GHC.Base.Maybe ()))))))))))))))) ->
                    Eff_tls -> Rets_tls -> Prelude.Either
                    ((,)
                    (Prelude.Either ((,) ((,) () CertificateChain) PrivateKey)
                    (Prelude.Either ((,) ((,) () CertificateChain) PrivateKey)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () CertificateChain) PrivateKey)
                    ((,) ClientHelloMsg ByteString)) Cipher) I.KeyShareEntry)
                    GroupPublic)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () CertificateChain) PrivateKey)
                    ((,) ClientHelloMsg ByteString)) Cipher) I.KeyShareEntry)
                    ((,) GroupPublic GroupKey))
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () CertificateChain) PrivateKey)
                    ((,) ClientHelloMsg ByteString)) Cipher) I.KeyShareEntry)
                    ((,) GroupPublic GroupKey)) ByteString)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () CertificateChain) PrivateKey)
                    ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () CertificateChain) PrivateKey)
                    ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () CertificateChain) PrivateKey)
                    ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString) ByteString)
                    ((,) PublicKey HashAndSignatureAlgorithm))
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () PrivateKey) ((,) ClientHelloMsg ByteString))
                    Cipher) ((,) GroupPublic GroupKey)) ByteString) ByteString)
                    ((,) PublicKey HashAndSignatureAlgorithm)) ByteString)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString) ByteString) ByteString)
                    Handshake13)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString) ByteString) ByteString)
                    ByteString)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString) ByteString) ByteString)
                    ByteString) ByteString)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString) ByteString) ByteString)
                    ByteString) ByteString)
                    (Prelude.Either
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,)
                    ((,) ((,) ((,) () ((,) ClientHelloMsg ByteString)) Cipher)
                    ((,) GroupPublic GroupKey)) ByteString) ByteString) ByteString)
                    ByteString) ByteString) (GHC.Base.Maybe ())))))))))))))))
                    (GHC.Base.Maybe (SigT Eff_tls Args_tls))) (GHC.Base.Maybe ())
doHandshake_step =
  sum_merge
    (prod_curry
      (prod_curry (\_ c p _ _ -> Prelude.Left ((,) (Prelude.Right (Prelude.Left ((,)
        ((,) () c) p))) (GHC.Base.Just (ExistT RecvClientHello
        (unsafeCoerce ())))))))
    (sum_merge
      (prod_curry
        (prod_curry (\_ c p ->
          lift_tls RecvClientHello (\r -> Prelude.Left ((,)
            (case chooseCipher (chCiphers (fst (unsafeCoerce r)))
                    ciphersuite_default of {
              GHC.Base.Just a ->
               case extension_KeyShare (chExtension (fst (unsafeCoerce r))) of {
                GHC.Base.Just a0 ->
                 case findKeyShare a0 serverGroups of {
                  GHC.Base.Just a1 ->
                   case decodeGroupPublic (ksGroup a1) (ksData a1) of {
                    Prelude.Left _ -> Prelude.Right (Prelude.Right (Prelude.Right
                     (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                     (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                     (Prelude.Right (Prelude.Right (Prelude.Right
                     GHC.Base.Nothing)))))))))))));
                    Prelude.Right b -> Prelude.Right (Prelude.Right (Prelude.Left
                     ((,) ((,) ((,) ((,) ((,) ((,) () c) p) (unsafeCoerce r)) a) a1)
                     b)))};
                  GHC.Base.Nothing -> Prelude.Right (Prelude.Right (Prelude.Right
                   (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                   (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                   (Prelude.Right (Prelude.Right (Prelude.Right
                   GHC.Base.Nothing)))))))))))))};
                GHC.Base.Nothing -> Prelude.Right (Prelude.Right (Prelude.Right
                 (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                 (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                 (Prelude.Right (Prelude.Right (Prelude.Right
                 GHC.Base.Nothing)))))))))))))};
              GHC.Base.Nothing -> Prelude.Right (Prelude.Right (Prelude.Right
               (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
               (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
               (Prelude.Right (Prelude.Right (Prelude.Right
               GHC.Base.Nothing)))))))))))))})
            (case chooseCipher (chCiphers (fst (unsafeCoerce r)))
                    ciphersuite_default of {
              GHC.Base.Just _ ->
               case extension_KeyShare (chExtension (fst (unsafeCoerce r))) of {
                GHC.Base.Just a ->
                 case findKeyShare a serverGroups of {
                  GHC.Base.Just a0 ->
                   case decodeGroupPublic (ksGroup a0) (ksData a0) of {
                    Prelude.Left _ -> GHC.Base.Nothing;
                    Prelude.Right b -> GHC.Base.Just (ExistT GroupGetPubShared
                     (unsafeCoerce b))};
                  GHC.Base.Nothing -> GHC.Base.Nothing};
                GHC.Base.Nothing -> GHC.Base.Nothing};
              GHC.Base.Nothing -> GHC.Base.Nothing}))))))
      (sum_merge
        (prod_curry
          (prod_curry
            (prod_curry
              (prod_curry
                (prod_curry
                  (prod_curry (\_ c p r c0 k _ ->
                    lift_tls GroupGetPubShared (\r0 -> Prelude.Left ((,)
                      (case unsafeCoerce r0 of {
                        GHC.Base.Just a -> Prelude.Right (Prelude.Right
                         (Prelude.Right (Prelude.Left ((,) ((,) ((,) ((,) ((,) ((,)
                         () c) p) r) c0) k) a))));
                        GHC.Base.Nothing -> Prelude.Right (Prelude.Right
                         (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                         (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                         (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                         GHC.Base.Nothing)))))))))))))})
                      (case unsafeCoerce r0 of {
                        GHC.Base.Just _ -> GHC.Base.Just (ExistT GetRandomBytes
                         (unsafeCoerce ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                           ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                           ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                           ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                           ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                           ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                           ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                           ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                           ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                           ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                           ((Prelude.+) 1 ((Prelude.+) 1
                           0))))))))))))))))))))))))))))))))));
                        GHC.Base.Nothing -> GHC.Base.Nothing}))))))))))
        (sum_merge
          (prod_curry
            (prod_curry
              (prod_curry
                (prod_curry
                  (prod_curry
                    (prod_curry (\_ c p r c0 k p0 ->
                      lift_tls GetRandomBytes (\r0 -> Prelude.Left ((,)
                        (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                        (Prelude.Left ((,) ((,) ((,) ((,) ((,) ((,) ((,) () c) p) r)
                        c0) k) p0) (unsafeCoerce r0))))))) (GHC.Base.Just (ExistT
                        SendPacket
                        (unsafeCoerce ((,)
                          (handshake13 ((:)
                            (serverHello13 (unsafeCoerce r0) (chSession (fst r))
                              (cipherID c0) ((:)
                              (extensionRaw_KeyShare
                                (extensionEncode_KeyShare (I.KeyShareEntry
                                  (ksGroup k) (encodeGroupPublic (fst p0))))) ((:)
                              (extensionRaw_SupportedVersions
                                (extensionEncode_SupportedVersions tLS13)) [])))
                            [])) GHC.Base.Nothing)))))))))))))
          (sum_merge
            (prod_curry
              (prod_curry
                (prod_curry
                  (prod_curry
                    (prod_curry
                      (prod_curry
                        (prod_curry (\_ c p r c0 _ p0 _ ->
                          lift_tls SendPacket (\r0 -> Prelude.Left ((,)
                            (Prelude.Right (Prelude.Right (Prelude.Right
                            (Prelude.Right (Prelude.Right (Prelude.Left ((,) ((,)
                            ((,) ((,) ((,) ((,) () c) p) r) c0) p0)
                            (unsafeCoerce r0)))))))) (GHC.Base.Just (ExistT
                            SendPacket
                            (unsafeCoerce ((,) changeCipherSpec GHC.Base.Nothing))))))))))))))
            (sum_merge
              (prod_curry
                (prod_curry
                  (prod_curry
                    (prod_curry
                      (prod_curry
                        (prod_curry (\_ c p r c0 p0 r0 ->
                          lift_tls SendPacket (\_ -> Prelude.Left ((,)
                            (Prelude.Right (Prelude.Right (Prelude.Right
                            (Prelude.Right (Prelude.Right (Prelude.Right
                            (Prelude.Left ((,) ((,) ((,) ((,) ((,) ((,) () c) p) r)
                            c0) p0) r0)))))))) (GHC.Base.Just (ExistT SendPacket
                            (unsafeCoerce ((,)
                              (handshake13 ((:) (encryptedExtensions13 []) []))
                              (GHC.Base.Just ((,) ((,) ((,) (cipherHash c0) c0)
                              (hkdfExpandLabel (cipherHash c0)
                                (hkdfExtract (cipherHash c0)
                                  (hkdfExpandLabel (cipherHash c0)
                                    (hkdfExtract (cipherHash c0)
                                      (b_replicate (hashDigestSize (cipherHash c0))
                                        w0)
                                      (b_replicate (hashDigestSize (cipherHash c0))
                                        w0))
                                    (s2b ((:) 'd' ((:) 'e' ((:) 'r' ((:) 'i' ((:)
                                      'v' ((:) 'e' ((:) 'd' ([])))))))))
                                    (hashWith (cipherHash c0) ((:) (s2b ([])) []))
                                    (hashDigestSize (cipherHash c0)))
                                  (ba_convert (snd p0)))
                                (s2b ((:) 's' ((:) ' ' ((:) 'h' ((:) 's' ((:) ' '
                                  ((:) 't' ((:) 'r' ((:) 'a' ((:) 'f' ((:) 'f' ((:)
                                  'i' ((:) 'c' ([]))))))))))))))
                                (hashWith (cipherHash c0) ((:) (snd r) ((:) r0 [])))
                                (hashDigestSize (cipherHash c0)))) 0)))))))))))))))
              (sum_merge
                (prod_curry
                  (prod_curry
                    (prod_curry
                      (prod_curry
                        (prod_curry
                          (prod_curry (\_ c p r c0 p0 r0 ->
                            lift_tls SendPacket (\r1 -> Prelude.Left ((,)
                              (case decideCredInfo p (getCertificates c)
                                      (extension_SignatureAlgorithms
                                        (chExtension (fst r))) of {
                                GHC.Base.Just a -> Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Left ((,)
                                 ((,) ((,) ((,) ((,) ((,) ((,) ((,) () c) p) r) c0)
                                 p0) r0) (unsafeCoerce r1)) a))))))));
                                GHC.Base.Nothing -> Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 GHC.Base.Nothing)))))))))))))})
                              (case decideCredInfo p (getCertificates c)
                                      (extension_SignatureAlgorithms
                                        (chExtension (fst r))) of {
                                GHC.Base.Just _ -> GHC.Base.Just (ExistT SendPacket
                                 (unsafeCoerce ((,)
                                   (handshake13 ((:)
                                     (certificate13 empty c ((:) [] [])) []))
                                   (GHC.Base.Just ((,) ((,) ((,) (cipherHash c0) c0)
                                   (hkdfExpandLabel (cipherHash c0)
                                     (hkdfExtract (cipherHash c0)
                                       (hkdfExpandLabel (cipherHash c0)
                                         (hkdfExtract (cipherHash c0)
                                           (b_replicate
                                             (hashDigestSize (cipherHash c0)) w0)
                                           (b_replicate
                                             (hashDigestSize (cipherHash c0)) w0))
                                         (s2b ((:) 'd' ((:) 'e' ((:) 'r' ((:) 'i'
                                           ((:) 'v' ((:) 'e' ((:) 'd' ([])))))))))
                                         (hashWith (cipherHash c0) ((:) (s2b ([]))
                                           [])) (hashDigestSize (cipherHash c0)))
                                       (ba_convert (snd p0)))
                                     (s2b ((:) 's' ((:) ' ' ((:) 'h' ((:) 's' ((:)
                                       ' ' ((:) 't' ((:) 'r' ((:) 'a' ((:) 'f' ((:)
                                       'f' ((:) 'i' ((:) 'c' ([]))))))))))))))
                                     (hashWith (cipherHash c0) ((:) (snd r) ((:) r0
                                       []))) (hashDigestSize (cipherHash c0))))
                                   ((Prelude.+) 1 0))))));
                                GHC.Base.Nothing -> GHC.Base.Nothing}))))))))))
                (sum_merge
                  (prod_curry
                    (prod_curry
                      (prod_curry
                        (prod_curry
                          (prod_curry
                            (prod_curry
                              (prod_curry
                                (prod_curry (\_ _ p r c p0 r0 r1 p1 ->
                                  lift_tls SendPacket (\r2 -> Prelude.Left ((,)
                                    (Prelude.Right (Prelude.Right (Prelude.Right
                                    (Prelude.Right (Prelude.Right (Prelude.Right
                                    (Prelude.Right (Prelude.Right (Prelude.Left ((,)
                                    ((,) ((,) ((,) ((,) ((,) ((,) ((,) () p) r) c)
                                    p0) r0) r1) p1) (unsafeCoerce r2)))))))))))
                                    (GHC.Base.Just (ExistT MakeCertVerify
                                    (unsafeCoerce ((,) ((,) ((,) (fst p1) p)
                                      (snd p1))
                                      (hashWith (cipherHash c) ((:) (snd r) ((:) r0
                                        ((:) r1 ((:) (unsafeCoerce r2) []))))))))))))))))))))
                  (sum_merge
                    (prod_curry
                      (prod_curry
                        (prod_curry
                          (prod_curry
                            (prod_curry
                              (prod_curry
                                (prod_curry
                                  (prod_curry (\_ _ r c p r0 r1 _ r2 ->
                                    lift_tls MakeCertVerify (\r3 -> Prelude.Left
                                      ((,) (Prelude.Right (Prelude.Right
                                      (Prelude.Right (Prelude.Right (Prelude.Right
                                      (Prelude.Right (Prelude.Right (Prelude.Right
                                      (Prelude.Right (Prelude.Left ((,) ((,) ((,)
                                      ((,) ((,) ((,) ((,) () r) c) p) r0) r1) r2)
                                      (unsafeCoerce r3)))))))))))) (GHC.Base.Just
                                      (ExistT SendPacket
                                      (unsafeCoerce ((,)
                                        (handshake13 ((:) (unsafeCoerce r3) []))
                                        (GHC.Base.Just ((,) ((,) ((,) (cipherHash c)
                                        c)
                                        (hkdfExpandLabel (cipherHash c)
                                          (hkdfExtract (cipherHash c)
                                            (hkdfExpandLabel (cipherHash c)
                                              (hkdfExtract (cipherHash c)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c))
                                                  w0)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c))
                                                  w0))
                                              (s2b ((:) 'd' ((:) 'e' ((:) 'r' ((:)
                                                'i' ((:) 'v' ((:) 'e' ((:) 'd'
                                                ([])))))))))
                                              (hashWith (cipherHash c) ((:)
                                                (s2b ([])) []))
                                              (hashDigestSize (cipherHash c)))
                                            (ba_convert (snd p)))
                                          (s2b ((:) 's' ((:) ' ' ((:) 'h' ((:) 's'
                                            ((:) ' ' ((:) 't' ((:) 'r' ((:) 'a' ((:)
                                            'f' ((:) 'f' ((:) 'i' ((:) 'c'
                                            ([]))))))))))))))
                                          (hashWith (cipherHash c) ((:) (snd r) ((:)
                                            r0 [])))
                                          (hashDigestSize (cipherHash c))))
                                        ((Prelude.+) 1 ((Prelude.+) 1 0)))))))))))))))))))
                    (sum_merge
                      (prod_curry
                        (prod_curry
                          (prod_curry
                            (prod_curry
                              (prod_curry
                                (prod_curry
                                  (prod_curry (\_ r c p r0 r1 r2 _ ->
                                    lift_tls SendPacket (\r3 -> Prelude.Left ((,)
                                      (Prelude.Right (Prelude.Right (Prelude.Right
                                      (Prelude.Right (Prelude.Right (Prelude.Right
                                      (Prelude.Right (Prelude.Right (Prelude.Right
                                      (Prelude.Right (Prelude.Left ((,) ((,) ((,)
                                      ((,) ((,) ((,) ((,) () r) c) p) r0) r1) r2)
                                      (unsafeCoerce r3))))))))))))) (GHC.Base.Just
                                      (ExistT SendPacket
                                      (unsafeCoerce ((,)
                                        (handshake13 ((:)
                                          (finished13
                                            (makeVerifyData (cipherHash c)
                                              (hkdfExpandLabel (cipherHash c)
                                                (hkdfExtract (cipherHash c)
                                                  (hkdfExpandLabel (cipherHash c)
                                                    (hkdfExtract (cipherHash c)
                                                      (b_replicate
                                                        (hashDigestSize
                                                          (cipherHash c)) w0)
                                                      (b_replicate
                                                        (hashDigestSize
                                                          (cipherHash c)) w0))
                                                    (s2b ((:) 'd' ((:) 'e' ((:) 'r'
                                                      ((:) 'i' ((:) 'v' ((:) 'e'
                                                      ((:) 'd' ([])))))))))
                                                    (hashWith (cipherHash c) ((:)
                                                      (s2b ([])) []))
                                                    (hashDigestSize (cipherHash c)))
                                                  (ba_convert (snd p)))
                                                (s2b ((:) 's' ((:) ' ' ((:) 'h' ((:)
                                                  's' ((:) ' ' ((:) 't' ((:) 'r'
                                                  ((:) 'a' ((:) 'f' ((:) 'f' ((:)
                                                  'i' ((:) 'c' ([]))))))))))))))
                                                (hashWith (cipherHash c) ((:)
                                                  (snd r) ((:) r0 [])))
                                                (hashDigestSize (cipherHash c)))
                                              (hashWith (cipherHash c) ((:) 
                                                (snd r) ((:) r0 ((:) r1 ((:) r2 ((:)
                                                (unsafeCoerce r3) [])))))))) []))
                                        (GHC.Base.Just ((,) ((,) ((,) (cipherHash c)
                                        c)
                                        (hkdfExpandLabel (cipherHash c)
                                          (hkdfExtract (cipherHash c)
                                            (hkdfExpandLabel (cipherHash c)
                                              (hkdfExtract (cipherHash c)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c))
                                                  w0)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c))
                                                  w0))
                                              (s2b ((:) 'd' ((:) 'e' ((:) 'r' ((:)
                                                'i' ((:) 'v' ((:) 'e' ((:) 'd'
                                                ([])))))))))
                                              (hashWith (cipherHash c) ((:)
                                                (s2b ([])) []))
                                              (hashDigestSize (cipherHash c)))
                                            (ba_convert (snd p)))
                                          (s2b ((:) 's' ((:) ' ' ((:) 'h' ((:) 's'
                                            ((:) ' ' ((:) 't' ((:) 'r' ((:) 'a' ((:)
                                            'f' ((:) 'f' ((:) 'i' ((:) 'c'
                                            ([]))))))))))))))
                                          (hashWith (cipherHash c) ((:) (snd r) ((:)
                                            r0 [])))
                                          (hashDigestSize (cipherHash c))))
                                        ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                                        0)))))))))))))))))))
                      (sum_merge
                        (prod_curry
                          (prod_curry
                            (prod_curry
                              (prod_curry
                                (prod_curry
                                  (prod_curry
                                    (prod_curry (\_ r c p r0 r1 r2 r3 ->
                                      lift_tls SendPacket (\r4 -> Prelude.Left ((,)
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Right (Prelude.Left
                                        ((,) ((,) ((,) ((,) ((,) ((,) ((,) ((,) ()
                                        r) c) p) r0) r1) r2) r3)
                                        (unsafeCoerce r4))))))))))))))
                                        (GHC.Base.Just (ExistT RecvCCS
                                        (unsafeCoerce ())))))))))))))
                        (sum_merge
                          (prod_curry
                            (prod_curry
                              (prod_curry
                                (prod_curry
                                  (prod_curry
                                    (prod_curry
                                      (prod_curry
                                        (prod_curry (\_ r c p r0 r1 r2 r3 r4 ->
                                          lift_tls RecvCCS (\_ -> Prelude.Left ((,)
                                            (Prelude.Right (Prelude.Right
                                            (Prelude.Right (Prelude.Right
                                            (Prelude.Right (Prelude.Right
                                            (Prelude.Right (Prelude.Right
                                            (Prelude.Right (Prelude.Right
                                            (Prelude.Right (Prelude.Right
                                            (Prelude.Left ((,) ((,) ((,) ((,) ((,)
                                            ((,) ((,) ((,) () r) c) p) r0) r1) r2)
                                            r3) r4)))))))))))))) (GHC.Base.Just
                                            (ExistT RecvFinished
                                            (unsafeCoerce (GHC.Base.Just ((,) ((,)
                                              (cipherHash c) c)
                                              (hkdfExpandLabel (cipherHash c)
                                                (hkdfExtract (cipherHash c)
                                                  (hkdfExpandLabel (cipherHash c)
                                                    (hkdfExtract (cipherHash c)
                                                      (b_replicate
                                                        (hashDigestSize
                                                          (cipherHash c)) w0)
                                                      (b_replicate
                                                        (hashDigestSize
                                                          (cipherHash c)) w0))
                                                    (s2b ((:) 'd' ((:) 'e' ((:) 'r'
                                                      ((:) 'i' ((:) 'v' ((:) 'e'
                                                      ((:) 'd' ([])))))))))
                                                    (hashWith (cipherHash c) ((:)
                                                      (s2b ([])) []))
                                                    (hashDigestSize (cipherHash c)))
                                                  (ba_convert (snd p)))
                                                (s2b ((:) 'c' ((:) ' ' ((:) 'h' ((:)
                                                  's' ((:) ' ' ((:) 't' ((:) 'r'
                                                  ((:) 'a' ((:) 'f' ((:) 'f' ((:)
                                                  'i' ((:) 'c' ([]))))))))))))))
                                                (hashWith (cipherHash c) ((:)
                                                  (snd r) ((:) r0 [])))
                                                (hashDigestSize (cipherHash c)))))))))))))))))))
                          (sum_merge
                            (prod_curry
                              (prod_curry
                                (prod_curry
                                  (prod_curry
                                    (prod_curry
                                      (prod_curry
                                        (prod_curry
                                          (prod_curry (\_ r c p r0 r1 r2 r3 r4 ->
                                            lift_tls RecvFinished (\r5 ->
                                              Prelude.Left ((,)
                                              (case byteString_beq (unsafeCoerce r5)
                                                      (makeVerifyData (cipherHash c)
                                                        (hkdfExpandLabel
                                                          (cipherHash c)
                                                          (hkdfExtract
                                                            (cipherHash c)
                                                            (hkdfExpandLabel
                                                              (cipherHash c)
                                                              (hkdfExtract
                                                                (cipherHash c)
                                                                (b_replicate
                                                                  (hashDigestSize
                                                                    (cipherHash c))
                                                                  w0)
                                                                (b_replicate
                                                                  (hashDigestSize
                                                                    (cipherHash c))
                                                                  w0))
                                                              (s2b ((:) 'd' ((:) 'e'
                                                                ((:) 'r' ((:) 'i'
                                                                ((:) 'v' ((:) 'e'
                                                                ((:) 'd'
                                                                ([])))))))))
                                                              (hashWith
                                                                (cipherHash c) ((:)
                                                                (s2b ([])) []))
                                                              (hashDigestSize
                                                                (cipherHash c)))
                                                            (ba_convert (snd p)))
                                                          (s2b ((:) 'c' ((:) ' '
                                                            ((:) 'h' ((:) 's' ((:)
                                                            ' ' ((:) 't' ((:) 'r'
                                                            ((:) 'a' ((:) 'f' ((:)
                                                            'f' ((:) 'i' ((:) 'c'
                                                            ([]))))))))))))))
                                                          (hashWith (cipherHash c)
                                                            ((:) (snd r) ((:) r0
                                                            [])))
                                                          (hashDigestSize
                                                            (cipherHash c)))
                                                        (hashWith (cipherHash c)
                                                          ((:) (snd r) ((:) r0 ((:)
                                                          r1 ((:) r2 ((:) r3 ((:) r4
                                                          [])))))))) of {
                                                GHC.Base.True -> Prelude.Right
                                                 (Prelude.Right (Prelude.Right
                                                 (Prelude.Right (Prelude.Right
                                                 (Prelude.Right (Prelude.Right
                                                 (Prelude.Right (Prelude.Right
                                                 (Prelude.Right (Prelude.Right
                                                 (Prelude.Right (Prelude.Right
                                                 (Prelude.Left ((,) ((,) ((,) ((,)
                                                 ((,) ((,) ((,) ((,) () r) c) p) r0)
                                                 r1) r2) r3) r4))))))))))))));
                                                GHC.Base.False -> Prelude.Right
                                                 (Prelude.Right (Prelude.Right
                                                 (Prelude.Right (Prelude.Right
                                                 (Prelude.Right (Prelude.Right
                                                 (Prelude.Right (Prelude.Right
                                                 (Prelude.Right (Prelude.Right
                                                 (Prelude.Right (Prelude.Right
                                                 (Prelude.Right
                                                 GHC.Base.Nothing)))))))))))))})
                                              (case byteString_beq (unsafeCoerce r5)
                                                      (makeVerifyData (cipherHash c)
                                                        (hkdfExpandLabel
                                                          (cipherHash c)
                                                          (hkdfExtract
                                                            (cipherHash c)
                                                            (hkdfExpandLabel
                                                              (cipherHash c)
                                                              (hkdfExtract
                                                                (cipherHash c)
                                                                (b_replicate
                                                                  (hashDigestSize
                                                                    (cipherHash c))
                                                                  w0)
                                                                (b_replicate
                                                                  (hashDigestSize
                                                                    (cipherHash c))
                                                                  w0))
                                                              (s2b ((:) 'd' ((:) 'e'
                                                                ((:) 'r' ((:) 'i'
                                                                ((:) 'v' ((:) 'e'
                                                                ((:) 'd'
                                                                ([])))))))))
                                                              (hashWith
                                                                (cipherHash c) ((:)
                                                                (s2b ([])) []))
                                                              (hashDigestSize
                                                                (cipherHash c)))
                                                            (ba_convert (snd p)))
                                                          (s2b ((:) 'c' ((:) ' '
                                                            ((:) 'h' ((:) 's' ((:)
                                                            ' ' ((:) 't' ((:) 'r'
                                                            ((:) 'a' ((:) 'f' ((:)
                                                            'f' ((:) 'i' ((:) 'c'
                                                            ([]))))))))))))))
                                                          (hashWith (cipherHash c)
                                                            ((:) (snd r) ((:) r0
                                                            [])))
                                                          (hashDigestSize
                                                            (cipherHash c)))
                                                        (hashWith (cipherHash c)
                                                          ((:) (snd r) ((:) r0 ((:)
                                                          r1 ((:) r2 ((:) r3 ((:) r4
                                                          [])))))))) of {
                                                GHC.Base.True -> GHC.Base.Just
                                                 (ExistT SendPacket
                                                 (unsafeCoerce ((,)
                                                   (appData13
                                                     (s2b ((:) 'h' ((:) 'e' ((:) 'l'
                                                       ((:) 'l' ((:) 'o' ((:) ' '
                                                       ([]))))))))) (GHC.Base.Just
                                                   ((,) ((,) ((,) (cipherHash c) c)
                                                   (hkdfExpandLabel (cipherHash c)
                                                     (hkdfExtract (cipherHash c)
                                                       (hkdfExpandLabel
                                                         (cipherHash c)
                                                         (hkdfExtract (cipherHash c)
                                                           (hkdfExpandLabel
                                                             (cipherHash c)
                                                             (hkdfExtract
                                                               (cipherHash c)
                                                               (b_replicate
                                                                 (hashDigestSize
                                                                   (cipherHash c))
                                                                 w0)
                                                               (b_replicate
                                                                 (hashDigestSize
                                                                   (cipherHash c))
                                                                 w0))
                                                             (s2b ((:) 'd' ((:) 'e'
                                                               ((:) 'r' ((:) 'i'
                                                               ((:) 'v' ((:) 'e'
                                                               ((:) 'd' ([])))))))))
                                                             (hashWith
                                                               (cipherHash c) ((:)
                                                               (s2b ([])) []))
                                                             (hashDigestSize
                                                               (cipherHash c)))
                                                           (ba_convert (snd p)))
                                                         (s2b ((:) 'd' ((:) 'e' ((:)
                                                           'r' ((:) 'i' ((:) 'v'
                                                           ((:) 'e' ((:) 'd'
                                                           ([])))))))))
                                                         (hashWith (cipherHash c)
                                                           ((:) (s2b ([])) []))
                                                         (hashDigestSize
                                                           (cipherHash c)))
                                                       (b_replicate
                                                         (hashDigestSize
                                                           (cipherHash c)) w0))
                                                     (s2b ((:) 's' ((:) ' ' ((:) 'a'
                                                       ((:) 'p' ((:) ' ' ((:) 't'
                                                       ((:) 'r' ((:) 'a' ((:) 'f'
                                                       ((:) 'f' ((:) 'i' ((:) 'c'
                                                       ([]))))))))))))))
                                                     (hashWith (cipherHash c) ((:)
                                                       (snd r) ((:) r0 ((:) r1 ((:)
                                                       r2 ((:) r3 ((:) r4 [])))))))
                                                     (hashDigestSize (cipherHash c))))
                                                   0)))));
                                                GHC.Base.False -> GHC.Base.Nothing}))))))))))))
                            (sum_merge
                              (prod_curry
                                (prod_curry
                                  (prod_curry
                                    (prod_curry
                                      (prod_curry
                                        (prod_curry
                                          (prod_curry
                                            (prod_curry (\_ _ _ _ _ _ _ _ _ ->
                                              lift_tls SendPacket (\_ ->
                                                Prelude.Left ((,) (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (GHC.Base.Just
                                                ()))))))))))))))) GHC.Base.Nothing)))))))))))
                              (\o _ _ -> Prelude.Right o))))))))))))))

