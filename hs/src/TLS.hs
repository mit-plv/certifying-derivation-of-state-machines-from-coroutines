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
import qualified Data.Word
import qualified Data.Bits
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

__ :: any
__ = Prelude.error "Logical or arity value used"

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

data Comparison =
   Eq
 | Lt
 | Gt

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
data SigT a p =
   ExistT a p

projT1 :: (SigT a1 a2) -> a1
projT1 x =
  case x of {
   ExistT a _ -> a}

projT2 :: (SigT a1 a2) -> a2
projT2 x =
  case x of {
   ExistT _ h -> h}

add :: GHC.Base.Int -> GHC.Base.Int -> GHC.Base.Int
add n m =
  (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\p -> (Prelude.+) 1 (add p m))
    n

compare :: GHC.Base.Int -> GHC.Base.Int -> Comparison
compare n m =
  (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
      (\_ -> Eq)
      (\_ -> Lt)
      m)
    (\n' ->
    (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
      (\_ -> Gt)
      (\m' -> compare n' m')
      m)
    n

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

data Positive =
   XI Positive
 | XO Positive
 | XH

data N =
   N0
 | Npos Positive

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add0 :: Positive -> Positive -> Positive
add0 x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add0 p q);
     XH -> XO (succ p)};
   XO p -> case y of {
            XI q -> XI (add0 p q);
            XO q -> XO (add0 p q);
            XH -> XI p};
   XH -> case y of {
          XI q -> XO (succ q);
          XO q -> XI q;
          XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add0 p q);
     XH -> XO (succ p)};
   XH -> case y of {
          XI q -> XI (succ q);
          XO q -> XO (succ q);
          XH -> XI XH}}

mul :: Positive -> Positive -> Positive
mul x y =
  case x of {
   XI p -> add0 y (XO (mul p y));
   XO p -> XO (mul p y);
   XH -> y}

iter_op :: (a1 -> a1 -> a1) -> Positive -> a1 -> a1
iter_op op p a =
  case p of {
   XI p0 -> op a (iter_op op p0 (op a a));
   XO p0 -> iter_op op p0 (op a a);
   XH -> a}

to_nat :: Positive -> GHC.Base.Int
to_nat x =
  iter_op add x ((Prelude.+) 1 0)

add1 :: N -> N -> N
add1 n m =
  case n of {
   N0 -> m;
   Npos p -> case m of {
              N0 -> n;
              Npos q -> Npos (add0 p q)}}

mul0 :: N -> N -> N
mul0 n m =
  case n of {
   N0 -> N0;
   Npos p -> case m of {
              N0 -> N0;
              Npos q -> Npos (mul p q)}}

to_nat0 :: N -> GHC.Base.Int
to_nat0 a =
  case a of {
   N0 -> 0;
   Npos p -> to_nat p}

n_of_digits :: (([]) GHC.Base.Bool) -> N
n_of_digits l =
  case l of {
   [] -> N0;
   (:) b l' ->
    add1 (case b of {
           GHC.Base.True -> Npos XH;
           GHC.Base.False -> N0}) (mul0 (Npos (XO XH)) (n_of_digits l'))}

n_of_ascii :: Prelude.Char -> N
n_of_ascii a =
  (\f a -> f (Data.Bits.testBit (Data.Char.ord a) 0)
              (Data.Bits.testBit (Data.Char.ord a) 1)
              (Data.Bits.testBit (Data.Char.ord a) 2)
              (Data.Bits.testBit (Data.Char.ord a) 3)
              (Data.Bits.testBit (Data.Char.ord a) 4)
              (Data.Bits.testBit (Data.Char.ord a) 5)
              (Data.Bits.testBit (Data.Char.ord a) 6)
              (Data.Bits.testBit (Data.Char.ord a) 7))
    (\a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits ((:) a0 ((:) a1 ((:) a2 ((:) a3 ((:) a4 ((:) a5 ((:) a6 ((:) a7
      [])))))))))
    a

nat_of_ascii :: Prelude.Char -> GHC.Base.Int
nat_of_ascii a =
  to_nat0 (n_of_ascii a)

data Map a =
   Node ((,) Prelude.String a) (Map a) (Map a)
 | Leaf

compareAscii :: Prelude.Char -> Prelude.Char -> Comparison
compareAscii x y =
  compare (nat_of_ascii x) (nat_of_ascii y)

compareString :: Prelude.String -> Prelude.String -> Comparison
compareString x y =
  case x of {
   ([]) -> case y of {
            ([]) -> Eq;
            (:) _ _ -> Lt};
   (:) c x' ->
    case y of {
     ([]) -> Gt;
     (:) d y' -> case compareAscii c d of {
                  Eq -> compareString x' y';
                  x0 -> x0}}}

lebString :: Prelude.String -> Prelude.String -> GHC.Base.Bool
lebString x y =
  case compareString x y of {
   Gt -> GHC.Base.False;
   _ -> GHC.Base.True}

insert :: Prelude.String -> a1 -> (Map a1) -> Map a1
insert x a0 t =
  case t of {
   Node p l r ->
    case p of {
     (,) y a ->
      case lebString x y of {
       GHC.Base.True -> Node ((,) y a) (insert x a0 l) r;
       GHC.Base.False -> Node ((,) y a) l (insert x a0 r)}};
   Leaf -> Node ((,) x a0) Leaf Leaf}

bsearch :: Prelude.String -> (Map a1) -> GHC.Base.Maybe a1
bsearch key t =
  case t of {
   Node p l r ->
    case p of {
     (,) x a ->
      case compareString key x of {
       Eq -> GHC.Base.Just a;
       Lt -> bsearch key l;
       Gt -> bsearch key r}};
   Leaf -> GHC.Base.Nothing}

replace_map :: Prelude.String -> a1 -> (Map a1) -> Map a1
replace_map key a0 t =
  case t of {
   Node p l r ->
    case p of {
     (,) x a ->
      case compareString key x of {
       Eq -> Node ((,) key a0) l r;
       Lt -> Node ((,) x a) (replace_map key a0 l) r;
       Gt -> Node ((,) x a) l (replace_map key a0 r)}};
   Leaf -> Leaf}

type Step_type eff args rets ret_type state =
  state -> eff -> rets -> Prelude.Either
  ((,) state (GHC.Base.Maybe (SigT eff args))) ret_type

data Yield_effect =
   Yield

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

type Word32 = Data.Word.Word32

type PublicKey = X.PubKey

type PrivateKey = X.PrivKey

type GroupPublic = I.GroupPublic

type GroupKey = I.GroupKey

type Hash = T.Hash

type Cipher = T.Cipher

type HashAndSignatureAlgorithm = I.HashAndSignatureAlgorithm

type KeyUpdate = I.KeyUpdate

type Certificate = X.Certificate

type CertificateChain = X.CertificateChain

type Signature = I.Signature

clientHello :: I.Packet13 -> GHC.Base.Maybe
               ((,) ((,) ((,) ((,) Version ByteString) Session) (([]) ExtensionRaw))
               (([]) CipherID))
clientHello h =
  case h of {
   I.Handshake13 l ->
    case l of {
     [] -> GHC.Base.Nothing;
     (:) c l0 ->
      case c of {
       I.ClientHello13 v rand sess cipherIDs ext ->
        case l0 of {
         [] -> GHC.Base.Just ((,) ((,) ((,) ((,) v (I.unClientRandom rand)) sess) ext) cipherIDs);
         (:) _ _ -> GHC.Base.Nothing};
       _ -> GHC.Base.Nothing}};
   _ -> GHC.Base.Nothing}

finished :: I.Handshake13 -> GHC.Base.Maybe ByteString
finished h =
  case h of {
   I.Finished13 bs -> GHC.Base.Just bs;
   _ -> GHC.Base.Nothing}

handshake :: I.Packet13 -> GHC.Base.Maybe I.Handshake13
handshake p =
  case p of {
   I.Handshake13 l ->
    case l of {
     [] -> GHC.Base.Nothing;
     (:) h l0 -> case l0 of {
                  [] -> GHC.Base.Just h;
                  (:) _ _ -> GHC.Base.Nothing}};
   _ -> GHC.Base.Nothing}

changeCipherSpec :: I.Packet13 -> GHC.Base.Maybe ()
changeCipherSpec p =
  case p of
    I.ChangeCipherSpec13 -> GHC.Base.Just ()
    _ -> GHC.Base.Nothing

appData :: I.Packet13 -> GHC.Base.Maybe ByteString
appData p =
  case p of {
   I.AppData13 dat -> GHC.Base.Just dat;
   _ -> GHC.Base.Nothing}

type Args_tls' =
  Prelude.Either
  (Prelude.Either
  (Prelude.Either
  (Prelude.Either GHC.Base.Int
  ((,) I.Packet13
  (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int))))
  GroupPublic)
  ((,) ((,) ((,) PublicKey PrivateKey) HashAndSignatureAlgorithm) ByteString))
  GHC.Base.Int

type Rets_tls' =
  Prelude.Either
  (Prelude.Either (GHC.Base.Maybe ((,) GroupPublic GroupKey)) I.Handshake13)
  ByteString

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

extension_SignatureAlgorithms :: (([]) ExtensionRaw) -> ([])
                                 HashAndSignatureAlgorithm
extension_SignatureAlgorithms = (\exts -> case Helper.extensionLookup I.extensionID_SignatureAlgorithms exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.SignatureAlgorithms sas) -> sas })

getCertificates :: CertificateChain -> ([]) Certificate
getCertificates = \cch -> case cch of { X.CertificateChain certs -> Prelude.map X.getCertificate certs }

empty :: ByteString
empty = B.empty

hashWith :: Hash -> (([]) ByteString) -> ByteString
hashWith = Helper.hashWith

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

hmac :: Hash -> ByteString -> ByteString -> ByteString
hmac = I.hmac

inb :: (a1 -> a1 -> GHC.Base.Bool) -> a1 -> (([]) a1) -> GHC.Base.Bool
inb eqbA x l =
  case l of {
   [] -> GHC.Base.False;
   (:) y l' ->
    case eqbA x y of {
     GHC.Base.True -> GHC.Base.True;
     GHC.Base.False -> inb eqbA x l'}}

chooseCipher :: (([]) CipherID) -> (([]) Cipher) -> GHC.Base.Maybe Cipher
chooseCipher clientCipherIDs serverCiphers0 =
  hd_error
    (filter (\cipher -> inb cipherID_beq (cipherID cipher) clientCipherIDs)
      serverCiphers0)

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

lF :: Prelude.String
lF =
  (:) '\n' ([])

mconcat :: (([]) ByteString) -> ByteString
mconcat = B.concat

serverCiphers :: ([]) Cipher
serverCiphers = I.ciphersuite_13

replicate :: GHC.Base.Int -> a1 -> ([]) a1
replicate n a =
  (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
    (\_ -> [])
    (\n' -> (:) a (replicate n' a))
    n

type ProtocolType = I.ProtocolType

hdReadLen :: I.Header -> GHC.Base.Int
hdReadLen hd =
  case hd of {
   I.Header _ _ n -> Prelude.fromIntegral n}

decodeHeader :: ByteString -> I.Header
decodeHeader bs =
  case I.decodeHeader bs of
    Prelude.Right h -> h

decodeRecord :: I.Header -> (GHC.Base.Maybe ((,) ((,) Hash Cipher) ByteString)) ->
                ByteString -> GHC.Base.Maybe I.Packet13
decodeRecord = Helper.decodeRecord

doHandshake_derive :: SigT ()
                      (SigT (Step_type Yield_effect Args_tls' Rets_tls' () Any)
                      (GHC.Base.Int -> CertificateChain -> PrivateKey -> Any))
doHandshake_derive =
  ExistT __ (ExistT
    (unsafeCoerce sum_merge
      (prod_curry
        (prod_curry
          (prod_curry (\_ n c p _ _ -> Prelude.Left ((,) (Prelude.Right
            (Prelude.Left ((,) ((,) ((,) () n) c) p))) (GHC.Base.Just (ExistT Yield
            (Prelude.Right ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
            ((Prelude.+) 1 ((Prelude.+) 1 0)))))))))))))
      (sum_merge
        (prod_curry
          (prod_curry
            (prod_curry (\_ n c p _ r -> Prelude.Left ((,)
              (case r of {
                Prelude.Left _ -> Prelude.Right (Prelude.Right (Prelude.Right
                 (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                 (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                 (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                 (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                 ()))))))))))))))))));
                Prelude.Right b -> Prelude.Right (Prelude.Right (Prelude.Left ((,)
                 ((,) ((,) ((,) () n) c) p) b)))})
              (case r of {
                Prelude.Left _ -> GHC.Base.Nothing;
                Prelude.Right b -> GHC.Base.Just (ExistT Yield (Prelude.Right
                 (hdReadLen (decodeHeader b))))}))))))
        (sum_merge
          (prod_curry
            (prod_curry
              (prod_curry
                (prod_curry (\_ n c p b _ r -> Prelude.Left ((,)
                  (case r of {
                    Prelude.Left _ -> Prelude.Right (Prelude.Right (Prelude.Right
                     (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                     (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                     (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                     (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                     ()))))))))))))))))));
                    Prelude.Right b0 ->
                     case decodeRecord (decodeHeader b) GHC.Base.Nothing b0 of {
                      GHC.Base.Just a ->
                       case clientHello a of {
                        GHC.Base.Just a0 ->
                         case chooseCipher (snd a0) serverCiphers of {
                          GHC.Base.Just a1 ->
                           case extension_KeyShare (snd (fst a0)) of {
                            GHC.Base.Just a2 ->
                             case findKeyShare a2 serverGroups of {
                              GHC.Base.Just a3 ->
                               case decodeGroupPublic (ksGroup a3) (ksData a3) of {
                                Prelude.Left _ -> Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right ()))))))))))))))))));
                                Prelude.Right b1 -> Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Left ((,) ((,) ((,) ((,)
                                 ((,) ((,) ((,) ((,) () n) c) p) b0) a0) a1) a3)
                                 b1))))};
                              GHC.Base.Nothing -> Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right ()))))))))))))))))))};
                            GHC.Base.Nothing -> Prelude.Right (Prelude.Right
                             (Prelude.Right (Prelude.Right (Prelude.Right
                             (Prelude.Right (Prelude.Right (Prelude.Right
                             (Prelude.Right (Prelude.Right (Prelude.Right
                             (Prelude.Right (Prelude.Right (Prelude.Right
                             (Prelude.Right (Prelude.Right (Prelude.Right
                             (Prelude.Right (Prelude.Right ()))))))))))))))))))};
                          GHC.Base.Nothing -> Prelude.Right (Prelude.Right
                           (Prelude.Right (Prelude.Right (Prelude.Right
                           (Prelude.Right (Prelude.Right (Prelude.Right
                           (Prelude.Right (Prelude.Right (Prelude.Right
                           (Prelude.Right (Prelude.Right (Prelude.Right
                           (Prelude.Right (Prelude.Right (Prelude.Right
                           (Prelude.Right (Prelude.Right ()))))))))))))))))))};
                        GHC.Base.Nothing -> Prelude.Right (Prelude.Right
                         (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                         (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                         (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                         (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                         (Prelude.Right ()))))))))))))))))))};
                      GHC.Base.Nothing -> Prelude.Right (Prelude.Right
                       (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                       (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                       (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                       (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                       (Prelude.Right ()))))))))))))))))))}})
                  (case r of {
                    Prelude.Left _ -> GHC.Base.Nothing;
                    Prelude.Right b0 ->
                     case decodeRecord (decodeHeader b) GHC.Base.Nothing b0 of {
                      GHC.Base.Just a ->
                       case clientHello a of {
                        GHC.Base.Just a0 ->
                         case chooseCipher (snd a0) serverCiphers of {
                          GHC.Base.Just _ ->
                           case extension_KeyShare (snd (fst a0)) of {
                            GHC.Base.Just a1 ->
                             case findKeyShare a1 serverGroups of {
                              GHC.Base.Just a2 ->
                               case decodeGroupPublic (ksGroup a2) (ksData a2) of {
                                Prelude.Left _ -> GHC.Base.Nothing;
                                Prelude.Right b1 -> GHC.Base.Just (ExistT Yield
                                 (Prelude.Left (Prelude.Left (Prelude.Right b1))))};
                              GHC.Base.Nothing -> GHC.Base.Nothing};
                            GHC.Base.Nothing -> GHC.Base.Nothing};
                          GHC.Base.Nothing -> GHC.Base.Nothing};
                        GHC.Base.Nothing -> GHC.Base.Nothing};
                      GHC.Base.Nothing -> GHC.Base.Nothing}})))))))
          (sum_merge
            (prod_curry
              (prod_curry
                (prod_curry
                  (prod_curry
                    (prod_curry
                      (prod_curry
                        (prod_curry
                          (prod_curry (\_ n c p b p0 c0 k _ _ r -> Prelude.Left ((,)
                            (case r of {
                              Prelude.Left a ->
                               case a of {
                                Prelude.Left a0 ->
                                 case a0 of {
                                  GHC.Base.Just a1 -> Prelude.Right (Prelude.Right
                                   (Prelude.Right (Prelude.Right (Prelude.Left ((,)
                                   ((,) ((,) ((,) ((,) ((,) ((,) ((,) () n) c) p) b)
                                   p0) c0) k) a1)))));
                                  GHC.Base.Nothing -> Prelude.Right (Prelude.Right
                                   (Prelude.Right (Prelude.Right (Prelude.Right
                                   (Prelude.Right (Prelude.Right (Prelude.Right
                                   (Prelude.Right (Prelude.Right (Prelude.Right
                                   (Prelude.Right (Prelude.Right (Prelude.Right
                                   (Prelude.Right (Prelude.Right (Prelude.Right
                                   (Prelude.Right (Prelude.Right
                                   ()))))))))))))))))))};
                                Prelude.Right _ -> Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right ()))))))))))))))))))};
                              Prelude.Right _ -> Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right ()))))))))))))))))))})
                            (case r of {
                              Prelude.Left a ->
                               case a of {
                                Prelude.Left a0 ->
                                 case a0 of {
                                  GHC.Base.Just _ -> GHC.Base.Just (ExistT Yield
                                   (Prelude.Left (Prelude.Left (Prelude.Left
                                   (Prelude.Left ((Prelude.+) 1 ((Prelude.+) 1
                                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                                   0)))))))))))))))))))))))))))))))))))));
                                  GHC.Base.Nothing -> GHC.Base.Nothing};
                                Prelude.Right _ -> GHC.Base.Nothing};
                              Prelude.Right _ -> GHC.Base.Nothing})))))))))))
            (sum_merge
              (prod_curry
                (prod_curry
                  (prod_curry
                    (prod_curry
                      (prod_curry
                        (prod_curry
                          (prod_curry
                            (prod_curry (\_ n c p b p0 c0 k p1 _ r -> Prelude.Left
                              ((,)
                              (case r of {
                                Prelude.Left _ -> Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right ()))))))))))))))))));
                                Prelude.Right b0 -> Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Left ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                 ((,) ((,) () n) c) p) b) p0) c0) k) p1) b0))))))})
                              (case r of {
                                Prelude.Left _ -> GHC.Base.Nothing;
                                Prelude.Right b0 -> GHC.Base.Just (ExistT Yield
                                 (Prelude.Left (Prelude.Left (Prelude.Left
                                 (Prelude.Right ((,) (I.Handshake13 ((:)
                                 (I.ServerHello13 (I.ServerRandom b0)
                                 (snd (fst (fst p0))) (cipherID c0) ((:)
                                 (extensionRaw_KeyShare
                                   (extensionEncode_KeyShare (I.KeyShareEntry
                                     (ksGroup k) (encodeGroupPublic (fst p1)))))
                                 ((:)
                                 (extensionRaw_SupportedVersions
                                   (extensionEncode_SupportedVersions tLS13)) [])))
                                 [])) GHC.Base.Nothing))))))})))))))))))
              (sum_merge
                (prod_curry
                  (prod_curry
                    (prod_curry
                      (prod_curry
                        (prod_curry
                          (prod_curry
                            (prod_curry
                              (prod_curry
                                (prod_curry (\_ n c p b p0 c0 _ p1 _ _ r ->
                                  Prelude.Left ((,)
                                  (case r of {
                                    Prelude.Left _ -> Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Right
                                     ()))))))))))))))))));
                                    Prelude.Right b0 -> Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Left ((,) ((,) ((,)
                                     ((,) ((,) ((,) ((,) ((,) () n) c) p) b) p0) c0)
                                     p1) b0)))))))})
                                  (case r of {
                                    Prelude.Left _ -> GHC.Base.Nothing;
                                    Prelude.Right _ -> GHC.Base.Just (ExistT Yield
                                     (Prelude.Left (Prelude.Left (Prelude.Left
                                     (Prelude.Right ((,) I.ChangeCipherSpec13
                                     GHC.Base.Nothing))))))}))))))))))))
                (sum_merge
                  (prod_curry
                    (prod_curry
                      (prod_curry
                        (prod_curry
                          (prod_curry
                            (prod_curry
                              (prod_curry
                                (prod_curry (\_ n c p b p0 c0 p1 b0 _ r ->
                                  Prelude.Left ((,)
                                  (case r of {
                                    Prelude.Left _ -> Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Right
                                     ()))))))))))))))))));
                                    Prelude.Right _ -> Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Right (Prelude.Right
                                     (Prelude.Right (Prelude.Right (Prelude.Left
                                     ((,) ((,) ((,) ((,) ((,) ((,) ((,) ((,) () n)
                                     c) p) b) p0) c0) p1) b0))))))))})
                                  (case r of {
                                    Prelude.Left _ -> GHC.Base.Nothing;
                                    Prelude.Right _ -> GHC.Base.Just (ExistT Yield
                                     (Prelude.Left (Prelude.Left (Prelude.Left
                                     (Prelude.Right ((,) (I.Handshake13 ((:)
                                     (I.EncryptedExtensions13 []) []))
                                     (GHC.Base.Just ((,) ((,) ((,) (cipherHash c0)
                                     c0)
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
                                         (ba_convert (snd p1)))
                                       (s2b ((:) 's' ((:) ' ' ((:) 'h' ((:) 's' ((:)
                                         ' ' ((:) 't' ((:) 'r' ((:) 'a' ((:) 'f'
                                         ((:) 'f' ((:) 'i' ((:) 'c'
                                         ([]))))))))))))))
                                       (hashWith (cipherHash c0) ((:) b ((:) b0
                                         []))) (hashDigestSize (cipherHash c0))))
                                     0))))))))})))))))))))
                  (sum_merge
                    (prod_curry
                      (prod_curry
                        (prod_curry
                          (prod_curry
                            (prod_curry
                              (prod_curry
                                (prod_curry
                                  (prod_curry (\_ n c p b p0 c0 p1 b0 _ r ->
                                    Prelude.Left ((,)
                                    (case r of {
                                      Prelude.Left _ -> Prelude.Right (Prelude.Right
                                       (Prelude.Right (Prelude.Right (Prelude.Right
                                       (Prelude.Right (Prelude.Right (Prelude.Right
                                       (Prelude.Right (Prelude.Right (Prelude.Right
                                       (Prelude.Right (Prelude.Right (Prelude.Right
                                       (Prelude.Right (Prelude.Right (Prelude.Right
                                       (Prelude.Right (Prelude.Right
                                       ()))))))))))))))))));
                                      Prelude.Right b1 ->
                                       case decideCredInfo p (getCertificates c)
                                              (extension_SignatureAlgorithms
                                                (snd (fst p0))) of {
                                        GHC.Base.Just a -> Prelude.Right
                                         (Prelude.Right (Prelude.Right
                                         (Prelude.Right (Prelude.Right
                                         (Prelude.Right (Prelude.Right
                                         (Prelude.Right (Prelude.Left ((,) ((,) ((,)
                                         ((,) ((,) ((,) ((,) ((,) ((,) () n) c) p)
                                         b) c0) p1) b0) b1) a)))))))));
                                        GHC.Base.Nothing -> Prelude.Right
                                         (Prelude.Right (Prelude.Right
                                         (Prelude.Right (Prelude.Right
                                         (Prelude.Right (Prelude.Right
                                         (Prelude.Right (Prelude.Right
                                         (Prelude.Right (Prelude.Right
                                         (Prelude.Right (Prelude.Right
                                         (Prelude.Right (Prelude.Right
                                         (Prelude.Right (Prelude.Right
                                         (Prelude.Right (Prelude.Right
                                         ()))))))))))))))))))}})
                                    (case r of {
                                      Prelude.Left _ -> GHC.Base.Nothing;
                                      Prelude.Right _ ->
                                       case decideCredInfo p (getCertificates c)
                                              (extension_SignatureAlgorithms
                                                (snd (fst p0))) of {
                                        GHC.Base.Just _ -> GHC.Base.Just (ExistT
                                         Yield (Prelude.Left (Prelude.Left
                                         (Prelude.Left (Prelude.Right ((,)
                                         (I.Handshake13 ((:) (I.Certificate13 empty
                                         c ((:) [] [])) [])) (GHC.Base.Just ((,)
                                         ((,) ((,) (cipherHash c0) c0)
                                         (hkdfExpandLabel (cipherHash c0)
                                           (hkdfExtract (cipherHash c0)
                                             (hkdfExpandLabel (cipherHash c0)
                                               (hkdfExtract (cipherHash c0)
                                                 (b_replicate
                                                   (hashDigestSize (cipherHash c0))
                                                   w0)
                                                 (b_replicate
                                                   (hashDigestSize (cipherHash c0))
                                                   w0))
                                               (s2b ((:) 'd' ((:) 'e' ((:) 'r' ((:)
                                                 'i' ((:) 'v' ((:) 'e' ((:) 'd'
                                                 ([])))))))))
                                               (hashWith (cipherHash c0) ((:)
                                                 (s2b ([])) []))
                                               (hashDigestSize (cipherHash c0)))
                                             (ba_convert (snd p1)))
                                           (s2b ((:) 's' ((:) ' ' ((:) 'h' ((:) 's'
                                             ((:) ' ' ((:) 't' ((:) 'r' ((:) 'a'
                                             ((:) 'f' ((:) 'f' ((:) 'i' ((:) 'c'
                                             ([]))))))))))))))
                                           (hashWith (cipherHash c0) ((:) b ((:) b0
                                             []))) (hashDigestSize (cipherHash c0))))
                                         ((Prelude.+) 1 0)))))))));
                                        GHC.Base.Nothing -> GHC.Base.Nothing}})))))))))))
                    (sum_merge
                      (prod_curry
                        (prod_curry
                          (prod_curry
                            (prod_curry
                              (prod_curry
                                (prod_curry
                                  (prod_curry
                                    (prod_curry
                                      (prod_curry (\_ n _ p b c p0 b0 b1 p1 _ r ->
                                        Prelude.Left ((,)
                                        (case r of {
                                          Prelude.Left _ -> Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           ()))))))))))))))))));
                                          Prelude.Right b2 -> Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Left ((,) ((,) ((,) ((,) ((,)
                                           ((,) ((,) ((,) ((,) () n) p) b) c) p0)
                                           b0) b1) p1) b2))))))))))})
                                        (case r of {
                                          Prelude.Left _ -> GHC.Base.Nothing;
                                          Prelude.Right b2 -> GHC.Base.Just (ExistT
                                           Yield (Prelude.Left (Prelude.Right ((,)
                                           ((,) ((,) (fst p1) p) (snd p1))
                                           (hashWith (cipherHash c) ((:) b ((:) b0
                                             ((:) b1 ((:) b2 [])))))))))}))))))))))))
                      (sum_merge
                        (prod_curry
                          (prod_curry
                            (prod_curry
                              (prod_curry
                                (prod_curry
                                  (prod_curry
                                    (prod_curry
                                      (prod_curry
                                        (prod_curry (\_ n _ b c p b0 b1 _ b2 _ r ->
                                          Prelude.Left ((,)
                                          (case r of {
                                            Prelude.Left a ->
                                             case a of {
                                              Prelude.Left _ -> Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               ()))))))))))))))))));
                                              Prelude.Right b3 -> Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Left ((,)
                                               ((,) ((,) ((,) ((,) ((,) ((,) ((,) ()
                                               n) b) c) p) b0) b1) b2) b3)))))))))))};
                                            Prelude.Right _ -> Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             ()))))))))))))))))))})
                                          (case r of {
                                            Prelude.Left a ->
                                             case a of {
                                              Prelude.Left _ -> GHC.Base.Nothing;
                                              Prelude.Right b3 -> GHC.Base.Just
                                               (ExistT Yield (Prelude.Left
                                               (Prelude.Left (Prelude.Left
                                               (Prelude.Right ((,) (I.Handshake13
                                               ((:) b3 [])) (GHC.Base.Just ((,) ((,)
                                               ((,) (cipherHash c) c)
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
                                                 (s2b ((:) 's' ((:) ' ' ((:) 'h'
                                                   ((:) 's' ((:) ' ' ((:) 't' ((:)
                                                   'r' ((:) 'a' ((:) 'f' ((:) 'f'
                                                   ((:) 'i' ((:) 'c'
                                                   ([]))))))))))))))
                                                 (hashWith (cipherHash c) ((:) b
                                                   ((:) b0 [])))
                                                 (hashDigestSize (cipherHash c))))
                                               ((Prelude.+) 1 ((Prelude.+) 1
                                               0))))))))))};
                                            Prelude.Right _ -> GHC.Base.Nothing}))))))))))))
                        (sum_merge
                          (prod_curry
                            (prod_curry
                              (prod_curry
                                (prod_curry
                                  (prod_curry
                                    (prod_curry
                                      (prod_curry
                                        (prod_curry (\_ n b c p b0 b1 b2 _ _ r ->
                                          Prelude.Left ((,)
                                          (case r of {
                                            Prelude.Left _ -> Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             ()))))))))))))))))));
                                            Prelude.Right b3 -> Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Right (Prelude.Right
                                             (Prelude.Left ((,) ((,) ((,) ((,) ((,)
                                             ((,) ((,) ((,) () n) b) c) p) b0) b1)
                                             b2) b3))))))))))))})
                                          (case r of {
                                            Prelude.Left _ -> GHC.Base.Nothing;
                                            Prelude.Right b3 -> GHC.Base.Just
                                             (ExistT Yield (Prelude.Left
                                             (Prelude.Left (Prelude.Left
                                             (Prelude.Right ((,) (I.Handshake13 ((:)
                                             (I.Finished13
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
                                                 (s2b ((:) 's' ((:) ' ' ((:) 'h'
                                                   ((:) 's' ((:) ' ' ((:) 't' ((:)
                                                   'r' ((:) 'a' ((:) 'f' ((:) 'f'
                                                   ((:) 'i' ((:) 'c'
                                                   ([]))))))))))))))
                                                 (hashWith (cipherHash c) ((:) b
                                                   ((:) b0 [])))
                                                 (hashDigestSize (cipherHash c)))
                                               (hashWith (cipherHash c) ((:) b ((:)
                                                 b0 ((:) b1 ((:) b2 ((:) b3 []))))))))
                                             [])) (GHC.Base.Just ((,) ((,) ((,)
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
                                                     ((:) 'i' ((:) 'v' ((:) 'e' ((:)
                                                     'd' ([])))))))))
                                                   (hashWith (cipherHash c) ((:)
                                                     (s2b ([])) []))
                                                   (hashDigestSize (cipherHash c)))
                                                 (ba_convert (snd p)))
                                               (s2b ((:) 's' ((:) ' ' ((:) 'h' ((:)
                                                 's' ((:) ' ' ((:) 't' ((:) 'r' ((:)
                                                 'a' ((:) 'f' ((:) 'f' ((:) 'i' ((:)
                                                 'c' ([]))))))))))))))
                                               (hashWith (cipherHash c) ((:) b ((:)
                                                 b0 [])))
                                               (hashDigestSize (cipherHash c))))
                                             ((Prelude.+) 1 ((Prelude.+) 1
                                             ((Prelude.+) 1 0)))))))))))})))))))))))
                          (sum_merge
                            (prod_curry
                              (prod_curry
                                (prod_curry
                                  (prod_curry
                                    (prod_curry
                                      (prod_curry
                                        (prod_curry
                                          (prod_curry (\_ n b c p b0 b1 b2 b3 _ r ->
                                            Prelude.Left ((,)
                                            (case r of {
                                              Prelude.Left _ -> Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               ()))))))))))))))))));
                                              Prelude.Right b4 -> Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Left ((,)
                                               ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                               ((,) () n) b) c) p) b0) b1) b2) b3)
                                               b4)))))))))))))})
                                            (case r of {
                                              Prelude.Left _ -> GHC.Base.Nothing;
                                              Prelude.Right _ -> GHC.Base.Just
                                               (ExistT Yield (Prelude.Right
                                               ((Prelude.+) 1 ((Prelude.+) 1
                                               ((Prelude.+) 1 ((Prelude.+) 1
                                               ((Prelude.+) 1 0)))))))})))))))))))
                            (sum_merge
                              (prod_curry
                                (prod_curry
                                  (prod_curry
                                    (prod_curry
                                      (prod_curry
                                        (prod_curry
                                          (prod_curry
                                            (prod_curry
                                              (prod_curry
                                                (\_ n b c p b0 b1 b2 b3 b4 _ r ->
                                                Prelude.Left ((,)
                                                (case r of {
                                                  Prelude.Left _ -> Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   ()))))))))))))))))));
                                                  Prelude.Right b5 -> Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Left ((,) ((,) ((,) ((,)
                                                   ((,) ((,) ((,) ((,) ((,) ((,) ()
                                                   n) b) c) p) b0) b1) b2) b3) b4)
                                                   b5))))))))))))))})
                                                (case r of {
                                                  Prelude.Left _ -> GHC.Base.Nothing;
                                                  Prelude.Right b5 -> GHC.Base.Just
                                                   (ExistT Yield (Prelude.Right
                                                   (hdReadLen (decodeHeader b5))))}))))))))))))
                              (sum_merge
                                (prod_curry
                                  (prod_curry
                                    (prod_curry
                                      (prod_curry
                                        (prod_curry
                                          (prod_curry
                                            (prod_curry
                                              (prod_curry
                                                (prod_curry
                                                  (prod_curry
                                                    (\_ n b c p b0 b1 b2 b3 b4 b5 _ r ->
                                                    Prelude.Left ((,)
                                                    (case r of {
                                                      Prelude.Left _ ->
                                                       Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right
                                                       ()))))))))))))))))));
                                                      Prelude.Right b6 ->
                                                       case decodeRecord
                                                              (decodeHeader b5)
                                                              GHC.Base.Nothing b6 of {
                                                        GHC.Base.Just a ->
                                                         case changeCipherSpec a of {
                                                          GHC.Base.Just _ ->
                                                           Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Left ((,) ((,)
                                                           ((,) ((,) ((,) ((,) ((,)
                                                           ((,) ((,) () n) b) c) p)
                                                           b0) b1) b2) b3)
                                                           b4)))))))))))))));
                                                          GHC.Base.Nothing ->
                                                           Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           ()))))))))))))))))))};
                                                        GHC.Base.Nothing ->
                                                         Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         ()))))))))))))))))))}})
                                                    (case r of {
                                                      Prelude.Left _ ->
                                                       GHC.Base.Nothing;
                                                      Prelude.Right b6 ->
                                                       case decodeRecord
                                                              (decodeHeader b5)
                                                              GHC.Base.Nothing b6 of {
                                                        GHC.Base.Just a ->
                                                         case changeCipherSpec a of {
                                                          GHC.Base.Just _ ->
                                                           GHC.Base.Just (ExistT
                                                           Yield (Prelude.Right
                                                           ((Prelude.+) 1
                                                           ((Prelude.+) 1
                                                           ((Prelude.+) 1
                                                           ((Prelude.+) 1
                                                           ((Prelude.+) 1 0)))))));
                                                          GHC.Base.Nothing ->
                                                           GHC.Base.Nothing};
                                                        GHC.Base.Nothing ->
                                                         GHC.Base.Nothing}})))))))))))))
                                (sum_merge
                                  (prod_curry
                                    (prod_curry
                                      (prod_curry
                                        (prod_curry
                                          (prod_curry
                                            (prod_curry
                                              (prod_curry
                                                (prod_curry
                                                  (prod_curry
                                                    (\_ n b c p b0 b1 b2 b3 b4 _ r ->
                                                    Prelude.Left ((,)
                                                    (case r of {
                                                      Prelude.Left _ ->
                                                       Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right
                                                       ()))))))))))))))))));
                                                      Prelude.Right b5 ->
                                                       Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Left
                                                       ((,) ((,) ((,) ((,) ((,) ((,)
                                                       ((,) ((,) ((,) ((,) () n) b)
                                                       c) p) b0) b1) b2) b3) b4)
                                                       b5))))))))))))))))})
                                                    (case r of {
                                                      Prelude.Left _ ->
                                                       GHC.Base.Nothing;
                                                      Prelude.Right b5 ->
                                                       GHC.Base.Just (ExistT Yield
                                                       (Prelude.Right
                                                       (hdReadLen (decodeHeader b5))))}))))))))))))
                                  (sum_merge
                                    (prod_curry
                                      (prod_curry
                                        (prod_curry
                                          (prod_curry
                                            (prod_curry
                                              (prod_curry
                                                (prod_curry
                                                  (prod_curry
                                                    (prod_curry
                                                      (prod_curry
                                                        (\_ n b c p b0 b1 b2 b3 b4 b5 _ r ->
                                                        Prelude.Left ((,)
                                                        (case r of {
                                                          Prelude.Left _ ->
                                                           Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           ()))))))))))))))))));
                                                          Prelude.Right b6 ->
                                                           case decodeRecord
                                                                  (decodeHeader b5)
                                                                  (GHC.Base.Just
                                                                  ((,) ((,)
                                                                  (cipherHash c) c)
                                                                  (hkdfExpandLabel
                                                                    (cipherHash c)
                                                                    (hkdfExtract
                                                                      (cipherHash c)
                                                                      (hkdfExpandLabel
                                                                        (cipherHash
                                                                          c)
                                                                        (hkdfExtract
                                                                          (cipherHash
                                                                           c)
                                                                          (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0)
                                                                          (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0))
                                                                        (s2b ((:)
                                                                          'd' ((:)
                                                                          'e' ((:)
                                                                          'r' ((:)
                                                                          'i' ((:)
                                                                          'v' ((:)
                                                                          'e' ((:)
                                                                          'd'
                                                                          ([])))))))))
                                                                        (hashWith
                                                                          (cipherHash
                                                                           c) ((:)
                                                                          (s2b ([]))
                                                                          []))
                                                                        (hashDigestSize
                                                                          (cipherHash
                                                                           c)))
                                                                      (ba_convert
                                                                        (snd p)))
                                                                    (s2b ((:) 'c'
                                                                      ((:) ' ' ((:)
                                                                      'h' ((:) 's'
                                                                      ((:) ' ' ((:)
                                                                      't' ((:) 'r'
                                                                      ((:) 'a' ((:)
                                                                      'f' ((:) 'f'
                                                                      ((:) 'i' ((:)
                                                                      'c'
                                                                      ([]))))))))))))))
                                                                    (hashWith
                                                                      (cipherHash c)
                                                                      ((:) b ((:) b0
                                                                      [])))
                                                                    (hashDigestSize
                                                                      (cipherHash c)))))
                                                                  b6 of {
                                                            GHC.Base.Just a ->
                                                             case handshake a of {
                                                              GHC.Base.Just a0 ->
                                                               case finished a0 of {
                                                                GHC.Base.Just a1 ->
                                                                 case byteString_beq
                                                                        a1
                                                                        (makeVerifyData
                                                                          (cipherHash
                                                                           c)
                                                                          (hkdfExpandLabel
                                                                           (cipherHash
                                                                           c)
                                                                           (hkdfExtract
                                                                           (cipherHash
                                                                           c)
                                                                           (hkdfExpandLabel
                                                                           (cipherHash
                                                                           c)
                                                                           (hkdfExtract
                                                                           (cipherHash
                                                                           c)
                                                                           (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0)
                                                                           (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0))
                                                                           (s2b ((:)
                                                                           'd' ((:)
                                                                           'e' ((:)
                                                                           'r' ((:)
                                                                           'i' ((:)
                                                                           'v' ((:)
                                                                           'e' ((:)
                                                                           'd'
                                                                           ([])))))))))
                                                                           (hashWith
                                                                           (cipherHash
                                                                           c) ((:)
                                                                           (s2b
                                                                           ([]))
                                                                           []))
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)))
                                                                           (ba_convert
                                                                           (snd p)))
                                                                           (s2b ((:)
                                                                           'c' ((:)
                                                                           ' ' ((:)
                                                                           'h' ((:)
                                                                           's' ((:)
                                                                           ' ' ((:)
                                                                           't' ((:)
                                                                           'r' ((:)
                                                                           'a' ((:)
                                                                           'f' ((:)
                                                                           'f' ((:)
                                                                           'i' ((:)
                                                                           'c'
                                                                           ([]))))))))))))))
                                                                           (hashWith
                                                                           (cipherHash
                                                                           c) ((:) b
                                                                           ((:) b0
                                                                           [])))
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)))
                                                                          (hashWith
                                                                           (cipherHash
                                                                           c) ((:) b
                                                                           ((:) b0
                                                                           ((:) b1
                                                                           ((:) b2
                                                                           ((:) b3
                                                                           ((:) b4
                                                                           [])))))))) of {
                                                                  GHC.Base.True ->
                                                                   (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                                     (\_ ->
                                                                     Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     ())))))))))))))))))))
                                                                     (\n0 ->
                                                                     Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Left
                                                                     ((,) ((,) ((,)
                                                                     ((,) ((,) ((,)
                                                                     ((,) ((,) ((,)
                                                                     () b) c) p) b0)
                                                                     b1) b2) b3) b4)
                                                                     n0))))))))))))))))))
                                                                     n;
                                                                  GHC.Base.False ->
                                                                   Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   ()))))))))))))))))))};
                                                                GHC.Base.Nothing ->
                                                                 Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 ()))))))))))))))))))};
                                                              GHC.Base.Nothing ->
                                                               Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               ()))))))))))))))))))};
                                                            GHC.Base.Nothing ->
                                                             Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             (Prelude.Right
                                                             ()))))))))))))))))))}})
                                                        (case r of {
                                                          Prelude.Left _ ->
                                                           GHC.Base.Nothing;
                                                          Prelude.Right b6 ->
                                                           case decodeRecord
                                                                  (decodeHeader b5)
                                                                  (GHC.Base.Just
                                                                  ((,) ((,)
                                                                  (cipherHash c) c)
                                                                  (hkdfExpandLabel
                                                                    (cipherHash c)
                                                                    (hkdfExtract
                                                                      (cipherHash c)
                                                                      (hkdfExpandLabel
                                                                        (cipherHash
                                                                          c)
                                                                        (hkdfExtract
                                                                          (cipherHash
                                                                           c)
                                                                          (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0)
                                                                          (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0))
                                                                        (s2b ((:)
                                                                          'd' ((:)
                                                                          'e' ((:)
                                                                          'r' ((:)
                                                                          'i' ((:)
                                                                          'v' ((:)
                                                                          'e' ((:)
                                                                          'd'
                                                                          ([])))))))))
                                                                        (hashWith
                                                                          (cipherHash
                                                                           c) ((:)
                                                                          (s2b ([]))
                                                                          []))
                                                                        (hashDigestSize
                                                                          (cipherHash
                                                                           c)))
                                                                      (ba_convert
                                                                        (snd p)))
                                                                    (s2b ((:) 'c'
                                                                      ((:) ' ' ((:)
                                                                      'h' ((:) 's'
                                                                      ((:) ' ' ((:)
                                                                      't' ((:) 'r'
                                                                      ((:) 'a' ((:)
                                                                      'f' ((:) 'f'
                                                                      ((:) 'i' ((:)
                                                                      'c'
                                                                      ([]))))))))))))))
                                                                    (hashWith
                                                                      (cipherHash c)
                                                                      ((:) b ((:) b0
                                                                      [])))
                                                                    (hashDigestSize
                                                                      (cipherHash c)))))
                                                                  b6 of {
                                                            GHC.Base.Just a ->
                                                             case handshake a of {
                                                              GHC.Base.Just a0 ->
                                                               case finished a0 of {
                                                                GHC.Base.Just a1 ->
                                                                 case byteString_beq
                                                                        a1
                                                                        (makeVerifyData
                                                                          (cipherHash
                                                                           c)
                                                                          (hkdfExpandLabel
                                                                           (cipherHash
                                                                           c)
                                                                           (hkdfExtract
                                                                           (cipherHash
                                                                           c)
                                                                           (hkdfExpandLabel
                                                                           (cipherHash
                                                                           c)
                                                                           (hkdfExtract
                                                                           (cipherHash
                                                                           c)
                                                                           (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0)
                                                                           (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0))
                                                                           (s2b ((:)
                                                                           'd' ((:)
                                                                           'e' ((:)
                                                                           'r' ((:)
                                                                           'i' ((:)
                                                                           'v' ((:)
                                                                           'e' ((:)
                                                                           'd'
                                                                           ([])))))))))
                                                                           (hashWith
                                                                           (cipherHash
                                                                           c) ((:)
                                                                           (s2b
                                                                           ([]))
                                                                           []))
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)))
                                                                           (ba_convert
                                                                           (snd p)))
                                                                           (s2b ((:)
                                                                           'c' ((:)
                                                                           ' ' ((:)
                                                                           'h' ((:)
                                                                           's' ((:)
                                                                           ' ' ((:)
                                                                           't' ((:)
                                                                           'r' ((:)
                                                                           'a' ((:)
                                                                           'f' ((:)
                                                                           'f' ((:)
                                                                           'i' ((:)
                                                                           'c'
                                                                           ([]))))))))))))))
                                                                           (hashWith
                                                                           (cipherHash
                                                                           c) ((:) b
                                                                           ((:) b0
                                                                           [])))
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)))
                                                                          (hashWith
                                                                           (cipherHash
                                                                           c) ((:) b
                                                                           ((:) b0
                                                                           ((:) b1
                                                                           ((:) b2
                                                                           ((:) b3
                                                                           ((:) b4
                                                                           [])))))))) of {
                                                                  GHC.Base.True ->
                                                                   (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                                     (\_ ->
                                                                     GHC.Base.Nothing)
                                                                     (\_ ->
                                                                     GHC.Base.Just
                                                                     (ExistT Yield
                                                                     (Prelude.Right
                                                                     ((Prelude.+) 1
                                                                     ((Prelude.+) 1
                                                                     ((Prelude.+) 1
                                                                     ((Prelude.+) 1
                                                                     ((Prelude.+) 1
                                                                     0))))))))
                                                                     n;
                                                                  GHC.Base.False ->
                                                                   GHC.Base.Nothing};
                                                                GHC.Base.Nothing ->
                                                                 GHC.Base.Nothing};
                                                              GHC.Base.Nothing ->
                                                               GHC.Base.Nothing};
                                                            GHC.Base.Nothing ->
                                                             GHC.Base.Nothing}})))))))))))))
                                    (sum_merge
                                      (prod_curry
                                        (prod_curry
                                          (prod_curry
                                            (prod_curry
                                              (prod_curry
                                                (prod_curry
                                                  (prod_curry
                                                    (prod_curry
                                                      (prod_curry
                                                        (\_ b c p b0 b1 b2 b3 b4 n _ r ->
                                                        Prelude.Left ((,)
                                                        (case r of {
                                                          Prelude.Left _ ->
                                                           Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           ()))))))))))))))))));
                                                          Prelude.Right b5 ->
                                                           Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Right
                                                           (Prelude.Left ((,) ((,)
                                                           ((,) ((,) ((,) ((,) ((,)
                                                           ((,) ((,) ((,) () b) c)
                                                           p) b0) b1) b2) b3) b4) n)
                                                           b5))))))))))))))))))})
                                                        (case r of {
                                                          Prelude.Left _ ->
                                                           GHC.Base.Nothing;
                                                          Prelude.Right b5 ->
                                                           GHC.Base.Just (ExistT
                                                           Yield (Prelude.Right
                                                           (hdReadLen
                                                             (decodeHeader b5))))}))))))))))))
                                      (sum_merge
                                        (prod_curry
                                          (prod_curry
                                            (prod_curry
                                              (prod_curry
                                                (prod_curry
                                                  (prod_curry
                                                    (prod_curry
                                                      (prod_curry
                                                        (prod_curry
                                                          (prod_curry
                                                            (\_ b c p b0 b1 b2 b3 b4 n b5 _ r ->
                                                            Prelude.Left ((,)
                                                            (case r of {
                                                              Prelude.Left _ ->
                                                               Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               (Prelude.Right
                                                               ()))))))))))))))))));
                                                              Prelude.Right b6 ->
                                                               case decodeRecord
                                                                      (decodeHeader
                                                                        b5)
                                                                      (GHC.Base.Just
                                                                      ((,) ((,)
                                                                      (cipherHash c)
                                                                      c)
                                                                      (hkdfExpandLabel
                                                                        (cipherHash
                                                                          c)
                                                                        (hkdfExtract
                                                                          (cipherHash
                                                                           c)
                                                                          (hkdfExpandLabel
                                                                           (cipherHash
                                                                           c)
                                                                           (hkdfExtract
                                                                           (cipherHash
                                                                           c)
                                                                           (hkdfExpandLabel
                                                                           (cipherHash
                                                                           c)
                                                                           (hkdfExtract
                                                                           (cipherHash
                                                                           c)
                                                                           (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0)
                                                                           (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0))
                                                                           (s2b ((:)
                                                                           'd' ((:)
                                                                           'e' ((:)
                                                                           'r' ((:)
                                                                           'i' ((:)
                                                                           'v' ((:)
                                                                           'e' ((:)
                                                                           'd'
                                                                           ([])))))))))
                                                                           (hashWith
                                                                           (cipherHash
                                                                           c) ((:)
                                                                           (s2b
                                                                           ([]))
                                                                           []))
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)))
                                                                           (ba_convert
                                                                           (snd p)))
                                                                           (s2b ((:)
                                                                           'd' ((:)
                                                                           'e' ((:)
                                                                           'r' ((:)
                                                                           'i' ((:)
                                                                           'v' ((:)
                                                                           'e' ((:)
                                                                           'd'
                                                                           ([])))))))))
                                                                           (hashWith
                                                                           (cipherHash
                                                                           c) ((:)
                                                                           (s2b
                                                                           ([]))
                                                                           []))
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)))
                                                                          (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0))
                                                                        (s2b ((:)
                                                                          'c' ((:)
                                                                          ' ' ((:)
                                                                          'a' ((:)
                                                                          'p' ((:)
                                                                          ' ' ((:)
                                                                          't' ((:)
                                                                          'r' ((:)
                                                                          'a' ((:)
                                                                          'f' ((:)
                                                                          'f' ((:)
                                                                          'i' ((:)
                                                                          'c'
                                                                          ([]))))))))))))))
                                                                        (hashWith
                                                                          (cipherHash
                                                                           c) ((:) b
                                                                          ((:) b0
                                                                          ((:) b1
                                                                          ((:) b2
                                                                          ((:) b3
                                                                          ((:) b4
                                                                          [])))))))
                                                                        (hashDigestSize
                                                                          (cipherHash
                                                                           c))))) b6 of {
                                                                GHC.Base.Just a ->
                                                                 case appData a of {
                                                                  GHC.Base.Just a0 ->
                                                                   Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Left
                                                                   ((,) ((,) ((,)
                                                                   ((,) ((,) ((,)
                                                                   ((,) ((,) ((,)
                                                                   ((,) () b) c) p)
                                                                   b0) b1) b2) b3)
                                                                   b4) n)
                                                                   a0)))))))))))))))))));
                                                                  GHC.Base.Nothing ->
                                                                   Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   ()))))))))))))))))))};
                                                                GHC.Base.Nothing ->
                                                                 Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 ()))))))))))))))))))}})
                                                            (case r of {
                                                              Prelude.Left _ ->
                                                               GHC.Base.Nothing;
                                                              Prelude.Right b6 ->
                                                               case decodeRecord
                                                                      (decodeHeader
                                                                        b5)
                                                                      (GHC.Base.Just
                                                                      ((,) ((,)
                                                                      (cipherHash c)
                                                                      c)
                                                                      (hkdfExpandLabel
                                                                        (cipherHash
                                                                          c)
                                                                        (hkdfExtract
                                                                          (cipherHash
                                                                           c)
                                                                          (hkdfExpandLabel
                                                                           (cipherHash
                                                                           c)
                                                                           (hkdfExtract
                                                                           (cipherHash
                                                                           c)
                                                                           (hkdfExpandLabel
                                                                           (cipherHash
                                                                           c)
                                                                           (hkdfExtract
                                                                           (cipherHash
                                                                           c)
                                                                           (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0)
                                                                           (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0))
                                                                           (s2b ((:)
                                                                           'd' ((:)
                                                                           'e' ((:)
                                                                           'r' ((:)
                                                                           'i' ((:)
                                                                           'v' ((:)
                                                                           'e' ((:)
                                                                           'd'
                                                                           ([])))))))))
                                                                           (hashWith
                                                                           (cipherHash
                                                                           c) ((:)
                                                                           (s2b
                                                                           ([]))
                                                                           []))
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)))
                                                                           (ba_convert
                                                                           (snd p)))
                                                                           (s2b ((:)
                                                                           'd' ((:)
                                                                           'e' ((:)
                                                                           'r' ((:)
                                                                           'i' ((:)
                                                                           'v' ((:)
                                                                           'e' ((:)
                                                                           'd'
                                                                           ([])))))))))
                                                                           (hashWith
                                                                           (cipherHash
                                                                           c) ((:)
                                                                           (s2b
                                                                           ([]))
                                                                           []))
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)))
                                                                          (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0))
                                                                        (s2b ((:)
                                                                          'c' ((:)
                                                                          ' ' ((:)
                                                                          'a' ((:)
                                                                          'p' ((:)
                                                                          ' ' ((:)
                                                                          't' ((:)
                                                                          'r' ((:)
                                                                          'a' ((:)
                                                                          'f' ((:)
                                                                          'f' ((:)
                                                                          'i' ((:)
                                                                          'c'
                                                                          ([]))))))))))))))
                                                                        (hashWith
                                                                          (cipherHash
                                                                           c) ((:) b
                                                                          ((:) b0
                                                                          ((:) b1
                                                                          ((:) b2
                                                                          ((:) b3
                                                                          ((:) b4
                                                                          [])))))))
                                                                        (hashDigestSize
                                                                          (cipherHash
                                                                           c))))) b6 of {
                                                                GHC.Base.Just a ->
                                                                 case appData a of {
                                                                  GHC.Base.Just a0 ->
                                                                   GHC.Base.Just
                                                                   (ExistT Yield
                                                                   (Prelude.Left
                                                                   (Prelude.Left
                                                                   (Prelude.Left
                                                                   (Prelude.Right
                                                                   ((,) (I.AppData13
                                                                   (mconcat ((:)
                                                                     (s2b Prelude.$ "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\n\r\n" Prelude.++ "<html><body>")
                                                                     ((:) a0 ((:)
                                                                     (B.append (s2b ((:) '!'
                                                                       ((:) '\r'
                                                                       lF))) (s2b  "<img src=foo.png></body></html>\r\n"))
                                                                     (replicate
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       ((Prelude.+) 1
                                                                       0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                       (s2b ((:) '.'
                                                                         ((:) '.'
                                                                         ([]))))))))))
                                                                   (GHC.Base.Just
                                                                   ((,) ((,) ((,)
                                                                   (cipherHash c) c)
                                                                   (hkdfExpandLabel
                                                                     (cipherHash c)
                                                                     (hkdfExtract
                                                                       (cipherHash
                                                                         c)
                                                                       (hkdfExpandLabel
                                                                         (cipherHash
                                                                           c)
                                                                         (hkdfExtract
                                                                           (cipherHash
                                                                           c)
                                                                           (hkdfExpandLabel
                                                                           (cipherHash
                                                                           c)
                                                                           (hkdfExtract
                                                                           (cipherHash
                                                                           c)
                                                                           (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0)
                                                                           (b_replicate
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0))
                                                                           (s2b ((:)
                                                                           'd' ((:)
                                                                           'e' ((:)
                                                                           'r' ((:)
                                                                           'i' ((:)
                                                                           'v' ((:)
                                                                           'e' ((:)
                                                                           'd'
                                                                           ([])))))))))
                                                                           (hashWith
                                                                           (cipherHash
                                                                           c) ((:)
                                                                           (s2b
                                                                           ([]))
                                                                           []))
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)))
                                                                           (ba_convert
                                                                           (snd p)))
                                                                         (s2b ((:)
                                                                           'd' ((:)
                                                                           'e' ((:)
                                                                           'r' ((:)
                                                                           'i' ((:)
                                                                           'v' ((:)
                                                                           'e' ((:)
                                                                           'd'
                                                                           ([])))))))))
                                                                         (hashWith
                                                                           (cipherHash
                                                                           c) ((:)
                                                                           (s2b
                                                                           ([]))
                                                                           []))
                                                                         (hashDigestSize
                                                                           (cipherHash
                                                                           c)))
                                                                       (b_replicate
                                                                         (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0))
                                                                     (s2b ((:) 's'
                                                                       ((:) ' ' ((:)
                                                                       'a' ((:) 'p'
                                                                       ((:) ' ' ((:)
                                                                       't' ((:) 'r'
                                                                       ((:) 'a' ((:)
                                                                       'f' ((:) 'f'
                                                                       ((:) 'i' ((:)
                                                                       'c'
                                                                       ([]))))))))))))))
                                                                     (hashWith
                                                                       (cipherHash
                                                                         c) ((:) b
                                                                       ((:) b0 ((:)
                                                                       b1 ((:) b2
                                                                       ((:) b3 ((:)
                                                                       b4 [])))))))
                                                                     (hashDigestSize
                                                                       (cipherHash
                                                                         c))))
                                                                   0))))))));
                                                                  GHC.Base.Nothing ->
                                                                   GHC.Base.Nothing};
                                                                GHC.Base.Nothing ->
                                                                 GHC.Base.Nothing}})))))))))))))
                                        (sum_merge
                                          (prod_curry
                                            (prod_curry
                                              (prod_curry
                                                (prod_curry
                                                  (prod_curry
                                                    (prod_curry
                                                      (prod_curry
                                                        (prod_curry
                                                          (prod_curry
                                                            (prod_curry
                                                              (\_ b c p b0 b1 b2 b3 b4 n _ _ r ->
                                                              Prelude.Left ((,)
                                                              (case r of {
                                                                Prelude.Left _ ->
                                                                 Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 (Prelude.Right
                                                                 ()))))))))))))))))));
                                                                Prelude.Right _ ->
                                                                 (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                                   (\_ ->
                                                                   Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   ())))))))))))))))))))
                                                                   (\n0' ->
                                                                   Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Right
                                                                   (Prelude.Left
                                                                   ((,) ((,) ((,)
                                                                   ((,) ((,) ((,)
                                                                   ((,) ((,) ((,) ()
                                                                   b) c) p) b0) b1)
                                                                   b2) b3) b4)
                                                                   n0'))))))))))))))))))
                                                                   n})
                                                              (case r of {
                                                                Prelude.Left _ ->
                                                                 GHC.Base.Nothing;
                                                                Prelude.Right _ ->
                                                                 (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                                   (\_ ->
                                                                   GHC.Base.Nothing)
                                                                   (\_ ->
                                                                   GHC.Base.Just
                                                                   (ExistT Yield
                                                                   (Prelude.Right
                                                                   ((Prelude.+) 1
                                                                   ((Prelude.+) 1
                                                                   ((Prelude.+) 1
                                                                   ((Prelude.+) 1
                                                                   ((Prelude.+) 1
                                                                   0))))))))
                                                                   n})))))))))))))
                                          (\u _ _ -> Prelude.Right u))))))))))))))))))))
    (\fuel certs priv ->
    unsafeCoerce (Prelude.Left ((,) ((,) ((,) () fuel) certs) priv))))

data Eff_conn =
   NewAccept
 | Perform
 | Receive

type Args_conn = Any

type Rets_conn = Any

doHandshake_step :: Step_type Yield_effect Args_tls' Rets_tls' () Any
doHandshake_step =
  projT1 (projT2 doHandshake_derive)

lift_conn :: Eff_conn -> (Rets_conn -> Prelude.Either a1 (GHC.Base.Maybe a2)) ->
             Eff_conn -> Rets_conn -> Prelude.Either a1 (GHC.Base.Maybe a2)
lift_conn e a e0 =
  case e of {
   NewAccept ->
    case e0 of {
     NewAccept -> a;
     _ -> (\_ -> Prelude.Right GHC.Base.Nothing)};
   Perform ->
    case e0 of {
     Perform -> a;
     _ -> (\_ -> Prelude.Right GHC.Base.Nothing)};
   Receive ->
    case e0 of {
     Receive -> a;
     _ -> (\_ -> Prelude.Right GHC.Base.Nothing)}}

main_loop_step :: (Prelude.Either
                  ((,) ((,) ((,) () CertificateChain) PrivateKey) GHC.Base.Int)
                  (Prelude.Either
                  ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) GHC.Base.Int)
                  (Map Any))
                  (Prelude.Either
                  ((,)
                  ((,)
                  ((,)
                  ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) GHC.Base.Int)
                  (Map Any)) Prelude.String) Any) Args_tls')
                  (Prelude.Either
                  ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) GHC.Base.Int)
                  (Map Any))
                  (Prelude.Either
                  ((,)
                  ((,)
                  ((,)
                  ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) GHC.Base.Int)
                  (Map Any)) ((,) Prelude.String Rets_tls')) Any) Args_tls')
                  (GHC.Base.Maybe ())))))) -> Eff_conn -> Rets_conn ->
                  Prelude.Either
                  ((,)
                  (Prelude.Either
                  ((,) ((,) ((,) () CertificateChain) PrivateKey) GHC.Base.Int)
                  (Prelude.Either
                  ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) GHC.Base.Int)
                  (Map Any))
                  (Prelude.Either
                  ((,)
                  ((,)
                  ((,)
                  ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) GHC.Base.Int)
                  (Map Any)) Prelude.String) Any) Args_tls')
                  (Prelude.Either
                  ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) GHC.Base.Int)
                  (Map Any))
                  (Prelude.Either
                  ((,)
                  ((,)
                  ((,)
                  ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) GHC.Base.Int)
                  (Map Any)) ((,) Prelude.String Rets_tls')) Any) Args_tls')
                  (GHC.Base.Maybe ()))))))
                  (GHC.Base.Maybe (SigT Eff_conn Args_conn))) (GHC.Base.Maybe ())
main_loop_step =
  sum_merge
    (prod_curry
      (prod_curry
        (prod_curry (\_ c p n _ _ -> Prelude.Left ((,)
          ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
             (\_ -> Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
             (Prelude.Right (GHC.Base.Just ()))))))
             (\n0 -> Prelude.Right (Prelude.Left ((,) ((,) ((,) ((,) () c) p) n0)
             Leaf)))
             n)
          ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
             (\_ -> GHC.Base.Nothing)
             (\_ -> GHC.Base.Just (ExistT NewAccept (unsafeCoerce ())))
             n))))))
    (sum_merge
      (prod_curry
        (prod_curry
          (prod_curry
            (prod_curry (\_ c p n m ->
              lift_conn NewAccept (\r -> Prelude.Left ((,)
                (case unsafeCoerce r of {
                  GHC.Base.Just a -> Prelude.Right (Prelude.Right (Prelude.Left ((,)
                   ((,) ((,) ((,) ((,) ((,) ((,) () c) p) n) m) a)
                   (unsafeCoerce (Prelude.Right (Prelude.Left ((,) ((,) ((,) ()
                     ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                     ((Prelude.+) 1 0)))))) c) p))))) (Prelude.Right ((Prelude.+) 1
                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                   0)))))))));
                  GHC.Base.Nothing -> Prelude.Right (Prelude.Right (Prelude.Right
                   (Prelude.Left ((,) ((,) ((,) ((,) () c) p) n) m))))})
                (case unsafeCoerce r of {
                  GHC.Base.Just a -> GHC.Base.Just (ExistT Perform
                   (unsafeCoerce ((,) a (Prelude.Right ((Prelude.+) 1 ((Prelude.+) 1
                     ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 0)))))))));
                  GHC.Base.Nothing -> GHC.Base.Just (ExistT Receive
                   (unsafeCoerce ()))}))))))))
      (sum_merge
        (prod_curry
          (prod_curry
            (prod_curry
              (prod_curry
                (prod_curry
                  (prod_curry
                    (prod_curry (\_ c p n m s p0 _ ->
                      lift_conn Perform (\_ -> Prelude.Left ((,)
                        ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                           (\_ -> Prelude.Right (Prelude.Right (Prelude.Right
                           (Prelude.Right (Prelude.Right (GHC.Base.Just
                           ()))))))
                           (\n0' -> Prelude.Right (Prelude.Left ((,) ((,) ((,) ((,)
                           () c) p) n0') (insert s p0 m))))
                           n)
                        ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                           (\_ -> GHC.Base.Nothing)
                           (\_ -> GHC.Base.Just (ExistT NewAccept
                           (unsafeCoerce ())))
                           n)))))))))))
        (sum_merge
          (prod_curry
            (prod_curry
              (prod_curry
                (prod_curry (\_ c p n m ->
                  lift_conn Receive (\r -> Prelude.Left ((,)
                    (case unsafeCoerce r of {
                      GHC.Base.Just a ->
                       case bsearch (fst a) m of {
                        GHC.Base.Just a0 ->
                         case doHandshake_step a0 Yield (snd a) of {
                          Prelude.Left p0 ->
                           case p0 of {
                            (,) s o ->
                             case o of {
                              GHC.Base.Just s0 ->
                               case s0 of {
                                ExistT _ v -> Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Left ((,)
                                 ((,) ((,) ((,) ((,) ((,) ((,) () c) p) n) m) a) s)
                                 v)))))};
                              GHC.Base.Nothing -> Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (Prelude.Right
                               GHC.Base.Nothing))))}};
                          Prelude.Right _ -> Prelude.Right (Prelude.Right
                           (Prelude.Right (Prelude.Right (Prelude.Right
                           GHC.Base.Nothing))))};
                        GHC.Base.Nothing -> Prelude.Right (Prelude.Right
                         (Prelude.Right (Prelude.Right (Prelude.Right
                         GHC.Base.Nothing))))};
                      GHC.Base.Nothing ->
                       (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                         (\_ -> Prelude.Right (Prelude.Right (Prelude.Right
                         (Prelude.Right (Prelude.Right (GHC.Base.Just
                         ()))))))
                         (\n0' -> Prelude.Right (Prelude.Left ((,) ((,) ((,) ((,) ()
                         c) p) n0') m)))
                         n})
                    (case unsafeCoerce r of {
                      GHC.Base.Just a ->
                       case bsearch (fst a) m of {
                        GHC.Base.Just a0 ->
                         case doHandshake_step a0 Yield (snd a) of {
                          Prelude.Left p0 ->
                           case p0 of {
                            (,) _ o ->
                             case o of {
                              GHC.Base.Just s0 ->
                               case s0 of {
                                ExistT _ v -> GHC.Base.Just (ExistT Perform
                                 (unsafeCoerce ((,) (fst a) v)))};
                              GHC.Base.Nothing -> GHC.Base.Nothing}};
                          Prelude.Right _ -> GHC.Base.Nothing};
                        GHC.Base.Nothing -> GHC.Base.Nothing};
                      GHC.Base.Nothing ->
                       (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                         (\_ -> GHC.Base.Nothing)
                         (\_ -> GHC.Base.Just (ExistT NewAccept (unsafeCoerce ())))
                         n}))))))))
          (sum_merge
            (prod_curry
              (prod_curry
                (prod_curry
                  (prod_curry
                    (prod_curry
                      (prod_curry
                        (prod_curry (\_ c p n m p0 p1 _ ->
                          lift_conn Perform (\_ -> Prelude.Left ((,)
                            ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                               (\_ -> Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (GHC.Base.Just
                               ()))))))
                               (\n0' -> Prelude.Right (Prelude.Left ((,) ((,) ((,)
                               ((,) () c) p) n0') (replace_map (fst p0) p1 m))))
                               n)
                            ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                               (\_ -> GHC.Base.Nothing)
                               (\_ -> GHC.Base.Just (ExistT NewAccept
                               (unsafeCoerce ())))
                               n))))))))))) (\o _ _ -> Prelude.Right o)))))

