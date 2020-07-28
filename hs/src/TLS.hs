{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module TLS where

import qualified Network.TLS as T
import qualified Network.TLS.Internal as I
import qualified Data.ByteString as B
import qualified Data.ByteString.Internal
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

andb :: GHC.Base.Bool -> GHC.Base.Bool -> GHC.Base.Bool
andb b1 b2 =
  case b1 of {
   GHC.Base.True -> b2;
   GHC.Base.False -> GHC.Base.False}

negb :: GHC.Base.Bool -> GHC.Base.Bool
negb b =
  case b of {
   GHC.Base.True -> GHC.Base.False;
   GHC.Base.False -> GHC.Base.True}

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

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   [] -> m;
   (:) a l1 -> (:) a (app l1 m)}

data Comparison =
   Eq
 | Lt
 | Gt

data SigT a p =
   ExistT a p

add :: GHC.Base.Int -> GHC.Base.Int -> GHC.Base.Int
add n m =
  (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\p -> (Prelude.+) 1 (add p m))
    n

sub :: GHC.Base.Int -> GHC.Base.Int -> GHC.Base.Int
sub n m =
  (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
    (\_ -> n)
    (\k ->
    (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
      (\_ -> n)
      (\l -> sub k l)
      m)
    n

leb :: GHC.Base.Int -> GHC.Base.Int -> GHC.Base.Bool
leb n m =
  (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
    (\_ -> GHC.Base.True)
    (\n' ->
    (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
      (\_ -> GHC.Base.False)
      (\m' -> leb n' m')
      m)
    n

ltb :: GHC.Base.Int -> GHC.Base.Int -> GHC.Base.Bool
ltb n m =
  leb ((Prelude.+) 1 n) m

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

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   [] -> [];
   (:) a t -> (:) (f a) (map f t)}

fold_left :: (a1 -> a2 -> a1) -> (([]) a2) -> a1 -> a1
fold_left f l a0 =
  case l of {
   [] -> a0;
   (:) b t -> fold_left f t (f a0 b)}

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

type Inhabit a = a
  -- singleton inductive, whose constructor was Build_Inhabit
  
inhabitant :: (Inhabit a1) -> a1
inhabitant inhabit =
  inhabit

unit_inhabitant :: Inhabit ()
unit_inhabitant =
  ()

prod_inhabitant :: (Inhabit a1) -> (Inhabit a2) -> Inhabit ((,) a1 a2)
prod_inhabitant iA iB =
  (,) (inhabitant iA) (inhabitant iB)

option_inhabitant :: Inhabit (GHC.Base.Maybe a1)
option_inhabitant =
  GHC.Base.Nothing

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

sum_merge :: (a1 -> a3) -> (a2 -> a3) -> (Prelude.Either a1 a2) -> a3
sum_merge f g x =
  case x of {
   Prelude.Left a -> f a;
   Prelude.Right b -> g b}

option_branch :: (a1 -> a2) -> a2 -> (GHC.Base.Maybe a1) -> a2
option_branch f f0 o =
  case o of {
   GHC.Base.Just a -> f a;
   GHC.Base.Nothing -> f0}

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

type Word8 = Data.Word8.Word8

type HashAndSignatureAlgorithm = (,) I.HashAlgorithm I.SignatureAlgorithm

isHashSignatureValid :: ((,) I.HashAlgorithm I.SignatureAlgorithm) -> GHC.Base.Bool
isHashSignatureValid pat =
  case pat of {
   (,) h sig ->
    case h of {
     I.HashSHA256 ->
      case sig of {
       I.SignatureECDSA -> GHC.Base.True;
       _ -> GHC.Base.False};
     I.HashSHA384 ->
      case sig of {
       I.SignatureECDSA -> GHC.Base.True;
       _ -> GHC.Base.False};
     I.HashSHA512 ->
      case sig of {
       I.SignatureECDSA -> GHC.Base.True;
       _ -> GHC.Base.False};
     I.HashIntrinsic ->
      case sig of {
       I.SignatureAnonymous -> GHC.Base.False;
       I.SignatureRSA -> GHC.Base.False;
       I.SignatureDSS -> GHC.Base.False;
       I.SignatureECDSA -> GHC.Base.False;
       I.SignatureOther _ -> GHC.Base.False;
       _ -> GHC.Base.True};
     _ -> GHC.Base.False}}

extension_KeyShare :: (([]) ExtensionRaw) -> GHC.Base.Maybe (([]) I.KeyShareEntry)
extension_KeyShare = (\exts -> case Helper.extensionLookup I.extensionID_KeyShare exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.KeyShareClientHello kses) -> GHC.Base.return kses})

type Word32 = Data.Word.Word32

type PublicKey = X.PubKey

type PrivateKey = X.PrivKey

type GroupPublic = I.GroupPublic

type GroupKey = I.GroupKey

type Hash = T.Hash

type Cipher = T.Cipher

type KeyUpdate = I.KeyUpdate

type Certificate = X.Certificate

type CertificateChain = X.CertificateChain

type Signature = I.Signature

data RecvType =
   RFinished
 | RClientHello
 | RAppData
 | RCCS

recvType_beq :: RecvType -> RecvType -> GHC.Base.Bool
recvType_beq x y =
  case x of {
   RFinished -> case y of {
                 RFinished -> GHC.Base.True;
                 _ -> GHC.Base.False};
   RClientHello -> case y of {
                    RClientHello -> GHC.Base.True;
                    _ -> GHC.Base.False};
   RAppData -> case y of {
                RAppData -> GHC.Base.True;
                _ -> GHC.Base.False};
   RCCS -> case y of {
            RCCS -> GHC.Base.True;
            _ -> GHC.Base.False}}

data ClientHelloMsg =
   Build_ClientHelloMsg Version ByteString Session (([]) CipherID) (([])
                                                                   ExtensionRaw)

chSess :: ClientHelloMsg -> Session
chSess c =
  case c of {
   Build_ClientHelloMsg _ _ chSess0 _ _ -> chSess0}

chCipherIDs :: ClientHelloMsg -> ([]) CipherID
chCipherIDs c =
  case c of {
   Build_ClientHelloMsg _ _ _ chCipherIDs0 _ -> chCipherIDs0}

chExt :: ClientHelloMsg -> ([]) ExtensionRaw
chExt c =
  case c of {
   Build_ClientHelloMsg _ _ _ _ chExt0 -> chExt0}

clientHello :: I.Handshake13 -> GHC.Base.Maybe ClientHelloMsg
clientHello h =
  case h of {
   I.ClientHello13 v c sess cipherIDs ext ->
    case c of {
     I.ClientRandom rand -> GHC.Base.Just (Build_ClientHelloMsg v rand sess
      cipherIDs ext)};
   _ -> GHC.Base.Nothing}

finished :: I.Handshake13 -> GHC.Base.Maybe ByteString
finished h =
  case h of {
   I.Finished13 bs -> GHC.Base.Just bs;
   _ -> GHC.Base.Nothing}

cipherID_beq :: CipherID -> CipherID -> GHC.Base.Bool
cipherID_beq = (GHC.Base.==)

cipherID :: Cipher -> CipherID
cipherID = T.cipherID

hash_beq :: Hash -> Hash -> GHC.Base.Bool
hash_beq = (GHC.Base.==)

cipherHash :: Cipher -> Hash
cipherHash = T.cipherHash

version_beq :: Version -> Version -> GHC.Base.Bool
version_beq = (Prelude.==)

byteString_beq :: ByteString -> ByteString -> GHC.Base.Bool
byteString_beq = (GHC.Base.==)

blength :: ByteString -> GHC.Base.Int
blength = B.length

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

extensionLookup_SignatureAlgorithms :: (([]) ExtensionRaw) -> GHC.Base.Maybe
                                       ByteString
extensionLookup_SignatureAlgorithms = Helper.extensionLookup I.extensionID_SignatureAlgorithms

extensionDecode_SignatureAlgorithms :: ByteString -> GHC.Base.Maybe
                                       (([]) HashAndSignatureAlgorithm)
extensionDecode_SignatureAlgorithms = \exts -> case I.extensionDecode I.MsgTClientHello exts of { GHC.Base.Just (I.SignatureAlgorithms sas) -> GHC.Base.Just sas; _ -> GHC.Base.Nothing }

getCertificates :: CertificateChain -> ([]) Certificate
getCertificates = \cch -> case cch of { X.CertificateChain certs -> Prelude.map X.getCertificate certs }

empty :: ByteString
empty = B.empty

hashWith :: Hash -> (([]) ByteString) -> ByteString
hashWith = Helper.hashWith

sniExt :: ExtensionRaw
sniExt = Helper.sniExt

encodeGroupPublic :: GroupPublic -> ByteString
encodeGroupPublic = I.encodeGroupPublic

decodeGroupPublic :: T.Group -> ByteString -> GHC.Base.Maybe GroupPublic
decodeGroupPublic = \g bs -> case I.decodeGroupPublic g bs of { Prelude.Right a -> GHC.Base.Just a; _ -> GHC.Base.Nothing }

ba_convert :: GroupKey -> ByteString
ba_convert = BA.convert

hashDigestSize :: Hash -> GHC.Base.Int
hashDigestSize = I.hashDigestSize

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
  let {
   aux hss =
     case hss of {
      [] -> GHC.Base.Nothing;
      (:) hs rest ->
       case decideCredInfo' priv hs certs of {
        GHC.Base.Just res -> GHC.Base.Just res;
        GHC.Base.Nothing -> aux rest}}}
  in aux (filter isHashSignatureValid hashSigs)

lF :: Prelude.String
lF =
  (:) '\n' ([])

mconcat :: (([]) ByteString) -> ByteString
mconcat = B.concat

serverCiphers :: ([]) Cipher
serverCiphers = I.ciphersuite_default

type Word64 = Data.Word.Word64

lifetime :: T.TLS13TicketInfo -> Word32
lifetime t =
  case t of {
   T.TLS13TicketInfo lifetime0 _ _ _ -> lifetime0}

ageAdd :: T.TLS13TicketInfo -> Word32
ageAdd t =
  case t of {
   T.TLS13TicketInfo _ ageAdd0 _ _ -> ageAdd0}

txrxTime :: T.TLS13TicketInfo -> Word64
txrxTime t =
  case t of {
   T.TLS13TicketInfo _ _ txrxTime0 _ -> txrxTime0}

estimatedRTT :: T.TLS13TicketInfo -> GHC.Base.Maybe Word64
estimatedRTT t =
  case t of {
   T.TLS13TicketInfo _ _ _ estimatedRTT0 -> estimatedRTT0}

type CompressionID = T.CompressionID

sessionCipher :: I.SessionData -> CipherID
sessionCipher s =
  case s of {
   I.SessionData _ sessionCipher0 _ _ _ _ _ _ _ _ -> sessionCipher0}

sessionSecret :: I.SessionData -> ByteString
sessionSecret s =
  case s of {
   I.SessionData _ _ _ _ sessionSecret0 _ _ _ _ _ -> sessionSecret0}

sessionTicketInfo :: I.SessionData -> GHC.Base.Maybe T.TLS13TicketInfo
sessionTicketInfo s =
  case s of {
   I.SessionData _ _ _ _ _ _ sessionTicketInfo0 _ _ _ -> sessionTicketInfo0}

data Args_tls =
   SetPSK ((,) Prelude.String I.SessionData)
 | SessionResume Prelude.String
 | GetCurrentTime ()
 | CloseWith ((,) I.AlertLevel I.AlertDescription)
 | SendData ((,) I.Packet13
            (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int)))
 | GetRandomBytes GHC.Base.Int
 | RecvData ()
 | GroupGetPubShared GroupPublic
 | MakeCertVerify ((,) ((,) ((,) PublicKey PrivateKey) HashAndSignatureAlgorithm)
                  ByteString)
 | SetSecret ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Bool)
 | SendPacket I.Packet13
 | RecvPacket RecvType

data Rets_tls =
   RetAlert ((,) I.AlertLevel I.AlertDescription)
 | FromSetPSK
 | FromGetCurrentTime Word64
 | FromSessionResume (GHC.Base.Maybe I.SessionData)
 | FromSetSecret
 | FromSendPacket ByteString
 | FromGetRandomBytes ByteString
 | FromMakeCertVerify I.Handshake13
 | FromGroupGetPubShared (GHC.Base.Maybe ((,) GroupPublic GroupKey))
 | FromRecvClientHello ((,) ByteString ClientHelloMsg)
 | FromRecvFinished ByteString
 | FromRecvCCS
 | FromRecvAppData ByteString
 | FromRecvData ByteString

retAlert :: Rets_tls -> GHC.Base.Maybe ((,) I.AlertLevel I.AlertDescription)
retAlert p =
  case p of {
   RetAlert a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

fromSessionResume :: Rets_tls -> GHC.Base.Maybe (GHC.Base.Maybe I.SessionData)
fromSessionResume p =
  case p of {
   FromSessionResume a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

fromGetCurrentTime :: Rets_tls -> GHC.Base.Maybe Word64
fromGetCurrentTime p =
  case p of {
   FromGetCurrentTime a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

fromSendPacket :: Rets_tls -> GHC.Base.Maybe ByteString
fromSendPacket p =
  case p of {
   FromSendPacket a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

fromGetRandomBytes :: Rets_tls -> GHC.Base.Maybe ByteString
fromGetRandomBytes p =
  case p of {
   FromGetRandomBytes a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

fromMakeCertVerify :: Rets_tls -> GHC.Base.Maybe I.Handshake13
fromMakeCertVerify p =
  case p of {
   FromMakeCertVerify a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

fromGroupGetPubShared :: Rets_tls -> GHC.Base.Maybe
                         (GHC.Base.Maybe ((,) GroupPublic GroupKey))
fromGroupGetPubShared p =
  case p of {
   FromGroupGetPubShared a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

fromRecvClientHello :: Rets_tls -> GHC.Base.Maybe ((,) ByteString ClientHelloMsg)
fromRecvClientHello p =
  case p of {
   FromRecvClientHello a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

fromRecvFinished :: Rets_tls -> GHC.Base.Maybe ByteString
fromRecvFinished p =
  case p of {
   FromRecvFinished a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

fromRecvAppData :: Rets_tls -> GHC.Base.Maybe ByteString
fromRecvAppData p =
  case p of {
   FromRecvAppData a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

fromRecvData :: Rets_tls -> GHC.Base.Maybe ByteString
fromRecvData p =
  case p of {
   FromRecvData a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

sigT_rets_inhabit :: Inhabit Rets_tls
sigT_rets_inhabit =
  FromSetPSK

type ProtocolType = I.ProtocolType

hdReadLen :: I.Header -> GHC.Base.Int
hdReadLen hd =
  case hd of {
   I.Header _ _ n -> Prelude.fromIntegral n}

bsplit :: GHC.Base.Int -> ByteString -> (,) ByteString ByteString
bsplit = B.splitAt

pskKexMode_beq :: I.PskKexMode -> I.PskKexMode -> GHC.Base.Bool
pskKexMode_beq x y =
  case x of {
   I.PSK_KE ->
    case y of {
     I.PSK_KE -> GHC.Base.True;
     I.PSK_DHE_KE -> GHC.Base.False};
   I.PSK_DHE_KE ->
    case y of {
     I.PSK_KE -> GHC.Base.False;
     I.PSK_DHE_KE -> GHC.Base.True}}

find0 :: (a1 -> GHC.Base.Bool) -> (([]) a1) -> GHC.Base.Maybe a1
find0 f l =
  case l of {
   [] -> GHC.Base.Nothing;
   (:) a l' ->
    case f a of {
     GHC.Base.True -> GHC.Base.Just a;
     GHC.Base.False -> find0 f l'}}

extension_PreSharedKey :: (([]) ExtensionRaw) -> GHC.Base.Maybe I.PreSharedKey
extension_PreSharedKey = \exts -> Helper.extensionLookup I.extensionID_PreSharedKey exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello

extension_PreSharedKeyCH :: (([]) ExtensionRaw) -> GHC.Base.Maybe
                            ((,) ((,) ByteString Word32) (([]) ByteString))
extension_PreSharedKeyCH exts =
  case extension_PreSharedKey exts of {
   GHC.Base.Just p ->
    case p of {
     I.PreSharedKeyClientHello l bnds ->
      case l of {
       [] -> GHC.Base.Nothing;
       (:) p0 _ ->
        case p0 of {
         I.PskIdentity sessionID obfAge -> GHC.Base.Just ((,) ((,) sessionID obfAge)
          bnds)}};
     I.PreSharedKeyServerHello _ -> GHC.Base.Nothing};
   GHC.Base.Nothing -> GHC.Base.Nothing}

sumnat :: (([]) GHC.Base.Int) -> GHC.Base.Int
sumnat l =
  fold_left add l 0

b2s :: ByteString -> Prelude.String
b2s = (\b -> Prelude.map Data.ByteString.Internal.w2c (B.unpack b))

word32minus :: Word32 -> Word32 -> Word32
word32minus = (Prelude.-)

word64plus :: Word64 -> Word64 -> Word64
word64plus = (Prelude.+)

word64minus :: Word64 -> Word64 -> Word64
word64minus = (Prelude.-)

word64max :: Word64 -> Word64 -> Word64
word64max = Prelude.max

word64gt :: Word64 -> Word64 -> GHC.Base.Bool
word64gt = (Prelude.>)

word32le :: Word32 -> Word32 -> GHC.Base.Bool
word32le = (Prelude.<=)

w64_2000 :: Word64
w64_2000 = 2000

w32to64 :: Word32 -> Word64
w32to64 = Prelude.fromIntegral

bool_inhabitant :: Inhabit GHC.Base.Bool
bool_inhabitant =
  GHC.Base.True

checkFreshness :: T.TLS13TicketInfo -> Word32 -> Word64 -> GHC.Base.Bool
checkFreshness tinfo obfAge serverReceiveTime =
  case estimatedRTT tinfo of {
   GHC.Base.Just rtt ->
    let {age = word32minus obfAge (ageAdd tinfo)} in
    let {
     expectedArrivalTime = word64plus (txrxTime tinfo)
                             (word64plus rtt (w32to64 age))}
    in
    let {
     freshness = case word64gt expectedArrivalTime serverReceiveTime of {
                  GHC.Base.True -> word64minus expectedArrivalTime serverReceiveTime;
                  GHC.Base.False ->
                   word64minus serverReceiveTime expectedArrivalTime}}
    in
    andb (word32le age (lifetime tinfo))
      (word64gt (word64max rtt w64_2000) freshness);
   GHC.Base.Nothing -> GHC.Base.False}

byteString_inhabitant :: Inhabit ByteString
byteString_inhabitant =
  empty

btake :: GHC.Base.Int -> ByteString -> ByteString
btake = B.take

makePSKBinder :: ByteString -> ByteString -> Hash -> GHC.Base.Int -> GHC.Base.Int ->
                 ByteString
makePSKBinder chEncoded sec usedHash truncLen hsize =
  let {msg = btake (sub (blength chEncoded) truncLen) chEncoded} in
  let {hChTruncated = hashWith usedHash ((:) msg [])} in
  let {
   binderKey = hkdfExpandLabel usedHash sec
                 (s2b ((:) 'r' ((:) 'e' ((:) 's' ((:) ' ' ((:) 'b' ((:) 'i' ((:) 'n'
                   ((:) 'd' ((:) 'e' ((:) 'r' ([]))))))))))))
                 (hashWith usedHash ((:) (s2b ([])) [])) hsize}
  in
  makeVerifyData usedHash binderKey hChTruncated

extensionEncode_PreSharedKey :: I.PreSharedKey -> ByteString
extensionEncode_PreSharedKey = I.extensionEncode

extensionRaw_PreSharedKey :: ByteString -> ExtensionRaw
extensionRaw_PreSharedKey = I.ExtensionRaw I.extensionID_PreSharedKey

checkBinder :: ByteString -> Hash -> ByteString -> (GHC.Base.Maybe
               ((,) ((,) ByteString GHC.Base.Int) GHC.Base.Int)) -> GHC.Base.Int ->
               GHC.Base.Maybe (([]) ExtensionRaw)
checkBinder chEncoded usedHash earlySecret binderInfo hsize =
  case binderInfo of {
   GHC.Base.Just y ->
    case y of {
     (,) y0 tlen ->
      case y0 of {
       (,) binder n ->
        let {binder' = makePSKBinder chEncoded earlySecret usedHash tlen hsize} in
        case byteString_beq binder' binder of {
         GHC.Base.True ->
          let {
           selectedIdentity = extensionEncode_PreSharedKey
                                (I.PreSharedKeyServerHello n)}
          in
          GHC.Base.Just ((:) (extensionRaw_PreSharedKey selectedIdentity) []);
         GHC.Base.False -> GHC.Base.Nothing}}};
   GHC.Base.Nothing -> GHC.Base.Just []}

chooseServerName' :: (([]) I.ServerNameType) -> GHC.Base.Maybe Prelude.String
chooseServerName' ns =
  case ns of {
   [] -> GHC.Base.Nothing;
   (:) name rest ->
    case name of {
     I.ServerNameHostName hostName -> GHC.Base.Just hostName;
     I.ServerNameOther _ -> chooseServerName' rest}}

extension_ServerName :: (([]) ExtensionRaw) -> GHC.Base.Maybe I.ServerName
extension_ServerName = \exts -> Helper.extensionLookup I.extensionID_ServerName exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello

chooseServerName :: (([]) ExtensionRaw) -> GHC.Base.Maybe Prelude.String
chooseServerName exts =
  case extension_ServerName exts of {
   GHC.Base.Just s -> case s of {
                       I.ServerName ns -> chooseServerName' ns};
   GHC.Base.Nothing -> GHC.Base.Nothing}

extension_PskKeyModes :: (([]) ExtensionRaw) -> GHC.Base.Maybe (([]) I.PskKexMode)
extension_PskKeyModes = (\exts -> case Helper.extensionLookup I.extensionID_PskKeyExchangeModes exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.PskKeyExchangeModes ms) -> GHC.Base.return ms; GHC.Base.Nothing -> GHC.Base.return []})

extension_SupportedVersionsCH :: (([]) ExtensionRaw) -> GHC.Base.Maybe
                                 (([]) Version)
extension_SupportedVersionsCH = \exts -> case Helper.extensionLookup I.extensionID_SupportedVersions exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of {GHC.Base.Just (I.SupportedVersionsClientHello vers) -> GHC.Base.Just vers; _ -> GHC.Base.Nothing }

clientKeySharesValid :: (([]) I.KeyShareEntry) -> (([]) T.Group) -> GHC.Base.Bool
clientKeySharesValid ks gs =
  case ks of {
   [] -> GHC.Base.True;
   (:) k ks' ->
    case gs of {
     [] -> GHC.Base.False;
     (:) g gs' ->
      case group_beq (ksGroup k) g of {
       GHC.Base.True -> clientKeySharesValid ks' gs';
       GHC.Base.False -> clientKeySharesValid ((:) k ks') gs'}}}

extension_SupportedGroups :: (([]) ExtensionRaw) -> GHC.Base.Maybe (([]) T.Group)
extension_SupportedGroups = \exts -> case Helper.extensionLookup I.extensionID_NegotiatedGroups exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.NegotiatedGroups gs) -> GHC.Base.Just gs; _ -> GHC.Base.Nothing }

type DoHandshake_state =
  Prelude.Either ((,) ((,) ((,) () GHC.Base.Int) CertificateChain) PrivateKey)
  (Prelude.Either ()
  (Prelude.Either ((,) ((,) () CertificateChain) PrivateKey)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) ByteString) ClientHelloMsg)
  Cipher) I.KeyShareEntry) (([]) ByteString)) ClientHelloMsg) GroupPublic)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) ByteString) ClientHelloMsg)
  Cipher) I.KeyShareEntry) (([]) ByteString)) ClientHelloMsg)
  ((,) GroupPublic GroupKey)) (([]) ByteString)) ByteString) Word32) ByteString)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) ByteString) ClientHelloMsg)
  Cipher) I.KeyShareEntry) (([]) ByteString)) ClientHelloMsg)
  ((,) GroupPublic GroupKey)) (([]) ByteString)) Word32) ByteString) I.SessionData)
  T.TLS13TicketInfo)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) ByteString) ClientHelloMsg)
  Cipher) I.KeyShareEntry) (([]) ByteString)) ClientHelloMsg)
  ((,) GroupPublic GroupKey)) ByteString)
  (GHC.Base.Maybe ((,) ((,) ByteString GHC.Base.Int) GHC.Base.Int)))
  (([]) ExtensionRaw))
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) ByteString) ClientHelloMsg)
  Cipher) I.KeyShareEntry) (([]) ByteString)) ClientHelloMsg)
  ((,) GroupPublic GroupKey)) ByteString)
  (GHC.Base.Maybe ((,) ((,) ByteString GHC.Base.Int) GHC.Base.Int)))
  (([]) ExtensionRaw))
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) ByteString) ClientHelloMsg)
  Cipher) I.KeyShareEntry) (([]) ByteString)) ClientHelloMsg)
  ((,) GroupPublic GroupKey)) ByteString) (([]) ExtensionRaw))
  (GHC.Base.Maybe (([]) HashAndSignatureAlgorithm)))
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) ByteString) ClientHelloMsg)
  Cipher) I.KeyShareEntry) (([]) ByteString)) ClientHelloMsg)
  ((,) GroupPublic GroupKey)) ByteString) (([]) ExtensionRaw))
  (GHC.Base.Maybe (([]) HashAndSignatureAlgorithm))) ByteString)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) ByteString) Cipher)
  (([]) ByteString)) ClientHelloMsg) ((,) GroupPublic GroupKey)) ByteString)
  (GHC.Base.Maybe (([]) HashAndSignatureAlgorithm))) ByteString)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) ByteString) Cipher)
  (([]) ByteString)) ClientHelloMsg) ((,) GroupPublic GroupKey)) ByteString)
  (GHC.Base.Maybe (([]) HashAndSignatureAlgorithm))) ByteString)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) ByteString) Cipher)
  (([]) ByteString)) ClientHelloMsg) ((,) GroupPublic GroupKey)) ByteString)
  (GHC.Base.Maybe (([]) HashAndSignatureAlgorithm))) ByteString)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) ByteString) Cipher)
  (([]) ByteString)) ((,) GroupPublic GroupKey)) ByteString)
  (GHC.Base.Maybe (([]) HashAndSignatureAlgorithm))) ByteString) ByteString)
  PublicKey) HashAndSignatureAlgorithm)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) ByteString) Cipher)
  (([]) ByteString)) ((,) GroupPublic GroupKey)) ByteString)
  (GHC.Base.Maybe (([]) HashAndSignatureAlgorithm))) ByteString) ByteString)
  PublicKey) HashAndSignatureAlgorithm) ByteString)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) ByteString) Cipher)
  (([]) ByteString)) ((,) GroupPublic GroupKey)) ByteString)
  (GHC.Base.Maybe (([]) HashAndSignatureAlgorithm))) ByteString) ByteString)
  ByteString) I.Handshake13)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) ((,) () CertificateChain) PrivateKey) ByteString) Cipher)
  (([]) ByteString)) ((,) GroupPublic GroupKey)) ByteString)
  (GHC.Base.Maybe (([]) HashAndSignatureAlgorithm))) ByteString) ByteString)
  (Prelude.Either
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) () ByteString) Cipher) ((,) GroupPublic GroupKey)) ByteString)
  ByteString) (([]) ByteString))
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) () ByteString) Cipher) ((,) GroupPublic GroupKey)) ByteString)
  ByteString) (([]) ByteString)) ByteString)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) () ByteString) Cipher) ((,) GroupPublic GroupKey)) ByteString)
  ByteString) (([]) ByteString)) ByteString)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) () ByteString) Cipher) ((,) GroupPublic GroupKey)) ByteString)
  ByteString) (([]) ByteString)) ByteString)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) () ByteString) Cipher) ((,) GroupPublic GroupKey)) ByteString)
  ByteString) (([]) ByteString)) ByteString)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) () ByteString) Cipher) ((,) GroupPublic GroupKey)) ByteString)
  ByteString) (([]) ByteString)) ByteString) ByteString)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) () ByteString) Cipher) ((,) GroupPublic GroupKey)) ByteString)
  ByteString) (([]) ByteString)) ByteString) ByteString)
  (Prelude.Either ()
  (Prelude.Either ((,) () ByteString)
  (Prelude.Either ()
  (Prelude.Either ((,) () ((,) I.AlertLevel I.AlertDescription))
  (Prelude.Either ((,) () ((,) I.AlertLevel I.AlertDescription))
  (Prelude.Either ((,) () ((,) I.AlertLevel I.AlertDescription)) ())))))))))))))))))))))))))))))

doHandshake_step :: DoHandshake_state -> Rets_tls -> Prelude.Either
                    ((,) DoHandshake_state (GHC.Base.Maybe (SigT () Args_tls))) 
                    ()
doHandshake_step x x0 =
  sum_merge
    (prod_curry
      (prod_curry
        (prod_curry (\_ _ c p _ _ -> Prelude.Left ((,) (Prelude.Right (Prelude.Right
          (Prelude.Left ((,) ((,) () c) p)))) (GHC.Base.Just (ExistT __ (RecvPacket
          RClientHello))))))))
    (sum_merge (\_ _ _ -> Prelude.Left ((,) (Prelude.Right (Prelude.Right
      (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
      (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
      (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
      (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
      (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
      (Prelude.Right (Prelude.Right (Prelude.Right ()))))))))))))))))))))))))))))))
      GHC.Base.Nothing))
      (sum_merge
        (prod_curry
          (prod_curry (\_ c p _ r -> Prelude.Left ((,)
            (option_branch (\x1 ->
              case x1 of {
               (,) a b ->
                option_branch (\_ ->
                  option_branch (\x2 ->
                    case negb
                           (clientKeySharesValid
                             (case extension_KeyShare (chExt b) of {
                               GHC.Base.Just kss -> kss;
                               GHC.Base.Nothing -> []})
                             (case extension_SupportedGroups (chExt b) of {
                               GHC.Base.Just gs -> gs;
                               GHC.Base.Nothing -> []})) of {
                     GHC.Base.True -> Prelude.Right (Prelude.Left ());
                     GHC.Base.False ->
                      option_branch (\x3 ->
                        option_branch (\x4 ->
                          case x4 of {
                           (,) a0 b0 ->
                            case a0 of {
                             (,) a1 b1 ->
                              option_branch (\x5 -> Prelude.Right (Prelude.Right
                                (Prelude.Right (Prelude.Left ((,) ((,) ((,) ((,)
                                ((,) ((,) ((,) ((,) ((,) () c) p) a) b) x2) b0) a1)
                                b1) x5))))) (Prelude.Right (Prelude.Left ()))
                                (decodeGroupPublic (ksGroup b0) (ksData b0))}})
                          (Prelude.Right (Prelude.Left ())) (GHC.Base.Just ((,) ((,)
                          ((:) a []) b) x3)))
                        (option_branch (\x3 ->
                          case x3 of {
                           (,) a0 b0 ->
                            case a0 of {
                             (,) a1 b1 ->
                              option_branch (\x4 -> Prelude.Right (Prelude.Right
                                (Prelude.Right (Prelude.Left ((,) ((,) ((,) ((,)
                                ((,) ((,) ((,) ((,) ((,) () c) p) a) b) x2) b0) a1)
                                b1) x4))))) (Prelude.Right (Prelude.Left ()))
                                (decodeGroupPublic (ksGroup b0) (ksData b0))}})
                          (Prelude.Right (Prelude.Left ())) GHC.Base.Nothing)
                        (findKeyShare
                          (case extension_KeyShare (chExt b) of {
                            GHC.Base.Just kss -> kss;
                            GHC.Base.Nothing -> []}) serverGroups)}) (Prelude.Right
                    (Prelude.Left ())) (chooseCipher (chCipherIDs b) serverCiphers))
                  (Prelude.Right (Prelude.Left ()))
                  (case extension_SupportedVersionsCH (chExt b) of {
                    GHC.Base.Just vers ->
                     case inb version_beq tLS13 vers of {
                      GHC.Base.True -> GHC.Base.Just tLS13;
                      GHC.Base.False -> GHC.Base.Nothing};
                    GHC.Base.Nothing -> GHC.Base.Nothing})})
              (option_branch (\x1 -> Prelude.Right (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Left ((,) ()
                x1))))))))))))))))))))))))))))))) (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (inhabitant unit_inhabitant)))))))))))))))))))))))))))))))
                (retAlert r)) (fromRecvClientHello r))
            (option_branch (\x1 ->
              case x1 of {
               (,) a b ->
                option_branch (\_ ->
                  option_branch (\_ ->
                    case negb
                           (clientKeySharesValid
                             (case extension_KeyShare (chExt b) of {
                               GHC.Base.Just kss -> kss;
                               GHC.Base.Nothing -> []})
                             (case extension_SupportedGroups (chExt b) of {
                               GHC.Base.Just gs -> gs;
                               GHC.Base.Nothing -> []})) of {
                     GHC.Base.True -> GHC.Base.Just (ExistT __ (CloseWith ((,)
                      I.AlertLevel_Fatal I.IllegalParameter)));
                     GHC.Base.False ->
                      option_branch (\x2 ->
                        option_branch (\x3 ->
                          case x3 of {
                           (,) _ b0 ->
                            option_branch (\x4 -> GHC.Base.Just (ExistT __
                              (GroupGetPubShared x4))) (GHC.Base.Just (ExistT __
                              (CloseWith ((,) I.AlertLevel_Fatal
                              I.IllegalParameter))))
                              (decodeGroupPublic (ksGroup b0) (ksData b0))})
                          (GHC.Base.Just (ExistT __ (CloseWith ((,)
                          I.AlertLevel_Fatal I.IllegalParameter)))) (GHC.Base.Just
                          ((,) ((,) ((:) a []) b) x2)))
                        (option_branch (\x2 ->
                          case x2 of {
                           (,) _ b0 ->
                            option_branch (\x3 -> GHC.Base.Just (ExistT __
                              (GroupGetPubShared x3))) (GHC.Base.Just (ExistT __
                              (CloseWith ((,) I.AlertLevel_Fatal
                              I.IllegalParameter))))
                              (decodeGroupPublic (ksGroup b0) (ksData b0))})
                          (GHC.Base.Just (ExistT __ (CloseWith ((,)
                          I.AlertLevel_Fatal I.IllegalParameter))))
                          GHC.Base.Nothing)
                        (findKeyShare
                          (case extension_KeyShare (chExt b) of {
                            GHC.Base.Just kss -> kss;
                            GHC.Base.Nothing -> []}) serverGroups)}) (GHC.Base.Just
                    (ExistT __ (CloseWith ((,) I.AlertLevel_Fatal
                    I.HandshakeFailure))))
                    (chooseCipher (chCipherIDs b) serverCiphers)) (GHC.Base.Just
                  (ExistT __ (CloseWith ((,) I.AlertLevel_Fatal
                  I.ProtocolVersion))))
                  (case extension_SupportedVersionsCH (chExt b) of {
                    GHC.Base.Just vers ->
                     case inb version_beq tLS13 vers of {
                      GHC.Base.True -> GHC.Base.Just tLS13;
                      GHC.Base.False -> GHC.Base.Nothing};
                    GHC.Base.Nothing -> GHC.Base.Nothing})})
              (option_branch (\x1 -> GHC.Base.Just (ExistT __ (CloseWith x1)))
                GHC.Base.Nothing (retAlert r)) (fromRecvClientHello r))))))
        (sum_merge
          (prod_curry
            (prod_curry
              (prod_curry
                (prod_curry
                  (prod_curry
                    (prod_curry
                      (prod_curry
                        (prod_curry
                          (prod_curry (\_ c p b c0 c1 k l c2 _ _ r -> Prelude.Left
                            ((,)
                            (option_branch (\x1 ->
                              option_branch (\x2 ->
                                option_branch (\x3 ->
                                  case x3 of {
                                   (,) a b0 ->
                                    case a of {
                                     (,) a0 b1 ->
                                      option_branch (\x4 ->
                                        case inb pskKexMode_beq I.PSK_DHE_KE
                                               (case extension_PskKeyModes
                                                       (chExt c2) of {
                                                 GHC.Base.Just ms -> ms;
                                                 GHC.Base.Nothing -> []}) of {
                                         GHC.Base.True -> Prelude.Right
                                          (Prelude.Right (Prelude.Right
                                          (Prelude.Right (Prelude.Left ((,) ((,)
                                          ((,) ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                          ((,) ((,) ((,) () c) p) b) c0) c1) k) l)
                                          c2) x2) b0) a0) b1) x4)))));
                                         GHC.Base.False ->
                                          option_branch (\x5 ->
                                            option_branch (\_ -> Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Left ((,) ((,)
                                              ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                              ((,) ((,) ((,) () c) p) b) c0) c1) k)
                                              l) c2) x2)
                                              (b_replicate
                                                (hashDigestSize (cipherHash c1)) w0))
                                              x5) GHC.Base.Nothing))))))))))
                                              (option_branch (\x6 ->
                                                option_branch (\x7 -> Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Left ((,)
                                                  ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                                  ((,) ((,) ((,) ((,) () c) p) b)
                                                  c0) c1) k) l) c2) x2)
                                                  (b_replicate
                                                    (hashDigestSize (cipherHash c1))
                                                    w0)) x5) (GHC.Base.Just
                                                  x7))))))))))) (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Left ((,)
                                                  ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                                  ((,) ((,) ((,) ((,) () c) p) b)
                                                  c0) c1) k) l) c2) x2)
                                                  (b_replicate
                                                    (hashDigestSize (cipherHash c1))
                                                    w0)) GHC.Base.Nothing)
                                                  x5))))))))
                                                  (extensionDecode_SignatureAlgorithms
                                                    x6)) (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Left ((,) ((,) ((,) ((,)
                                                ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                                ((,) () c) p) b) c0) c1) k) l) c2)
                                                x2)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c1))
                                                  w0)) GHC.Base.Nothing) x5)))))))))
                                                (extensionLookup_SignatureAlgorithms
                                                  (chExt c2))) GHC.Base.Nothing)
                                            (Prelude.Right (Prelude.Left ()))
                                            (checkBinder b (cipherHash c1)
                                              (hkdfExtract (cipherHash c1)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c1))
                                                  w0)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c1))
                                                  w0)) GHC.Base.Nothing
                                              (hashDigestSize (cipherHash c1)))})
                                        (option_branch (\x4 ->
                                          option_branch (\_ -> Prelude.Right
                                            (Prelude.Right (Prelude.Right
                                            (Prelude.Right (Prelude.Right
                                            (Prelude.Right (Prelude.Right
                                            (Prelude.Right (Prelude.Left ((,) ((,)
                                            ((,) ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                            ((,) ((,) () c) p) b) c0) c1) k) l) c2)
                                            x2)
                                            (b_replicate
                                              (hashDigestSize (cipherHash c1)) w0))
                                            x4) GHC.Base.Nothing))))))))))
                                            (option_branch (\x5 ->
                                              option_branch (\x6 -> Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Left ((,)
                                                ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                                ((,) ((,) ((,) ((,) () c) p) b) c0)
                                                c1) k) l) c2) x2)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c1))
                                                  w0)) x4) (GHC.Base.Just
                                                x6))))))))))) (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Left ((,)
                                                ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                                ((,) ((,) ((,) ((,) () c) p) b) c0)
                                                c1) k) l) c2) x2)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c1))
                                                  w0)) GHC.Base.Nothing) x4))))))))
                                                (extensionDecode_SignatureAlgorithms
                                                  x5)) (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Left ((,) ((,)
                                              ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                              ((,) ((,) ((,) () c) p) b) c0) c1) k)
                                              l) c2) x2)
                                              (b_replicate
                                                (hashDigestSize (cipherHash c1)) w0))
                                              GHC.Base.Nothing) x4)))))))))
                                              (extensionLookup_SignatureAlgorithms
                                                (chExt c2))) GHC.Base.Nothing)
                                          (Prelude.Right (Prelude.Left ()))
                                          (checkBinder b (cipherHash c1)
                                            (hkdfExtract (cipherHash c1)
                                              (b_replicate
                                                (hashDigestSize (cipherHash c1)) w0)
                                              (b_replicate
                                                (hashDigestSize (cipherHash c1)) w0))
                                            GHC.Base.Nothing
                                            (hashDigestSize (cipherHash c1))))
                                        (hd_error b0)}})
                                  (option_branch (\x3 ->
                                    option_branch (\_ -> Prelude.Right
                                      (Prelude.Right (Prelude.Right (Prelude.Right
                                      (Prelude.Right (Prelude.Right (Prelude.Right
                                      (Prelude.Right (Prelude.Left ((,) ((,) ((,)
                                      ((,) ((,) ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                      () c) p) b) c0) c1) k) l) c2) x2)
                                      (b_replicate (hashDigestSize (cipherHash c1))
                                        w0)) x3) GHC.Base.Nothing))))))))))
                                      (option_branch (\x4 ->
                                        option_branch (\x5 -> Prelude.Right
                                          (Prelude.Right (Prelude.Right
                                          (Prelude.Right (Prelude.Right
                                          (Prelude.Right (Prelude.Right
                                          (Prelude.Right (Prelude.Left ((,) ((,)
                                          ((,) ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                          ((,) ((,) () c) p) b) c0) c1) k) l) c2)
                                          x2)
                                          (b_replicate
                                            (hashDigestSize (cipherHash c1)) w0))
                                          x3) (GHC.Base.Just x5)))))))))))
                                          (Prelude.Right (Prelude.Right
                                          (Prelude.Right (Prelude.Right
                                          (Prelude.Right (Prelude.Right
                                          (Prelude.Left ((,) ((,) ((,) ((,) ((,)
                                          ((,) ((,) ((,) ((,) ((,) ((,) ((,) () c)
                                          p) b) c0) c1) k) l) c2) x2)
                                          (b_replicate
                                            (hashDigestSize (cipherHash c1)) w0))
                                          GHC.Base.Nothing) x3))))))))
                                          (extensionDecode_SignatureAlgorithms x4))
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Left ((,) ((,) ((,)
                                        ((,) ((,) ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                        () c) p) b) c0) c1) k) l) c2) x2)
                                        (b_replicate
                                          (hashDigestSize (cipherHash c1)) w0))
                                        GHC.Base.Nothing) x3)))))))))
                                        (extensionLookup_SignatureAlgorithms
                                          (chExt c2))) GHC.Base.Nothing)
                                    (Prelude.Right (Prelude.Left ()))
                                    (checkBinder b (cipherHash c1)
                                      (hkdfExtract (cipherHash c1)
                                        (b_replicate
                                          (hashDigestSize (cipherHash c1)) w0)
                                        (b_replicate
                                          (hashDigestSize (cipherHash c1)) w0))
                                      GHC.Base.Nothing
                                      (hashDigestSize (cipherHash c1))))
                                  (extension_PreSharedKeyCH (chExt c2)))
                                (Prelude.Right (Prelude.Left ())) x1) (Prelude.Right
                              (Prelude.Right (Prelude.Right (Prelude.Right
                              (Prelude.Right (Prelude.Right (Prelude.Right
                              (Prelude.Right (Prelude.Right (Prelude.Right
                              (Prelude.Right (Prelude.Right (Prelude.Right
                              (Prelude.Right (Prelude.Right (Prelude.Right
                              (Prelude.Right (Prelude.Right (Prelude.Right
                              (Prelude.Right (Prelude.Right (Prelude.Right
                              (Prelude.Right (Prelude.Right (Prelude.Right
                              (Prelude.Right (Prelude.Right (Prelude.Right
                              (Prelude.Right (Prelude.Right
                              (inhabitant unit_inhabitant)))))))))))))))))))))))))))))))
                              (fromGroupGetPubShared r))
                            (option_branch (\x1 ->
                              option_branch (\_ ->
                                option_branch (\x2 ->
                                  case x2 of {
                                   (,) a b0 ->
                                    case a of {
                                     (,) a0 _ ->
                                      option_branch (\_ ->
                                        case inb pskKexMode_beq I.PSK_DHE_KE
                                               (case extension_PskKeyModes
                                                       (chExt c2) of {
                                                 GHC.Base.Just ms -> ms;
                                                 GHC.Base.Nothing -> []}) of {
                                         GHC.Base.True -> GHC.Base.Just (ExistT __
                                          (SessionResume (b2s a0)));
                                         GHC.Base.False ->
                                          option_branch (\_ ->
                                            option_branch (\_ -> GHC.Base.Just
                                              (ExistT __ (GetRandomBytes
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              0)))))))))))))))))))))))))))))))))))
                                              (option_branch (\x3 ->
                                                option_branch (\_ -> GHC.Base.Just
                                                  (ExistT __ (GetRandomBytes
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  0)))))))))))))))))))))))))))))))))))
                                                  (GHC.Base.Just (ExistT __
                                                  (CloseWith ((,) I.AlertLevel_Fatal
                                                  I.DecodeError))))
                                                  (extensionDecode_SignatureAlgorithms
                                                    x3)) (GHC.Base.Just (ExistT __
                                                (CloseWith ((,) I.AlertLevel_Fatal
                                                I.MissingExtension))))
                                                (extensionLookup_SignatureAlgorithms
                                                  (chExt c2))) GHC.Base.Nothing)
                                            (GHC.Base.Just (ExistT __ (CloseWith
                                            ((,) I.AlertLevel_Fatal
                                            I.DecryptError))))
                                            (checkBinder b (cipherHash c1)
                                              (hkdfExtract (cipherHash c1)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c1))
                                                  w0)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c1))
                                                  w0)) GHC.Base.Nothing
                                              (hashDigestSize (cipherHash c1)))})
                                        (option_branch (\_ ->
                                          option_branch (\_ -> GHC.Base.Just (ExistT
                                            __ (GetRandomBytes ((Prelude.+) 1
                                            ((Prelude.+) 1 ((Prelude.+) 1
                                            ((Prelude.+) 1 ((Prelude.+) 1
                                            ((Prelude.+) 1 ((Prelude.+) 1
                                            ((Prelude.+) 1 ((Prelude.+) 1
                                            ((Prelude.+) 1 ((Prelude.+) 1
                                            ((Prelude.+) 1 ((Prelude.+) 1
                                            ((Prelude.+) 1 ((Prelude.+) 1
                                            ((Prelude.+) 1 ((Prelude.+) 1
                                            ((Prelude.+) 1 ((Prelude.+) 1
                                            ((Prelude.+) 1 ((Prelude.+) 1
                                            ((Prelude.+) 1 ((Prelude.+) 1
                                            ((Prelude.+) 1 ((Prelude.+) 1
                                            ((Prelude.+) 1 ((Prelude.+) 1
                                            ((Prelude.+) 1 ((Prelude.+) 1
                                            ((Prelude.+) 1 ((Prelude.+) 1
                                            ((Prelude.+) 1
                                            0)))))))))))))))))))))))))))))))))))
                                            (option_branch (\x3 ->
                                              option_branch (\_ -> GHC.Base.Just
                                                (ExistT __ (GetRandomBytes
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                0)))))))))))))))))))))))))))))))))))
                                                (GHC.Base.Just (ExistT __ (CloseWith
                                                ((,) I.AlertLevel_Fatal
                                                I.DecodeError))))
                                                (extensionDecode_SignatureAlgorithms
                                                  x3)) (GHC.Base.Just (ExistT __
                                              (CloseWith ((,) I.AlertLevel_Fatal
                                              I.MissingExtension))))
                                              (extensionLookup_SignatureAlgorithms
                                                (chExt c2))) GHC.Base.Nothing)
                                          (GHC.Base.Just (ExistT __ (CloseWith ((,)
                                          I.AlertLevel_Fatal I.DecryptError))))
                                          (checkBinder b (cipherHash c1)
                                            (hkdfExtract (cipherHash c1)
                                              (b_replicate
                                                (hashDigestSize (cipherHash c1)) w0)
                                              (b_replicate
                                                (hashDigestSize (cipherHash c1)) w0))
                                            GHC.Base.Nothing
                                            (hashDigestSize (cipherHash c1))))
                                        (hd_error b0)}})
                                  (option_branch (\_ ->
                                    option_branch (\_ -> GHC.Base.Just (ExistT __
                                      (GetRandomBytes ((Prelude.+) 1 ((Prelude.+) 1
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
                                      0)))))))))))))))))))))))))))))))))))
                                      (option_branch (\x2 ->
                                        option_branch (\_ -> GHC.Base.Just (ExistT
                                          __ (GetRandomBytes ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1
                                          0)))))))))))))))))))))))))))))))))))
                                          (GHC.Base.Just (ExistT __ (CloseWith ((,)
                                          I.AlertLevel_Fatal I.DecodeError))))
                                          (extensionDecode_SignatureAlgorithms x2))
                                        (GHC.Base.Just (ExistT __ (CloseWith ((,)
                                        I.AlertLevel_Fatal I.MissingExtension))))
                                        (extensionLookup_SignatureAlgorithms
                                          (chExt c2))) GHC.Base.Nothing)
                                    (GHC.Base.Just (ExistT __ (CloseWith ((,)
                                    I.AlertLevel_Fatal I.DecryptError))))
                                    (checkBinder b (cipherHash c1)
                                      (hkdfExtract (cipherHash c1)
                                        (b_replicate
                                          (hashDigestSize (cipherHash c1)) w0)
                                        (b_replicate
                                          (hashDigestSize (cipherHash c1)) w0))
                                      GHC.Base.Nothing
                                      (hashDigestSize (cipherHash c1))))
                                  (extension_PreSharedKeyCH (chExt c2)))
                                (GHC.Base.Just (ExistT __ (CloseWith ((,)
                                I.AlertLevel_Fatal I.IllegalParameter)))) x1)
                              GHC.Base.Nothing (fromGroupGetPubShared r)))))))))))))
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
                                (prod_curry
                                  (prod_curry
                                    (prod_curry
                                      (\_ c p b c0 c1 k l c2 p0 l0 _ w b0 _ r ->
                                      Prelude.Left ((,)
                                      (option_branch (\x1 ->
                                        option_branch (\x2 ->
                                          option_branch (\x3 -> Prelude.Right
                                            (Prelude.Right (Prelude.Right
                                            (Prelude.Right (Prelude.Right
                                            (Prelude.Left ((,) ((,) ((,) ((,) ((,)
                                            ((,) ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                            ((,) () c) p) b) c0) c1) k) l) c2) p0)
                                            l0) w) b0) x2) x3)))))))
                                            (option_branch (\x3 ->
                                              option_branch (\_ -> Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Left ((,)
                                                ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                                ((,) ((,) ((,) ((,) () c) p) b) c0)
                                                c1) k) l) c2) p0)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c1))
                                                  w0)) x3)
                                                GHC.Base.Nothing))))))))))
                                                (option_branch (\x4 ->
                                                  option_branch (\x5 ->
                                                    Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Left ((,) ((,) ((,)
                                                    ((,) ((,) ((,) ((,) ((,) ((,)
                                                    ((,) ((,) ((,) () c) p) b) c0)
                                                    c1) k) l) c2) p0)
                                                    (b_replicate
                                                      (hashDigestSize
                                                        (cipherHash c1)) w0)) x3)
                                                    (GHC.Base.Just x5)))))))))))
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Left ((,) ((,) ((,)
                                                    ((,) ((,) ((,) ((,) ((,) ((,)
                                                    ((,) ((,) ((,) () c) p) b) c0)
                                                    c1) k) l) c2) p0)
                                                    (b_replicate
                                                      (hashDigestSize
                                                        (cipherHash c1)) w0))
                                                    GHC.Base.Nothing) x3))))))))
                                                    (extensionDecode_SignatureAlgorithms
                                                      x4)) (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Left ((,) ((,) ((,) ((,)
                                                  ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                                  ((,) () c) p) b) c0) c1) k) l) c2)
                                                  p0)
                                                  (b_replicate
                                                    (hashDigestSize (cipherHash c1))
                                                    w0)) GHC.Base.Nothing)
                                                  x3)))))))))
                                                  (extensionLookup_SignatureAlgorithms
                                                    (chExt c2))) GHC.Base.Nothing)
                                              (Prelude.Right (Prelude.Left ()))
                                              (checkBinder b (cipherHash c1)
                                                (hkdfExtract (cipherHash c1)
                                                  (b_replicate
                                                    (hashDigestSize (cipherHash c1))
                                                    w0)
                                                  (b_replicate
                                                    (hashDigestSize (cipherHash c1))
                                                    w0)) GHC.Base.Nothing
                                                (hashDigestSize (cipherHash c1))))
                                            (sessionTicketInfo x2))
                                          (option_branch (\x2 ->
                                            option_branch (\_ -> Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Left ((,) ((,)
                                              ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                              ((,) ((,) ((,) () c) p) b) c0) c1) k)
                                              l) c2) p0)
                                              (b_replicate
                                                (hashDigestSize (cipherHash c1)) w0))
                                              x2) GHC.Base.Nothing))))))))))
                                              (option_branch (\x3 ->
                                                option_branch (\x4 -> Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Left ((,)
                                                  ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                                  ((,) ((,) ((,) ((,) () c) p) b)
                                                  c0) c1) k) l) c2) p0)
                                                  (b_replicate
                                                    (hashDigestSize (cipherHash c1))
                                                    w0)) x2) (GHC.Base.Just
                                                  x4))))))))))) (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Left ((,)
                                                  ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                                  ((,) ((,) ((,) ((,) () c) p) b)
                                                  c0) c1) k) l) c2) p0)
                                                  (b_replicate
                                                    (hashDigestSize (cipherHash c1))
                                                    w0)) GHC.Base.Nothing)
                                                  x2))))))))
                                                  (extensionDecode_SignatureAlgorithms
                                                    x3)) (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Left ((,) ((,) ((,) ((,)
                                                ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                                ((,) () c) p) b) c0) c1) k) l) c2)
                                                p0)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c1))
                                                  w0)) GHC.Base.Nothing) x2)))))))))
                                                (extensionLookup_SignatureAlgorithms
                                                  (chExt c2))) GHC.Base.Nothing)
                                            (Prelude.Right (Prelude.Left ()))
                                            (checkBinder b (cipherHash c1)
                                              (hkdfExtract (cipherHash c1)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c1))
                                                  w0)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c1))
                                                  w0)) GHC.Base.Nothing
                                              (hashDigestSize (cipherHash c1)))) x1)
                                        (case inhabitant
                                                (prod_inhabitant
                                                  (prod_inhabitant
                                                    byteString_inhabitant
                                                    option_inhabitant)
                                                  bool_inhabitant) of {
                                          (,) a _ ->
                                           case a of {
                                            (,) a0 b1 ->
                                             option_branch (\x1 ->
                                               option_branch (\_ -> Prelude.Right
                                                 (Prelude.Right (Prelude.Right
                                                 (Prelude.Right (Prelude.Right
                                                 (Prelude.Right (Prelude.Right
                                                 (Prelude.Right (Prelude.Left ((,)
                                                 ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                                 ((,) ((,) ((,) ((,) () c) p) b) c0)
                                                 c1) k) l) c2) p0) a0) x1)
                                                 GHC.Base.Nothing))))))))))
                                                 (option_branch (\x2 ->
                                                   option_branch (\x3 ->
                                                     Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Left ((,) ((,) ((,)
                                                     ((,) ((,) ((,) ((,) ((,) ((,)
                                                     ((,) ((,) ((,) () c) p) b) c0)
                                                     c1) k) l) c2) p0) a0) x1)
                                                     (GHC.Base.Just x3)))))))))))
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Left ((,) ((,) ((,)
                                                     ((,) ((,) ((,) ((,) ((,) ((,)
                                                     ((,) ((,) ((,) () c) p) b) c0)
                                                     c1) k) l) c2) p0) a0) b1)
                                                     x1))))))))
                                                     (extensionDecode_SignatureAlgorithms
                                                       x2)) (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Right (Prelude.Right
                                                   (Prelude.Left ((,) ((,) ((,) ((,)
                                                   ((,) ((,) ((,) ((,) ((,) ((,)
                                                   ((,) ((,) () c) p) b) c0) c1) k)
                                                   l) c2) p0) a0) b1) x1)))))))))
                                                   (extensionLookup_SignatureAlgorithms
                                                     (chExt c2))) b1) (Prelude.Right
                                               (Prelude.Left ()))
                                               (checkBinder b (cipherHash c1)
                                                 (hkdfExtract (cipherHash c1)
                                                   (b_replicate
                                                     (hashDigestSize
                                                       (cipherHash c1)) w0) a0) b1
                                                 (hashDigestSize (cipherHash c1)))}})
                                        (fromSessionResume r))
                                      (option_branch (\x1 ->
                                        option_branch (\x2 ->
                                          option_branch (\_ -> GHC.Base.Just (ExistT
                                            __ (GetCurrentTime ())))
                                            (option_branch (\_ ->
                                              option_branch (\_ -> GHC.Base.Just
                                                (ExistT __ (GetRandomBytes
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                ((Prelude.+) 1 ((Prelude.+) 1
                                                0)))))))))))))))))))))))))))))))))))
                                                (option_branch (\x3 ->
                                                  option_branch (\_ -> GHC.Base.Just
                                                    (ExistT __ (GetRandomBytes
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    0)))))))))))))))))))))))))))))))))))
                                                    (GHC.Base.Just (ExistT __
                                                    (CloseWith ((,)
                                                    I.AlertLevel_Fatal
                                                    I.DecodeError))))
                                                    (extensionDecode_SignatureAlgorithms
                                                      x3)) (GHC.Base.Just (ExistT __
                                                  (CloseWith ((,) I.AlertLevel_Fatal
                                                  I.MissingExtension))))
                                                  (extensionLookup_SignatureAlgorithms
                                                    (chExt c2))) GHC.Base.Nothing)
                                              (GHC.Base.Just (ExistT __ (CloseWith
                                              ((,) I.AlertLevel_Fatal
                                              I.DecryptError))))
                                              (checkBinder b (cipherHash c1)
                                                (hkdfExtract (cipherHash c1)
                                                  (b_replicate
                                                    (hashDigestSize (cipherHash c1))
                                                    w0)
                                                  (b_replicate
                                                    (hashDigestSize (cipherHash c1))
                                                    w0)) GHC.Base.Nothing
                                                (hashDigestSize (cipherHash c1))))
                                            (sessionTicketInfo x2))
                                          (option_branch (\_ ->
                                            option_branch (\_ -> GHC.Base.Just
                                              (ExistT __ (GetRandomBytes
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              ((Prelude.+) 1 ((Prelude.+) 1
                                              0)))))))))))))))))))))))))))))))))))
                                              (option_branch (\x2 ->
                                                option_branch (\_ -> GHC.Base.Just
                                                  (ExistT __ (GetRandomBytes
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  0)))))))))))))))))))))))))))))))))))
                                                  (GHC.Base.Just (ExistT __
                                                  (CloseWith ((,) I.AlertLevel_Fatal
                                                  I.DecodeError))))
                                                  (extensionDecode_SignatureAlgorithms
                                                    x2)) (GHC.Base.Just (ExistT __
                                                (CloseWith ((,) I.AlertLevel_Fatal
                                                I.MissingExtension))))
                                                (extensionLookup_SignatureAlgorithms
                                                  (chExt c2))) GHC.Base.Nothing)
                                            (GHC.Base.Just (ExistT __ (CloseWith
                                            ((,) I.AlertLevel_Fatal
                                            I.DecryptError))))
                                            (checkBinder b (cipherHash c1)
                                              (hkdfExtract (cipherHash c1)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c1))
                                                  w0)
                                                (b_replicate
                                                  (hashDigestSize (cipherHash c1))
                                                  w0)) GHC.Base.Nothing
                                              (hashDigestSize (cipherHash c1)))) x1)
                                        (case inhabitant
                                                (prod_inhabitant
                                                  (prod_inhabitant
                                                    byteString_inhabitant
                                                    option_inhabitant)
                                                  bool_inhabitant) of {
                                          (,) a _ ->
                                           case a of {
                                            (,) a0 b1 ->
                                             option_branch (\_ ->
                                               option_branch (\_ -> GHC.Base.Just
                                                 (ExistT __ (GetRandomBytes
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 ((Prelude.+) 1 ((Prelude.+) 1
                                                 0)))))))))))))))))))))))))))))))))))
                                                 (option_branch (\x1 ->
                                                   option_branch (\_ ->
                                                     GHC.Base.Just (ExistT __
                                                     (GetRandomBytes ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1
                                                     0)))))))))))))))))))))))))))))))))))
                                                     (GHC.Base.Just (ExistT __
                                                     (CloseWith ((,)
                                                     I.AlertLevel_Fatal
                                                     I.DecodeError))))
                                                     (extensionDecode_SignatureAlgorithms
                                                       x1)) (GHC.Base.Just (ExistT
                                                   __ (CloseWith ((,)
                                                   I.AlertLevel_Fatal
                                                   I.MissingExtension))))
                                                   (extensionLookup_SignatureAlgorithms
                                                     (chExt c2))) b1) (GHC.Base.Just
                                               (ExistT __ (CloseWith ((,)
                                               I.AlertLevel_Fatal I.DecryptError))))
                                               (checkBinder b (cipherHash c1)
                                                 (hkdfExtract (cipherHash c1)
                                                   (b_replicate
                                                     (hashDigestSize
                                                       (cipherHash c1)) w0) a0) b1
                                                 (hashDigestSize (cipherHash c1)))}})
                                        (fromSessionResume r)))))))))))))))))
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
                                  (prod_curry
                                    (prod_curry
                                      (prod_curry
                                        (prod_curry
                                          (\_ c p b c0 c1 k l c2 p0 l0 w b0 s t _ r ->
                                          Prelude.Left ((,)
                                          (option_branch (\x1 ->
                                            case andb
                                                   (case find0 (\c3 ->
                                                           cipherID_beq
                                                             (cipherID c3)
                                                             (sessionCipher s))
                                                           serverCiphers of {
                                                     GHC.Base.Just c3 ->
                                                      hash_beq (cipherHash c3)
                                                        (cipherHash c1);
                                                     GHC.Base.Nothing ->
                                                      GHC.Base.False})
                                                   (checkFreshness t w x1) of {
                                             GHC.Base.True ->
                                              option_branch (\x2 ->
                                                option_branch (\_ -> Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Left ((,)
                                                  ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                                  ((,) ((,) ((,) ((,) () c) p) b)
                                                  c0) c1) k) l) c2) p0)
                                                  (sessionSecret s)) x2)
                                                  GHC.Base.Nothing))))))))))
                                                  (option_branch (\x3 ->
                                                    option_branch (\x4 ->
                                                      Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Left ((,) ((,) ((,)
                                                      ((,) ((,) ((,) ((,) ((,) ((,)
                                                      ((,) ((,) ((,) () c) p) b) c0)
                                                      c1) k) l) c2) p0)
                                                      (sessionSecret s)) x2)
                                                      (GHC.Base.Just x4)))))))))))
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Left ((,) ((,) ((,)
                                                      ((,) ((,) ((,) ((,) ((,) ((,)
                                                      ((,) ((,) ((,) () c) p) b) c0)
                                                      c1) k) l) c2) p0)
                                                      (sessionSecret s))
                                                      (GHC.Base.Just ((,) ((,) b0 0)
                                                      (add
                                                        (sumnat
                                                          (map (\x4 ->
                                                            add (blength x4)
                                                              ((Prelude.+) 1 0)) l0))
                                                        ((Prelude.+) 1
                                                        ((Prelude.+) 1 0))))))
                                                      x2))))))))
                                                      (extensionDecode_SignatureAlgorithms
                                                        x3)) (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Left ((,) ((,) ((,)
                                                    ((,) ((,) ((,) ((,) ((,) ((,)
                                                    ((,) ((,) ((,) () c) p) b) c0)
                                                    c1) k) l) c2) p0)
                                                    (sessionSecret s))
                                                    (GHC.Base.Just ((,) ((,) b0 0)
                                                    (add
                                                      (sumnat
                                                        (map (\x3 ->
                                                          add (blength x3)
                                                            ((Prelude.+) 1 0)) l0))
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      0)))))) x2)))))))))
                                                    (extensionLookup_SignatureAlgorithms
                                                      (chExt c2))) (GHC.Base.Just
                                                  ((,) ((,) b0 0)
                                                  (add
                                                    (sumnat
                                                      (map (\x3 ->
                                                        add (blength x3)
                                                          ((Prelude.+) 1 0)) l0))
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    0)))))) (Prelude.Right
                                                (Prelude.Left ()))
                                                (checkBinder b (cipherHash c1)
                                                  (hkdfExtract (cipherHash c1)
                                                    (b_replicate
                                                      (hashDigestSize
                                                        (cipherHash c1)) w0)
                                                    (sessionSecret s))
                                                  (GHC.Base.Just ((,) ((,) b0 0)
                                                  (add
                                                    (sumnat
                                                      (map (\x2 ->
                                                        add (blength x2)
                                                          ((Prelude.+) 1 0)) l0))
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    0)))))
                                                  (hashDigestSize (cipherHash c1)));
                                             GHC.Base.False ->
                                              option_branch (\x2 ->
                                                option_branch (\_ -> Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Left ((,)
                                                  ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                                  ((,) ((,) ((,) ((,) () c) p) b)
                                                  c0) c1) k) l) c2) p0)
                                                  (b_replicate
                                                    (hashDigestSize (cipherHash c1))
                                                    w0)) x2)
                                                  GHC.Base.Nothing))))))))))
                                                  (option_branch (\x3 ->
                                                    option_branch (\x4 ->
                                                      Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Left ((,) ((,) ((,)
                                                      ((,) ((,) ((,) ((,) ((,) ((,)
                                                      ((,) ((,) ((,) () c) p) b) c0)
                                                      c1) k) l) c2) p0)
                                                      (b_replicate
                                                        (hashDigestSize
                                                          (cipherHash c1)) w0)) x2)
                                                      (GHC.Base.Just x4)))))))))))
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Left ((,) ((,) ((,)
                                                      ((,) ((,) ((,) ((,) ((,) ((,)
                                                      ((,) ((,) ((,) () c) p) b) c0)
                                                      c1) k) l) c2) p0)
                                                      (b_replicate
                                                        (hashDigestSize
                                                          (cipherHash c1)) w0))
                                                      GHC.Base.Nothing) x2))))))))
                                                      (extensionDecode_SignatureAlgorithms
                                                        x3)) (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Left ((,) ((,) ((,)
                                                    ((,) ((,) ((,) ((,) ((,) ((,)
                                                    ((,) ((,) ((,) () c) p) b) c0)
                                                    c1) k) l) c2) p0)
                                                    (b_replicate
                                                      (hashDigestSize
                                                        (cipherHash c1)) w0))
                                                    GHC.Base.Nothing) x2)))))))))
                                                    (extensionLookup_SignatureAlgorithms
                                                      (chExt c2))) GHC.Base.Nothing)
                                                (Prelude.Right (Prelude.Left ()))
                                                (checkBinder b (cipherHash c1)
                                                  (hkdfExtract (cipherHash c1)
                                                    (b_replicate
                                                      (hashDigestSize
                                                        (cipherHash c1)) w0)
                                                    (b_replicate
                                                      (hashDigestSize
                                                        (cipherHash c1)) w0))
                                                  GHC.Base.Nothing
                                                  (hashDigestSize (cipherHash c1)))})
                                            (case inhabitant
                                                    (prod_inhabitant
                                                      (prod_inhabitant
                                                        byteString_inhabitant
                                                        option_inhabitant)
                                                      bool_inhabitant) of {
                                              (,) a _ ->
                                               case a of {
                                                (,) a0 b1 ->
                                                 option_branch (\x1 ->
                                                   option_branch (\_ ->
                                                     Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Left ((,) ((,) ((,)
                                                     ((,) ((,) ((,) ((,) ((,) ((,)
                                                     ((,) ((,) ((,) () c) p) b) c0)
                                                     c1) k) l) c2) p0) a0) x1)
                                                     GHC.Base.Nothing))))))))))
                                                     (option_branch (\x2 ->
                                                       option_branch (\x3 ->
                                                         Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Left ((,) ((,)
                                                         ((,) ((,) ((,) ((,) ((,)
                                                         ((,) ((,) ((,) ((,) ((,) ()
                                                         c) p) b) c0) c1) k) l) c2)
                                                         p0) a0) x1) (GHC.Base.Just
                                                         x3)))))))))))
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Right
                                                         (Prelude.Left ((,) ((,)
                                                         ((,) ((,) ((,) ((,) ((,)
                                                         ((,) ((,) ((,) ((,) ((,) ()
                                                         c) p) b) c0) c1) k) l) c2)
                                                         p0) a0) b1) x1))))))))
                                                         (extensionDecode_SignatureAlgorithms
                                                           x2)) (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Left ((,) ((,) ((,)
                                                       ((,) ((,) ((,) ((,) ((,) ((,)
                                                       ((,) ((,) ((,) () c) p) b)
                                                       c0) c1) k) l) c2) p0) a0) b1)
                                                       x1)))))))))
                                                       (extensionLookup_SignatureAlgorithms
                                                         (chExt c2))) b1)
                                                   (Prelude.Right (Prelude.Left ()))
                                                   (checkBinder b (cipherHash c1)
                                                     (hkdfExtract (cipherHash c1)
                                                       (b_replicate
                                                         (hashDigestSize
                                                           (cipherHash c1)) w0) a0)
                                                     b1
                                                     (hashDigestSize
                                                       (cipherHash c1)))}})
                                            (fromGetCurrentTime r))
                                          (option_branch (\x1 ->
                                            case andb
                                                   (case find0 (\c3 ->
                                                           cipherID_beq
                                                             (cipherID c3)
                                                             (sessionCipher s))
                                                           serverCiphers of {
                                                     GHC.Base.Just c3 ->
                                                      hash_beq (cipherHash c3)
                                                        (cipherHash c1);
                                                     GHC.Base.Nothing ->
                                                      GHC.Base.False})
                                                   (checkFreshness t w x1) of {
                                             GHC.Base.True ->
                                              option_branch (\_ ->
                                                option_branch (\_ -> GHC.Base.Just
                                                  (ExistT __ (GetRandomBytes
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  0)))))))))))))))))))))))))))))))))))
                                                  (option_branch (\x2 ->
                                                    option_branch (\_ ->
                                                      GHC.Base.Just (ExistT __
                                                      (GetRandomBytes ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1
                                                      0)))))))))))))))))))))))))))))))))))
                                                      (GHC.Base.Just (ExistT __
                                                      (CloseWith ((,)
                                                      I.AlertLevel_Fatal
                                                      I.DecodeError))))
                                                      (extensionDecode_SignatureAlgorithms
                                                        x2)) (GHC.Base.Just (ExistT
                                                    __ (CloseWith ((,)
                                                    I.AlertLevel_Fatal
                                                    I.MissingExtension))))
                                                    (extensionLookup_SignatureAlgorithms
                                                      (chExt c2))) (GHC.Base.Just
                                                  ((,) ((,) b0 0)
                                                  (add
                                                    (sumnat
                                                      (map (\x2 ->
                                                        add (blength x2)
                                                          ((Prelude.+) 1 0)) l0))
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    0)))))) (GHC.Base.Just (ExistT
                                                __ (CloseWith ((,)
                                                I.AlertLevel_Fatal
                                                I.DecryptError))))
                                                (checkBinder b (cipherHash c1)
                                                  (hkdfExtract (cipherHash c1)
                                                    (b_replicate
                                                      (hashDigestSize
                                                        (cipherHash c1)) w0)
                                                    (sessionSecret s))
                                                  (GHC.Base.Just ((,) ((,) b0 0)
                                                  (add
                                                    (sumnat
                                                      (map (\x2 ->
                                                        add (blength x2)
                                                          ((Prelude.+) 1 0)) l0))
                                                    ((Prelude.+) 1 ((Prelude.+) 1
                                                    0)))))
                                                  (hashDigestSize (cipherHash c1)));
                                             GHC.Base.False ->
                                              option_branch (\_ ->
                                                option_branch (\_ -> GHC.Base.Just
                                                  (ExistT __ (GetRandomBytes
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  ((Prelude.+) 1 ((Prelude.+) 1
                                                  0)))))))))))))))))))))))))))))))))))
                                                  (option_branch (\x2 ->
                                                    option_branch (\_ ->
                                                      GHC.Base.Just (ExistT __
                                                      (GetRandomBytes ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1 ((Prelude.+) 1
                                                      ((Prelude.+) 1
                                                      0)))))))))))))))))))))))))))))))))))
                                                      (GHC.Base.Just (ExistT __
                                                      (CloseWith ((,)
                                                      I.AlertLevel_Fatal
                                                      I.DecodeError))))
                                                      (extensionDecode_SignatureAlgorithms
                                                        x2)) (GHC.Base.Just (ExistT
                                                    __ (CloseWith ((,)
                                                    I.AlertLevel_Fatal
                                                    I.MissingExtension))))
                                                    (extensionLookup_SignatureAlgorithms
                                                      (chExt c2))) GHC.Base.Nothing)
                                                (GHC.Base.Just (ExistT __ (CloseWith
                                                ((,) I.AlertLevel_Fatal
                                                I.DecryptError))))
                                                (checkBinder b (cipherHash c1)
                                                  (hkdfExtract (cipherHash c1)
                                                    (b_replicate
                                                      (hashDigestSize
                                                        (cipherHash c1)) w0)
                                                    (b_replicate
                                                      (hashDigestSize
                                                        (cipherHash c1)) w0))
                                                  GHC.Base.Nothing
                                                  (hashDigestSize (cipherHash c1)))})
                                            (case inhabitant
                                                    (prod_inhabitant
                                                      (prod_inhabitant
                                                        byteString_inhabitant
                                                        option_inhabitant)
                                                      bool_inhabitant) of {
                                              (,) a _ ->
                                               case a of {
                                                (,) a0 b1 ->
                                                 option_branch (\_ ->
                                                   option_branch (\_ ->
                                                     GHC.Base.Just (ExistT __
                                                     (GetRandomBytes ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1 ((Prelude.+) 1
                                                     ((Prelude.+) 1
                                                     0)))))))))))))))))))))))))))))))))))
                                                     (option_branch (\x1 ->
                                                       option_branch (\_ ->
                                                         GHC.Base.Just (ExistT __
                                                         (GetRandomBytes
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         ((Prelude.+) 1
                                                         0)))))))))))))))))))))))))))))))))))
                                                         (GHC.Base.Just (ExistT __
                                                         (CloseWith ((,)
                                                         I.AlertLevel_Fatal
                                                         I.DecodeError))))
                                                         (extensionDecode_SignatureAlgorithms
                                                           x1)) (GHC.Base.Just
                                                       (ExistT __ (CloseWith ((,)
                                                       I.AlertLevel_Fatal
                                                       I.MissingExtension))))
                                                       (extensionLookup_SignatureAlgorithms
                                                         (chExt c2))) b1)
                                                   (GHC.Base.Just (ExistT __
                                                   (CloseWith ((,)
                                                   I.AlertLevel_Fatal
                                                   I.DecryptError))))
                                                   (checkBinder b (cipherHash c1)
                                                     (hkdfExtract (cipherHash c1)
                                                       (b_replicate
                                                         (hashDigestSize
                                                           (cipherHash c1)) w0) a0)
                                                     b1
                                                     (hashDigestSize
                                                       (cipherHash c1)))}})
                                            (fromGetCurrentTime r))))))))))))))))))
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
                                    (prod_curry
                                      (prod_curry
                                        (\_ c p b c0 c1 k l c2 p0 b0 _ l0 _ _ ->
                                        Prelude.Left ((,) (Prelude.Right
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Left ((,) ((,) ((,)
                                        ((,) ((,) ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                        () c) p) b) c0) c1) k) l) c2) p0) b0) l0)
                                        GHC.Base.Nothing)))))))))) (GHC.Base.Just
                                        (ExistT __ (GetRandomBytes ((Prelude.+) 1
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
                                        ((Prelude.+) 1
                                        0)))))))))))))))))))))))))))))))))))))))))))))))))
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
                                      (prod_curry
                                        (prod_curry
                                          (\_ c p b c0 c1 k l c2 p0 b0 _ l0 _ _ ->
                                          Prelude.Left ((,) (Prelude.Right
                                          (Prelude.Right (Prelude.Right
                                          (Prelude.Right (Prelude.Right
                                          (Prelude.Right (Prelude.Right
                                          (Prelude.Right (Prelude.Left ((,) ((,)
                                          ((,) ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                          ((,) ((,) () c) p) b) c0) c1) k) l) c2)
                                          p0) b0) l0) GHC.Base.Nothing))))))))))
                                          (GHC.Base.Just (ExistT __ (GetRandomBytes
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          ((Prelude.+) 1 ((Prelude.+) 1
                                          0)))))))))))))))))))))))))))))))))))))))))))))))))
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
                                        (prod_curry
                                          (prod_curry
                                            (\_ c p b c0 c1 k l c2 p0 b0 l0 o _ r ->
                                            Prelude.Left ((,)
                                            (option_branch (\x1 -> Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Left ((,) ((,) ((,) ((,) ((,)
                                              ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                              ((,) () c) p) b) c0) c1) k) l) c2) p0)
                                              b0) l0) o) x1)))))))))))
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (inhabitant unit_inhabitant)))))))))))))))))))))))))))))))
                                              (fromGetRandomBytes r))
                                            (option_branch (\x1 -> GHC.Base.Just
                                              (ExistT __ (SendPacket (I.Handshake13
                                              ((:) (I.ServerHello13 (I.ServerRandom
                                              x1) (chSess c0) (cipherID c1) ((:)
                                              (extensionRaw_KeyShare
                                                (extensionEncode_KeyShare
                                                  (I.KeyShareEntry (ksGroup k)
                                                  (encodeGroupPublic (fst p0)))))
                                              ((:)
                                              (extensionRaw_SupportedVersions
                                                (extensionEncode_SupportedVersions
                                                  tLS13)) l0))) [])))))
                                              GHC.Base.Nothing
                                              (fromGetRandomBytes r))))))))))))))))
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
                                          (prod_curry
                                            (prod_curry
                                              (prod_curry
                                                (\_ c p b _ c0 _ l c1 p0 b0 _ o _ _ r ->
                                                Prelude.Left ((,)
                                                (option_branch (\x1 -> Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Left ((,)
                                                  ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                                  ((,) ((,) () c) p) b) c0) l) c1)
                                                  p0) b0) o) x1))))))))))))
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (inhabitant unit_inhabitant)))))))))))))))))))))))))))))))
                                                  (fromSendPacket r))
                                                (option_branch (\_ -> GHC.Base.Just
                                                  (ExistT __ (SendPacket
                                                  I.ChangeCipherSpec13)))
                                                  GHC.Base.Nothing
                                                  (fromSendPacket r)))))))))))))))))
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
                                            (\_ c p b c0 l c1 p0 b0 o b1 _ r ->
                                            Prelude.Left ((,)
                                            (option_branch (\_ -> Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Left ((,) ((,) ((,) ((,) ((,)
                                              ((,) ((,) ((,) ((,) ((,) () c) p) b)
                                              c0) l) c1) p0) b0) o) b1)))))))))))))
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (inhabitant unit_inhabitant)))))))))))))))))))))))))))))))
                                              (fromSendPacket r))
                                            (option_branch (\_ -> GHC.Base.Just
                                              (ExistT __ (SetSecret ((,) ((,) ((,)
                                              (cipherHash c0) c0)
                                              (hkdfExpandLabel (cipherHash c0)
                                                (hkdfExtract (cipherHash c0)
                                                  (hkdfExpandLabel (cipherHash c0)
                                                    (hkdfExtract (cipherHash c0)
                                                      (b_replicate
                                                        (hashDigestSize
                                                          (cipherHash c0)) w0) b0)
                                                    (s2b ((:) 'd' ((:) 'e' ((:) 'r'
                                                      ((:) 'i' ((:) 'v' ((:) 'e'
                                                      ((:) 'd' ([])))))))))
                                                    (hashWith (cipherHash c0) ((:)
                                                      (s2b ([])) []))
                                                    (hashDigestSize (cipherHash c0)))
                                                  (ba_convert (snd p0)))
                                                (s2b ((:) 's' ((:) ' ' ((:) 'h' ((:)
                                                  's' ((:) ' ' ((:) 't' ((:) 'r'
                                                  ((:) 'a' ((:) 'f' ((:) 'f' ((:)
                                                  'i' ((:) 'c' ([]))))))))))))))
                                                (hashWith (cipherHash c0) ((:) b
                                                  ((:) b1 [])))
                                                (hashDigestSize (cipherHash c0))))
                                              GHC.Base.False)))) GHC.Base.Nothing
                                              (fromSendPacket r))))))))))))))
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
                                              (\_ c p b c0 l c1 p0 b0 o b1 _ _ ->
                                              Prelude.Left ((,) (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Left ((,) ((,)
                                              ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                              ((,) () c) p) b) c0) l) c1) p0) b0) o)
                                              b1)))))))))))))) (GHC.Base.Just
                                              (ExistT __ (SendPacket (I.Handshake13
                                              ((:) (I.EncryptedExtensions13
                                              (case chooseServerName (chExt c1) of {
                                                GHC.Base.Just _ -> (:) sniExt [];
                                                GHC.Base.Nothing -> []})) [])))))))))))))))))
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
                                                (\_ c p b c0 l _ p0 b0 o b1 _ r ->
                                                Prelude.Left ((,)
                                                (option_branch (\x1 ->
                                                  option_branch (\x2 ->
                                                    option_branch (\x3 ->
                                                      case x3 of {
                                                       (,) a b2 -> Prelude.Right
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
                                                        (Prelude.Right (Prelude.Left
                                                        ((,) ((,) ((,) ((,) ((,)
                                                        ((,) ((,) ((,) ((,) ((,)
                                                        ((,) ((,) () c) p) b) c0) l)
                                                        p0) b0) o) b1) x1) a)
                                                        b2))))))))))))))})
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Left ((,) ((,) ((,)
                                                      ((,) ((,) ((,) ((,) ((,) ((,)
                                                      ((,) () c) p) b) c0) l) p0)
                                                      b0) o) b1)
                                                      x1))))))))))))))))))
                                                      (decideCredInfo p
                                                        (getCertificates c) x2))
                                                    (option_branch (\x2 ->
                                                      Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Left
                                                      ((,) ((,) ((,) ((,) ((,) ((,)
                                                      () b) c0) p0) b0) b1)
                                                      x2)))))))))))))))))))
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      ()))))))))))))))))))))))))))))))
                                                      (GHC.Base.Just
                                                      (app l ((:) b1 ((:) x1 [])))))
                                                    o) (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (inhabitant unit_inhabitant)))))))))))))))))))))))))))))))
                                                  (fromSendPacket r))
                                                (option_branch (\x1 ->
                                                  option_branch (\x2 ->
                                                    option_branch (\_ ->
                                                      GHC.Base.Just (ExistT __
                                                      (SendPacket (I.Handshake13
                                                      ((:) (I.Certificate13 empty c
                                                      ((:) [] [])) [])))))
                                                      (GHC.Base.Just (ExistT __
                                                      (CloseWith ((,)
                                                      I.AlertLevel_Fatal
                                                      I.HandshakeFailure))))
                                                      (decideCredInfo p
                                                        (getCertificates c) x2))
                                                    (option_branch (\x2 ->
                                                      GHC.Base.Just (ExistT __
                                                      (SendPacket (I.Handshake13
                                                      ((:) (I.Finished13
                                                      (makeVerifyData
                                                        (cipherHash c0)
                                                        (hkdfExpandLabel
                                                          (cipherHash c0)
                                                          (hkdfExtract
                                                            (cipherHash c0)
                                                            (hkdfExpandLabel
                                                              (cipherHash c0)
                                                              (hkdfExtract
                                                                (cipherHash c0)
                                                                (b_replicate
                                                                  (hashDigestSize
                                                                    (cipherHash c0))
                                                                  w0) b0)
                                                              (s2b ((:) 'd' ((:) 'e'
                                                                ((:) 'r' ((:) 'i'
                                                                ((:) 'v' ((:) 'e'
                                                                ((:) 'd'
                                                                ([])))))))))
                                                              (hashWith
                                                                (cipherHash c0) ((:)
                                                                (s2b ([])) []))
                                                              (hashDigestSize
                                                                (cipherHash c0)))
                                                            (ba_convert (snd p0)))
                                                          (s2b ((:) 's' ((:) ' '
                                                            ((:) 'h' ((:) 's' ((:)
                                                            ' ' ((:) 't' ((:) 'r'
                                                            ((:) 'a' ((:) 'f' ((:)
                                                            'f' ((:) 'i' ((:) 'c'
                                                            ([]))))))))))))))
                                                          (hashWith (cipherHash c0)
                                                            ((:) b ((:) b1 [])))
                                                          (hashDigestSize
                                                            (cipherHash c0)))
                                                        (hashWith (cipherHash c0)
                                                          x2))) [])))))
                                                      GHC.Base.Nothing
                                                      (GHC.Base.Just
                                                      (app l ((:) b1 ((:) x1 [])))))
                                                    o) GHC.Base.Nothing
                                                  (fromSendPacket r))))))))))))))
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
                                                  (prod_curry
                                                    (prod_curry
                                                      (\_ c p b c0 l p0 b0 o b1 b2 p1 h _ r ->
                                                      Prelude.Left ((,)
                                                      (option_branch (\x1 ->
                                                        Prelude.Right (Prelude.Right
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
                                                        (Prelude.Right (Prelude.Left
                                                        ((,) ((,) ((,) ((,) ((,)
                                                        ((,) ((,) ((,) ((,) ((,)
                                                        ((,) ((,) ((,) () c) p) b)
                                                        c0) l) p0) b0) o) b1) b2)
                                                        p1) h) x1))))))))))))))))
                                                        (option_branch (\x1 ->
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
                                                          ((,) ((,) ((,) ((,) () b)
                                                          c0) p0) b0) b1)
                                                          x1)))))))))))))))))))
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
                                                          ()))))))))))))))))))))))))))))))
                                                          (inhabitant
                                                            option_inhabitant))
                                                        (fromSendPacket r))
                                                      (option_branch (\x1 ->
                                                        GHC.Base.Just (ExistT __
                                                        (MakeCertVerify ((,) ((,)
                                                        ((,) p1 p) h)
                                                        (hashWith (cipherHash c0)
                                                          (app
                                                            (app l ((:) b1 ((:) b2
                                                              []))) ((:) x1 [])))))))
                                                        (option_branch (\x1 ->
                                                          GHC.Base.Just (ExistT __
                                                          (SendPacket (I.Handshake13
                                                          ((:) (I.Finished13
                                                          (makeVerifyData
                                                            (cipherHash c0)
                                                            (hkdfExpandLabel
                                                              (cipherHash c0)
                                                              (hkdfExtract
                                                                (cipherHash c0)
                                                                (hkdfExpandLabel
                                                                  (cipherHash c0)
                                                                  (hkdfExtract
                                                                    (cipherHash c0)
                                                                    (b_replicate
                                                                      (hashDigestSize
                                                                        (cipherHash
                                                                          c0)) w0)
                                                                    b0)
                                                                  (s2b ((:) 'd' ((:)
                                                                    'e' ((:) 'r'
                                                                    ((:) 'i' ((:)
                                                                    'v' ((:) 'e'
                                                                    ((:) 'd'
                                                                    ([])))))))))
                                                                  (hashWith
                                                                    (cipherHash c0)
                                                                    ((:) (s2b ([]))
                                                                    []))
                                                                  (hashDigestSize
                                                                    (cipherHash c0)))
                                                                (ba_convert
                                                                  (snd p0)))
                                                              (s2b ((:) 's' ((:) ' '
                                                                ((:) 'h' ((:) 's'
                                                                ((:) ' ' ((:) 't'
                                                                ((:) 'r' ((:) 'a'
                                                                ((:) 'f' ((:) 'f'
                                                                ((:) 'i' ((:) 'c'
                                                                ([]))))))))))))))
                                                              (hashWith
                                                                (cipherHash c0) ((:)
                                                                b ((:) b1 [])))
                                                              (hashDigestSize
                                                                (cipherHash c0)))
                                                            (hashWith
                                                              (cipherHash c0) x1)))
                                                          []))))) GHC.Base.Nothing
                                                          (inhabitant
                                                            option_inhabitant))
                                                        (fromSendPacket r))))))))))))))))
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
                                                    (prod_curry
                                                      (prod_curry
                                                        (prod_curry
                                                          (\_ c p b c0 l p0 b0 o b1 b2 _ _ b3 _ r ->
                                                          Prelude.Left ((,)
                                                          (option_branch (\x1 ->
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
                                                            (Prelude.Left ((,) ((,)
                                                            ((,) ((,) ((,) ((,) ((,)
                                                            ((,) ((,) ((,) ((,) ((,)
                                                            () c) p) b) c0) l) p0)
                                                            b0) o) b1) b2) b3)
                                                            x1)))))))))))))))))
                                                            (option_branch (\x1 ->
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
                                                              (Prelude.Left ((,)
                                                              ((,) ((,) ((,) ((,)
                                                              ((,) () b) c0) p0) b0)
                                                              b1)
                                                              x1)))))))))))))))))))
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
                                                              ()))))))))))))))))))))))))))))))
                                                              (inhabitant
                                                                option_inhabitant))
                                                            (fromMakeCertVerify r))
                                                          (option_branch (\x1 ->
                                                            GHC.Base.Just (ExistT __
                                                            (SendPacket
                                                            (I.Handshake13 ((:) x1
                                                            [])))))
                                                            (option_branch (\x1 ->
                                                              GHC.Base.Just (ExistT
                                                              __ (SendPacket
                                                              (I.Handshake13 ((:)
                                                              (I.Finished13
                                                              (makeVerifyData
                                                                (cipherHash c0)
                                                                (hkdfExpandLabel
                                                                  (cipherHash c0)
                                                                  (hkdfExtract
                                                                    (cipherHash c0)
                                                                    (hkdfExpandLabel
                                                                      (cipherHash
                                                                        c0)
                                                                      (hkdfExtract
                                                                        (cipherHash
                                                                          c0)
                                                                        (b_replicate
                                                                          (hashDigestSize
                                                                           (cipherHash
                                                                           c0)) w0)
                                                                        b0)
                                                                      (s2b ((:) 'd'
                                                                        ((:) 'e'
                                                                        ((:) 'r'
                                                                        ((:) 'i'
                                                                        ((:) 'v'
                                                                        ((:) 'e'
                                                                        ((:) 'd'
                                                                        ([])))))))))
                                                                      (hashWith
                                                                        (cipherHash
                                                                          c0) ((:)
                                                                        (s2b ([]))
                                                                        []))
                                                                      (hashDigestSize
                                                                        (cipherHash
                                                                          c0)))
                                                                    (ba_convert
                                                                      (snd p0)))
                                                                  (s2b ((:) 's' ((:)
                                                                    ' ' ((:) 'h'
                                                                    ((:) 's' ((:)
                                                                    ' ' ((:) 't'
                                                                    ((:) 'r' ((:)
                                                                    'a' ((:) 'f'
                                                                    ((:) 'f' ((:)
                                                                    'i' ((:) 'c'
                                                                    ([]))))))))))))))
                                                                  (hashWith
                                                                    (cipherHash c0)
                                                                    ((:) b ((:) b1
                                                                    [])))
                                                                  (hashDigestSize
                                                                    (cipherHash c0)))
                                                                (hashWith
                                                                  (cipherHash c0)
                                                                  x1))) [])))))
                                                              GHC.Base.Nothing
                                                              (inhabitant
                                                                option_inhabitant))
                                                            (fromMakeCertVerify r)))))))))))))))))
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
                                                      (prod_curry
                                                        (prod_curry
                                                          (\_ _ _ b c l p b0 _ b1 b2 b3 _ _ r ->
                                                          Prelude.Left ((,)
                                                          (option_branch (\x1 ->
                                                            option_branch (\x2 ->
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
                                                              (Prelude.Left ((,)
                                                              ((,) ((,) ((,) ((,)
                                                              ((,) () b) c) p) b0)
                                                              b1)
                                                              x2)))))))))))))))))))
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
                                                              ()))))))))))))))))))))))))))))))
                                                              (GHC.Base.Just
                                                              (app
                                                                (app l ((:) b1 ((:)
                                                                  b2 []))) ((:) b3
                                                                ((:) x1 [])))))
                                                            (option_branch (\x1 ->
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
                                                              (Prelude.Left ((,)
                                                              ((,) ((,) ((,) ((,)
                                                              ((,) () b) c) p) b0)
                                                              b1)
                                                              x1)))))))))))))))))))
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
                                                              ()))))))))))))))))))))))))))))))
                                                              (inhabitant
                                                                option_inhabitant))
                                                            (fromSendPacket r))
                                                          (option_branch (\x1 ->
                                                            option_branch (\x2 ->
                                                              GHC.Base.Just (ExistT
                                                              __ (SendPacket
                                                              (I.Handshake13 ((:)
                                                              (I.Finished13
                                                              (makeVerifyData
                                                                (cipherHash c)
                                                                (hkdfExpandLabel
                                                                  (cipherHash c)
                                                                  (hkdfExtract
                                                                    (cipherHash c)
                                                                    (hkdfExpandLabel
                                                                      (cipherHash c)
                                                                      (hkdfExtract
                                                                        (cipherHash
                                                                          c)
                                                                        (b_replicate
                                                                          (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0)
                                                                        b0)
                                                                      (s2b ((:) 'd'
                                                                        ((:) 'e'
                                                                        ((:) 'r'
                                                                        ((:) 'i'
                                                                        ((:) 'v'
                                                                        ((:) 'e'
                                                                        ((:) 'd'
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
                                                                  (s2b ((:) 's' ((:)
                                                                    ' ' ((:) 'h'
                                                                    ((:) 's' ((:)
                                                                    ' ' ((:) 't'
                                                                    ((:) 'r' ((:)
                                                                    'a' ((:) 'f'
                                                                    ((:) 'f' ((:)
                                                                    'i' ((:) 'c'
                                                                    ([]))))))))))))))
                                                                  (hashWith
                                                                    (cipherHash c)
                                                                    ((:) b ((:) b1
                                                                    [])))
                                                                  (hashDigestSize
                                                                    (cipherHash c)))
                                                                (hashWith
                                                                  (cipherHash c) x2)))
                                                              [])))))
                                                              GHC.Base.Nothing
                                                              (GHC.Base.Just
                                                              (app
                                                                (app l ((:) b1 ((:)
                                                                  b2 []))) ((:) b3
                                                                ((:) x1 [])))))
                                                            (option_branch (\x1 ->
                                                              GHC.Base.Just (ExistT
                                                              __ (SendPacket
                                                              (I.Handshake13 ((:)
                                                              (I.Finished13
                                                              (makeVerifyData
                                                                (cipherHash c)
                                                                (hkdfExpandLabel
                                                                  (cipherHash c)
                                                                  (hkdfExtract
                                                                    (cipherHash c)
                                                                    (hkdfExpandLabel
                                                                      (cipherHash c)
                                                                      (hkdfExtract
                                                                        (cipherHash
                                                                          c)
                                                                        (b_replicate
                                                                          (hashDigestSize
                                                                           (cipherHash
                                                                           c)) w0)
                                                                        b0)
                                                                      (s2b ((:) 'd'
                                                                        ((:) 'e'
                                                                        ((:) 'r'
                                                                        ((:) 'i'
                                                                        ((:) 'v'
                                                                        ((:) 'e'
                                                                        ((:) 'd'
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
                                                                  (s2b ((:) 's' ((:)
                                                                    ' ' ((:) 'h'
                                                                    ((:) 's' ((:)
                                                                    ' ' ((:) 't'
                                                                    ((:) 'r' ((:)
                                                                    'a' ((:) 'f'
                                                                    ((:) 'f' ((:)
                                                                    'i' ((:) 'c'
                                                                    ([]))))))))))))))
                                                                  (hashWith
                                                                    (cipherHash c)
                                                                    ((:) b ((:) b1
                                                                    [])))
                                                                  (hashDigestSize
                                                                    (cipherHash c)))
                                                                (hashWith
                                                                  (cipherHash c) x1)))
                                                              [])))))
                                                              GHC.Base.Nothing
                                                              (inhabitant
                                                                option_inhabitant))
                                                            (fromSendPacket r))))))))))))))))
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
                                                        (\_ _ _ b c _ p b0 _ b1 _ _ _ ->
                                                        Prelude.Left ((,)
                                                        (option_branch (\x1 ->
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
                                                          ((,) ((,) ((,) ((,) () b)
                                                          c) p) b0) b1)
                                                          x1)))))))))))))))))))
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
                                                          ()))))))))))))))))))))))))))))))
                                                          GHC.Base.Nothing)
                                                        (option_branch (\x1 ->
                                                          GHC.Base.Just (ExistT __
                                                          (SendPacket (I.Handshake13
                                                          ((:) (I.Finished13
                                                          (makeVerifyData
                                                            (cipherHash c)
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
                                                                        (cipherHash
                                                                          c)) w0)
                                                                    b0)
                                                                  (s2b ((:) 'd' ((:)
                                                                    'e' ((:) 'r'
                                                                    ((:) 'i' ((:)
                                                                    'v' ((:) 'e'
                                                                    ((:) 'd'
                                                                    ([])))))))))
                                                                  (hashWith
                                                                    (cipherHash c)
                                                                    ((:) (s2b ([]))
                                                                    []))
                                                                  (hashDigestSize
                                                                    (cipherHash c)))
                                                                (ba_convert (snd p)))
                                                              (s2b ((:) 's' ((:) ' '
                                                                ((:) 'h' ((:) 's'
                                                                ((:) ' ' ((:) 't'
                                                                ((:) 'r' ((:) 'a'
                                                                ((:) 'f' ((:) 'f'
                                                                ((:) 'i' ((:) 'c'
                                                                ([]))))))))))))))
                                                              (hashWith
                                                                (cipherHash c) ((:)
                                                                b ((:) b1 [])))
                                                              (hashDigestSize
                                                                (cipherHash c)))
                                                            (hashWith (cipherHash c)
                                                              x1))) [])))))
                                                          GHC.Base.Nothing
                                                          GHC.Base.Nothing)))))))))))))
                                    (sum_merge
                                      (prod_curry
                                        (prod_curry
                                          (prod_curry
                                            (prod_curry
                                              (prod_curry
                                                (prod_curry (\_ b c p b0 b1 l _ r ->
                                                  Prelude.Left ((,)
                                                  (option_branch (\x1 ->
                                                    Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Left ((,) ((,) ((,)
                                                    ((,) ((,) ((,) ((,) () b) c) p)
                                                    b0) b1) l)
                                                    x1))))))))))))))))))))
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (inhabitant unit_inhabitant)))))))))))))))))))))))))))))))
                                                    (fromSendPacket r))
                                                  (option_branch (\_ ->
                                                    GHC.Base.Just (ExistT __
                                                    (GetCurrentTime ())))
                                                    GHC.Base.Nothing
                                                    (fromSendPacket r))))))))))
                                      (sum_merge
                                        (prod_curry
                                          (prod_curry
                                            (prod_curry
                                              (prod_curry
                                                (prod_curry
                                                  (prod_curry
                                                    (prod_curry
                                                      (\_ b c p b0 b1 l b2 _ r ->
                                                      Prelude.Left ((,)
                                                      (option_branch (\_ ->
                                                        Prelude.Right (Prelude.Right
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
                                                        (Prelude.Right (Prelude.Left
                                                        ((,) ((,) ((,) ((,) ((,)
                                                        ((,) ((,) () b) c) p) b0)
                                                        b1) l)
                                                        b2)))))))))))))))))))))
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
                                                        (inhabitant unit_inhabitant)))))))))))))))))))))))))))))))
                                                        (fromGetCurrentTime r))
                                                      (option_branch (\_ ->
                                                        GHC.Base.Just (ExistT __
                                                        (SetSecret ((,) ((,) ((,)
                                                        (cipherHash c) c)
                                                        (hkdfExpandLabel
                                                          (cipherHash c)
                                                          (hkdfExtract
                                                            (cipherHash c)
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
                                                                        (cipherHash
                                                                          c)) w0)
                                                                    b0)
                                                                  (s2b ((:) 'd' ((:)
                                                                    'e' ((:) 'r'
                                                                    ((:) 'i' ((:)
                                                                    'v' ((:) 'e'
                                                                    ((:) 'd'
                                                                    ([])))))))))
                                                                  (hashWith
                                                                    (cipherHash c)
                                                                    ((:) (s2b ([]))
                                                                    []))
                                                                  (hashDigestSize
                                                                    (cipherHash c)))
                                                                (ba_convert (snd p)))
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
                                                            (b_replicate
                                                              (hashDigestSize
                                                                (cipherHash c)) w0))
                                                          (s2b ((:) 's' ((:) ' '
                                                            ((:) 'a' ((:) 'p' ((:)
                                                            ' ' ((:) 't' ((:) 'r'
                                                            ((:) 'a' ((:) 'f' ((:)
                                                            'f' ((:) 'i' ((:) 'c'
                                                            ([]))))))))))))))
                                                          (hashWith (cipherHash c)
                                                            (app l ((:) b2 [])))
                                                          (hashDigestSize
                                                            (cipherHash c))))
                                                        GHC.Base.False))))
                                                        GHC.Base.Nothing
                                                        (fromGetCurrentTime r)))))))))))
                                        (sum_merge
                                          (prod_curry
                                            (prod_curry
                                              (prod_curry
                                                (prod_curry
                                                  (prod_curry
                                                    (prod_curry
                                                      (prod_curry
                                                        (\_ b c p b0 b1 l b2 _ _ ->
                                                        Prelude.Left ((,)
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
                                                        (Prelude.Right
                                                        (Prelude.Right (Prelude.Left
                                                        ((,) ((,) ((,) ((,) ((,)
                                                        ((,) ((,) () b) c) p) b0)
                                                        b1) l)
                                                        b2))))))))))))))))))))))
                                                        (GHC.Base.Just (ExistT __
                                                        (SetSecret ((,) ((,) ((,)
                                                        (cipherHash c) c)
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
                                                                  w0) b0)
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
                                                            ((:) b ((:) b1 [])))
                                                          (hashDigestSize
                                                            (cipherHash c))))
                                                        GHC.Base.True)))))))))))))
                                          (sum_merge
                                            (prod_curry
                                              (prod_curry
                                                (prod_curry
                                                  (prod_curry
                                                    (prod_curry
                                                      (prod_curry
                                                        (prod_curry
                                                          (\_ b c p b0 b1 l b2 _ _ ->
                                                          Prelude.Left ((,)
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
                                                          (Prelude.Right
                                                          (Prelude.Right
                                                          (Prelude.Right
                                                          (Prelude.Left ((,) ((,)
                                                          ((,) ((,) ((,) ((,) ((,)
                                                          () b) c) p) b0) b1) l)
                                                          b2)))))))))))))))))))))))
                                                          (GHC.Base.Just (ExistT __
                                                          (RecvPacket
                                                          RFinished))))))))))))
                                            (sum_merge
                                              (prod_curry
                                                (prod_curry
                                                  (prod_curry
                                                    (prod_curry
                                                      (prod_curry
                                                        (prod_curry
                                                          (prod_curry
                                                            (\_ b c p b0 b1 l b2 _ r ->
                                                            Prelude.Left ((,)
                                                            (option_branch (\x1 ->
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
                                                              (Prelude.Right
                                                              (Prelude.Right
                                                              (Prelude.Right
                                                              (Prelude.Left ((,)
                                                              ((,) ((,) ((,) ((,)
                                                              ((,) ((,) ((,) () b)
                                                              c) p) b0) b1) l) b2)
                                                              x1))))))))))))))))))))))))
                                                              (option_branch (\x1 ->
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
                                                                (Prelude.Right
                                                                (Prelude.Right
                                                                (Prelude.Right
                                                                (Prelude.Right
                                                                (Prelude.Right
                                                                (Prelude.Right
                                                                (Prelude.Right
                                                                (Prelude.Right
                                                                (Prelude.Right
                                                                (Prelude.Left ((,)
                                                                ()
                                                                x1))))))))))))))))))))))))))))))
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
                                                                (inhabitant
                                                                  unit_inhabitant)))))))))))))))))))))))))))))))
                                                                (retAlert r))
                                                              (fromRecvFinished r))
                                                            (option_branch (\_ ->
                                                              GHC.Base.Just (ExistT
                                                              __ (GetCurrentTime
                                                              ())))
                                                              (option_branch (\x1 ->
                                                                GHC.Base.Just
                                                                (ExistT __
                                                                (CloseWith x1)))
                                                                GHC.Base.Nothing
                                                                (retAlert r))
                                                              (fromRecvFinished r)))))))))))
                                              (sum_merge
                                                (prod_curry
                                                  (prod_curry
                                                    (prod_curry
                                                      (prod_curry
                                                        (prod_curry
                                                          (prod_curry
                                                            (prod_curry
                                                              (prod_curry
                                                                (\_ b c p b0 b1 l b2 b3 _ r ->
                                                                Prelude.Left ((,)
                                                                (option_branch
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
                                                                  (Prelude.Right
                                                                  (Prelude.Right
                                                                  (Prelude.Right
                                                                  (Prelude.Right
                                                                  (Prelude.Left ((,)
                                                                  ((,) ((,) ((,)
                                                                  ((,) ((,) ((,)
                                                                  ((,) () b) c) p)
                                                                  b0) b1) l) b2)
                                                                  b3)))))))))))))))))))))))))
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
                                                                  (inhabitant
                                                                    unit_inhabitant)))))))))))))))))))))))))))))))
                                                                  (fromGetCurrentTime
                                                                    r))
                                                                (option_branch
                                                                  (\_ ->
                                                                  GHC.Base.Just
                                                                  (ExistT __
                                                                  (SetSecret ((,)
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
                                                                           b0)
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
                                                                          (s2b ([]))
                                                                          []))
                                                                        (hashDigestSize
                                                                          (cipherHash
                                                                           c)))
                                                                      (b_replicate
                                                                        (hashDigestSize
                                                                          (cipherHash
                                                                           c)) w0))
                                                                    (s2b ((:) 'c'
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
                                                                      (cipherHash c)
                                                                      (app l ((:) b2
                                                                        [])))
                                                                    (hashDigestSize
                                                                      (cipherHash c))))
                                                                  GHC.Base.True))))
                                                                  GHC.Base.Nothing
                                                                  (fromGetCurrentTime
                                                                    r))))))))))))
                                                (sum_merge
                                                  (prod_curry
                                                    (prod_curry
                                                      (prod_curry
                                                        (prod_curry
                                                          (prod_curry
                                                            (prod_curry
                                                              (prod_curry
                                                                (prod_curry
                                                                  (\_ b c p b0 b1 l b2 b3 _ _ ->
                                                                  Prelude.Left ((,)
                                                                  (case byteString_beq
                                                                          b3
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
                                                                           b0)
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
                                                                           ((:) b1
                                                                           [])))
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)))
                                                                           (hashWith
                                                                           (cipherHash
                                                                           c)
                                                                           (app l
                                                                           ((:) b2
                                                                           [])))) of {
                                                                    GHC.Base.True ->
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
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Right
                                                                     (Prelude.Left
                                                                     ()))))))))))))))))))))))));
                                                                    GHC.Base.False ->
                                                                     Prelude.Right
                                                                     (Prelude.Left
                                                                     ())})
                                                                  (case byteString_beq
                                                                          b3
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
                                                                           b0)
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
                                                                           ((:) b1
                                                                           [])))
                                                                           (hashDigestSize
                                                                           (cipherHash
                                                                           c)))
                                                                           (hashWith
                                                                           (cipherHash
                                                                           c)
                                                                           (app l
                                                                           ((:) b2
                                                                           [])))) of {
                                                                    GHC.Base.True ->
                                                                     GHC.Base.Just
                                                                     (ExistT __
                                                                     (RecvPacket
                                                                     RAppData));
                                                                    GHC.Base.False ->
                                                                     GHC.Base.Just
                                                                     (ExistT __
                                                                     (CloseWith ((,)
                                                                     I.AlertLevel_Fatal
                                                                     I.DecryptError)))})))))))))))
                                                  (sum_merge (\_ _ r -> Prelude.Left
                                                    ((,)
                                                    (option_branch (\x1 ->
                                                      Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Left
                                                      ((,) ()
                                                      x1)))))))))))))))))))))))))))
                                                      (option_branch (\x1 ->
                                                        Prelude.Right (Prelude.Right
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
                                                        (Prelude.Right
                                                        (Prelude.Right
                                                        (Prelude.Right
                                                        (Prelude.Right
                                                        (Prelude.Right
                                                        (Prelude.Right
                                                        (Prelude.Right (Prelude.Left
                                                        ((,) ()
                                                        x1)))))))))))))))))))))))))))))
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
                                                        (inhabitant unit_inhabitant)))))))))))))))))))))))))))))))
                                                        (retAlert r))
                                                      (fromRecvAppData r))
                                                    (option_branch (\x1 ->
                                                      GHC.Base.Just (ExistT __
                                                      (SendPacket (I.AppData13
                                                      (mconcat ((:)
                                                        (s2b ((:) 'H' ((:) 'T' ((:)
                                                          'T' ((:) 'P' ((:) '/' ((:)
                                                          '1' ((:) '.' ((:) '1' ((:)
                                                          ' ' ((:) '2' ((:) '0' ((:)
                                                          '0' ((:) ' ' ((:) 'O' ((:)
                                                          'K' ((:) '\r' ((:) '\n'
                                                          ((:) 'C' ((:) 'o' ((:) 'n'
                                                          ((:) 't' ((:) 'e' ((:) 'n'
                                                          ((:) 't' ((:) '-' ((:) 'T'
                                                          ((:) 'y' ((:) 'p' ((:) 'e'
                                                          ((:) ':' ((:) ' ' ((:) 't'
                                                          ((:) 'e' ((:) 'x' ((:) 't'
                                                          ((:) '/' ((:) 'p' ((:) 'l'
                                                          ((:) 'a' ((:) 'i' ((:) 'n'
                                                          ((:) '\r' ((:) '\n' ((:)
                                                          '\r' ((:) '\n' ((:) 'H'
                                                          ((:) 'e' ((:) 'l' ((:) 'l'
                                                          ((:) 'o' ((:) ',' ((:) ' '
                                                          ([]))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                        ((:) x1 ((:)
                                                        (s2b ((:) '!' ((:) '\r'
                                                          lF))) []))))))))
                                                      (option_branch (\x1 ->
                                                        GHC.Base.Just (ExistT __
                                                        (CloseWith x1)))
                                                        GHC.Base.Nothing
                                                        (retAlert r))
                                                      (fromRecvAppData r))))
                                                    (sum_merge
                                                      (prod_curry (\_ _ _ r ->
                                                        Prelude.Left ((,)
                                                        (option_branch (\_ ->
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
                                                          (Prelude.Right
                                                          (Prelude.Right
                                                          (Prelude.Right
                                                          (Prelude.Right
                                                          (Prelude.Right
                                                          (Prelude.Right
                                                          (Prelude.Right
                                                          (Prelude.Left
                                                          ())))))))))))))))))))))))))))
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
                                                          (inhabitant
                                                            unit_inhabitant)))))))))))))))))))))))))))))))
                                                          (fromSendPacket r))
                                                        (option_branch (\_ ->
                                                          GHC.Base.Just (ExistT __
                                                          (CloseWith ((,)
                                                          I.AlertLevel_Warning
                                                          I.CloseNotify))))
                                                          GHC.Base.Nothing
                                                          (fromSendPacket r)))))
                                                      (sum_merge (\_ _ _ ->
                                                        Prelude.Left ((,)
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
                                                        ()))))))))))))))))))))))))))))))
                                                        GHC.Base.Nothing))
                                                        (sum_merge
                                                          (prod_curry (\_ _ _ _ ->
                                                            Prelude.Left ((,)
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
                                                            (inhabitant
                                                              unit_inhabitant)))))))))))))))))))))))))))))))
                                                            GHC.Base.Nothing)))
                                                          (sum_merge
                                                            (prod_curry (\_ _ _ _ ->
                                                              Prelude.Left ((,)
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
                                                              (inhabitant
                                                                unit_inhabitant)))))))))))))))))))))))))))))))
                                                              GHC.Base.Nothing)))
                                                            (sum_merge
                                                              (prod_curry
                                                                (\_ _ _ _ ->
                                                                Prelude.Left ((,)
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
                                                                (inhabitant
                                                                  unit_inhabitant)))))))))))))))))))))))))))))))
                                                                GHC.Base.Nothing)))
                                                              (\u _ _ ->
                                                              Prelude.Right u))))))))))))))))))))))))))))))
    x __ x0

type TLSError = I.TLSError

errorToAlert :: TLSError -> (,) I.AlertLevel I.AlertDescription
errorToAlert = Helper.errorToAlert

isPError :: (I.GetResult a1) -> GHC.Base.Maybe ((,) I.AlertLevel I.AlertDescription)
isPError x =
  case x of {
   I.GotError err -> GHC.Base.Just (errorToAlert err);
   _ -> GHC.Base.Nothing}

isPPartial :: (I.GetResult a1) -> GHC.Base.Maybe (ByteString -> I.GetResult a1)
isPPartial x =
  case x of {
   I.GotPartial cont -> GHC.Base.Just cont;
   _ -> GHC.Base.Nothing}

isPSuccess :: (I.GetResult a1) -> GHC.Base.Maybe a1
isPSuccess x =
  case x of {
   I.GotSuccess p -> GHC.Base.Just p;
   _ -> GHC.Base.Nothing}

cProtocolType_beq :: I.ProtocolType -> I.ProtocolType -> GHC.Base.Bool
cProtocolType_beq x y =
  case x of {
   I.ProtocolType_ChangeCipherSpec ->
    case y of {
     I.ProtocolType_ChangeCipherSpec -> GHC.Base.True;
     _ -> GHC.Base.False};
   I.ProtocolType_Alert ->
    case y of {
     I.ProtocolType_Alert -> GHC.Base.True;
     _ -> GHC.Base.False};
   I.ProtocolType_Handshake ->
    case y of {
     I.ProtocolType_Handshake -> GHC.Base.True;
     _ -> GHC.Base.False};
   I.ProtocolType_AppData ->
    case y of {
     I.ProtocolType_AppData -> GHC.Base.True;
     _ -> GHC.Base.False};
   I.ProtocolType_DeprecatedHandshake ->
    case y of {
     I.ProtocolType_DeprecatedHandshake -> GHC.Base.True;
     _ -> GHC.Base.False}}

type HandshakeType = I.HandshakeType13

decodeHeader :: ByteString -> Prelude.Either I.AlertDescription I.Header
decodeHeader = \bs  -> case I.decodeHeader bs of { Prelude.Right a -> Prelude.Right a ; Prelude.Left err -> Prelude.Left (snd (errorToAlert err)) }

decodeRecord :: I.Header -> (GHC.Base.Maybe
                ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int)) -> ByteString
                -> Prelude.Either I.AlertDescription ((,) I.ProtocolType ByteString)
decodeRecord = Helper.decodeRecord

parseHandshakeRecord :: (GHC.Base.Maybe
                        (ByteString -> I.GetResult ((,) HandshakeType ByteString)))
                        -> ByteString -> I.GetResult ((,) HandshakeType ByteString)
parseHandshakeRecord = Helper.parseHandshakeRecord

parseHandshake :: ((,) HandshakeType ByteString) -> Prelude.Either
                  ((,) I.AlertLevel I.AlertDescription) I.Handshake13
parseHandshake = Helper.parseHandshake

maxCiphertextSize :: GHC.Base.Int
maxCiphertextSize = 16384

isRecvPacket :: Args_tls -> GHC.Base.Maybe RecvType
isRecvPacket p =
  case p of {
   RecvPacket a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

isSendPacket :: Args_tls -> GHC.Base.Maybe I.Packet13
isSendPacket p =
  case p of {
   SendPacket a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

isSetSecret :: Args_tls -> GHC.Base.Maybe
               ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Bool)
isSetSecret p =
  case p of {
   SetSecret a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

isCloseWith :: Args_tls -> GHC.Base.Maybe ((,) I.AlertLevel I.AlertDescription)
isCloseWith p =
  case p of {
   CloseWith a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

type ReadWrite_state =
  Prelude.Either ((,) ((,) ((,) () GHC.Base.Int) CertificateChain) PrivateKey)
  (Prelude.Either
  ((,) ((,) () GHC.Base.Int)
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int))
  (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int)))
  (GHC.Base.Maybe
  ((,) RecvType
  ((,) ByteString
  (GHC.Base.Maybe (ByteString -> I.GetResult ((,) HandshakeType ByteString)))))))
  ByteString) Rets_tls) DoHandshake_state))
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) ((,) () GHC.Base.Int) DoHandshake_state) Rets_tls) ByteString)
  (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int)))
  (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int))) RecvType)
  ((,) ByteString
  (GHC.Base.Maybe (ByteString -> I.GetResult ((,) HandshakeType ByteString)))))
  (Prelude.Either ((,) () ((,) I.AlertLevel I.AlertDescription))
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) ((,) ((,) () GHC.Base.Int) DoHandshake_state) Rets_tls) ByteString)
  (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int)))
  (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int))) RecvType)
  ((,) ByteString
  (GHC.Base.Maybe (ByteString -> I.GetResult ((,) HandshakeType ByteString)))))
  (Prelude.Either ((,) () ((,) I.AlertLevel I.AlertDescription))
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) () GHC.Base.Int) ByteString)
  (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int)))
  DoHandshake_state) I.Packet13) ((,) ((,) Hash Cipher) ByteString)) GHC.Base.Int)
  (Prelude.Either
  ((,)
  ((,)
  ((,) ((,) ((,) () GHC.Base.Int) ByteString)
  (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int)))
  DoHandshake_state) I.Packet13)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) () GHC.Base.Int) ByteString)
  (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int)))
  DoHandshake_state) ((,) I.AlertLevel I.AlertDescription))
  ((,) ((,) Hash Cipher) ByteString)) GHC.Base.Int)
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) () GHC.Base.Int) ByteString)
  (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int)))
  DoHandshake_state) ((,) I.AlertLevel I.AlertDescription))
  ((,) ((,) Hash Cipher) ByteString)) GHC.Base.Int)
  (Prelude.Either
  ((,)
  ((,)
  ((,) ((,) ((,) () GHC.Base.Int) ByteString)
  (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int)))
  DoHandshake_state) ((,) I.AlertLevel I.AlertDescription))
  (Prelude.Either
  ((,)
  ((,)
  ((,) ((,) ((,) () GHC.Base.Int) ByteString)
  (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int)))
  DoHandshake_state) ((,) I.AlertLevel I.AlertDescription))
  (Prelude.Either
  ((,)
  ((,)
  ((,)
  ((,) ((,) ((,) () GHC.Base.Int) ByteString)
  (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int)))
  (GHC.Base.Maybe ((,) ((,) ((,) Hash Cipher) ByteString) GHC.Base.Int)))
  DoHandshake_state) Args_tls) (GHC.Base.Maybe Prelude.String)))))))))))))

readWrite_step :: ReadWrite_state -> Rets_tls -> Prelude.Either
                  ((,) ReadWrite_state (GHC.Base.Maybe (SigT () Args_tls)))
                  (GHC.Base.Maybe Prelude.String)
readWrite_step x x0 =
  sum_merge
    (prod_curry
      (prod_curry
        (prod_curry (\_ n c p _ _ -> Prelude.Left ((,)
          ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
             (\_ -> Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
             (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
             (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
             (Prelude.Right GHC.Base.Nothing)))))))))))))
             (\n0 ->
             let {
              x1 = (,) ((,) ((,) ((,) ((,) GHC.Base.Nothing GHC.Base.Nothing)
               GHC.Base.Nothing) empty) (inhabitant sigT_rets_inhabit))
               (Prelude.Left ((,) ((,) ((,) () n) c) p))}
             in
             Prelude.Right (Prelude.Left ((,) ((,) () n0) x1)))
             n)
          ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
             (\_ -> GHC.Base.Nothing)
             (\_ -> GHC.Base.Just (ExistT __ (GetRandomBytes 0)))
             n))))))
    (sum_merge
      (prod_curry
        (prod_curry (\_ n p _ _ -> Prelude.Left ((,)
          (case p of {
            (,) a b ->
             case a of {
              (,) a0 b0 ->
               case a0 of {
                (,) a1 b1 ->
                 case a1 of {
                  (,) a2 b2 ->
                   case a2 of {
                    (,) a3 b3 ->
                     option_branch (\x1 ->
                       case x1 of {
                        (,) a4 b4 ->
                         case ltb (blength b1) ((Prelude.+) 1 ((Prelude.+) 1
                                ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 0))))) of {
                          GHC.Base.True -> Prelude.Right (Prelude.Right
                           (Prelude.Left ((,) ((,) ((,) ((,) ((,) ((,) ((,) ((,) ()
                           n) b) b0) b1) a3) b3) a4) b4)));
                          GHC.Base.False ->
                           case bsplit ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                                  ((Prelude.+) 1 ((Prelude.+) 1 0))))) b1 of {
                            (,) a5 b5 ->
                             case decodeHeader a5 of {
                              Prelude.Left a6 ->
                               (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                 (\_ -> Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right
                                 GHC.Base.Nothing)))))))))))))
                                 (\n0' -> Prelude.Right (Prelude.Left ((,) ((,) ()
                                 n0') ((,) ((,) ((,) ((,) ((,) a3 b3)
                                 GHC.Base.Nothing) b5) (RetAlert ((,)
                                 I.AlertLevel_Fatal a6))) b))))
                                 n;
                              Prelude.Right b6 ->
                               case ltb maxCiphertextSize (hdReadLen b6) of {
                                GHC.Base.True ->
                                 (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                   (\_ -> Prelude.Right (Prelude.Right
                                   (Prelude.Right (Prelude.Right (Prelude.Right
                                   (Prelude.Right (Prelude.Right (Prelude.Right
                                   (Prelude.Right (Prelude.Right (Prelude.Right
                                   (Prelude.Right (Prelude.Right
                                   GHC.Base.Nothing)))))))))))))
                                   (\n0' -> Prelude.Right (Prelude.Left ((,) ((,) ()
                                   n0') ((,) ((,) ((,) ((,) ((,) a3 b3)
                                   GHC.Base.Nothing) empty) (RetAlert ((,)
                                   I.AlertLevel_Fatal I.RecordOverflow))) b))))
                                   n;
                                GHC.Base.False ->
                                 case ltb (blength b5) (hdReadLen b6) of {
                                  GHC.Base.True -> Prelude.Right (Prelude.Right
                                   (Prelude.Right (Prelude.Right (Prelude.Left ((,)
                                   ((,) ((,) ((,) ((,) ((,) ((,) ((,) () n) b) b0)
                                   b1) a3) b3) a4) b4)))));
                                  GHC.Base.False ->
                                   case bsplit (hdReadLen b6) b5 of {
                                    (,) a6 b7 ->
                                     case b4 of {
                                      (,) a7 b8 ->
                                       case decodeRecord b6 a3 a6 of {
                                        Prelude.Left a8 ->
                                         option_branch (\x2 ->
                                           case x2 of {
                                            (,) a9 b9 ->
                                             (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                               (\_ -> Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right (Prelude.Right
                                               (Prelude.Right
                                               GHC.Base.Nothing)))))))))))))
                                               (\n0' -> Prelude.Right (Prelude.Left
                                               ((,) ((,) () n0') ((,) ((,) ((,) ((,)
                                               ((,) (GHC.Base.Just ((,) a9
                                               ((Prelude.+) 1 b9))) b3)
                                               GHC.Base.Nothing) b7) (RetAlert ((,)
                                               I.AlertLevel_Fatal a8))) b))))
                                               n})
                                           ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                              (\_ -> Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right
                                              GHC.Base.Nothing)))))))))))))
                                              (\n0' -> Prelude.Right (Prelude.Left
                                              ((,) ((,) () n0') ((,) ((,) ((,) ((,)
                                              ((,) GHC.Base.Nothing b3)
                                              GHC.Base.Nothing) b7) (RetAlert ((,)
                                              I.AlertLevel_Fatal a8))) b))))
                                              n) a3;
                                        Prelude.Right b9 ->
                                         case b9 of {
                                          (,) a8 b10 ->
                                           case cProtocolType_beq a8
                                                  I.ProtocolType_Handshake of {
                                            GHC.Base.True ->
                                             option_branch (\x2 ->
                                               option_branch (\x3 ->
                                                 case x3 of {
                                                  (,) a9 b11 ->
                                                   (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                     (\_ -> Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     GHC.Base.Nothing)))))))))))))
                                                     (\n0' -> Prelude.Right
                                                     (Prelude.Left ((,) ((,) () n0')
                                                     ((,) ((,) ((,) ((,) ((,)
                                                     (GHC.Base.Just ((,) a9
                                                     ((Prelude.+) 1 b11))) b3)
                                                     GHC.Base.Nothing) b7) (RetAlert
                                                     x2)) b))))
                                                     n})
                                                 ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                    (\_ -> Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    GHC.Base.Nothing)))))))))))))
                                                    (\n0' -> Prelude.Right
                                                    (Prelude.Left ((,) ((,) () n0')
                                                    ((,) ((,) ((,) ((,) ((,)
                                                    GHC.Base.Nothing b3)
                                                    GHC.Base.Nothing) b7) (RetAlert
                                                    x2)) b))))
                                                    n) a3)
                                               (option_branch (\x2 ->
                                                 option_branch (\x3 ->
                                                   case x3 of {
                                                    (,) a9 b11 ->
                                                     (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                       (\_ -> Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       (Prelude.Right (Prelude.Right
                                                       GHC.Base.Nothing)))))))))))))
                                                       (\n0' -> Prelude.Right
                                                       (Prelude.Left ((,) ((,) ()
                                                       n0') ((,) ((,) ((,) ((,) ((,)
                                                       (GHC.Base.Just ((,) a9
                                                       ((Prelude.+) 1 b11))) b3)
                                                       (GHC.Base.Just ((,) a4 ((,)
                                                       (mconcat ((:) a7 ((:) a6
                                                         []))) (GHC.Base.Just
                                                       x2))))) b7) b0) b))))
                                                       n})
                                                   ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                      (\_ -> Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      (Prelude.Right (Prelude.Right
                                                      GHC.Base.Nothing)))))))))))))
                                                      (\n0' -> Prelude.Right
                                                      (Prelude.Left ((,) ((,) ()
                                                      n0') ((,) ((,) ((,) ((,) ((,)
                                                      a3 b3) (GHC.Base.Just ((,) a4
                                                      ((,)
                                                      (mconcat ((:) a7 ((:) a6 [])))
                                                      (GHC.Base.Just x2))))) b7) b0)
                                                      b))))
                                                      n) a3)
                                                 (option_branch (\x2 ->
                                                   case parseHandshake x2 of {
                                                    Prelude.Left a9 ->
                                                     option_branch (\x3 ->
                                                       case x3 of {
                                                        (,) a10 b11 ->
                                                         (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                           (\_ -> Prelude.Right
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
                                                           GHC.Base.Nothing)))))))))))))
                                                           (\n0' -> Prelude.Right
                                                           (Prelude.Left ((,) ((,)
                                                           () n0') ((,) ((,) ((,)
                                                           ((,) ((,) (GHC.Base.Just
                                                           ((,) a10 ((Prelude.+) 1
                                                           b11))) b3)
                                                           GHC.Base.Nothing) b7)
                                                           (RetAlert a9)) b))))
                                                           n})
                                                       ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                          (\_ -> Prelude.Right
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
                                                          GHC.Base.Nothing)))))))))))))
                                                          (\n0' -> Prelude.Right
                                                          (Prelude.Left ((,) ((,) ()
                                                          n0') ((,) ((,) ((,) ((,)
                                                          ((,) GHC.Base.Nothing b3)
                                                          GHC.Base.Nothing) b7)
                                                          (RetAlert a9)) b))))
                                                          n) a3;
                                                    Prelude.Right b11 ->
                                                     option_branch (\x3 ->
                                                       case recvType_beq a4
                                                              RFinished of {
                                                        GHC.Base.True ->
                                                         option_branch (\x4 ->
                                                           case x4 of {
                                                            (,) a9 b12 ->
                                                             (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                               (\_ -> Prelude.Right
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
                                                               GHC.Base.Nothing)))))))))))))
                                                               (\n0' ->
                                                               Prelude.Right
                                                               (Prelude.Left ((,)
                                                               ((,) () n0') ((,)
                                                               ((,) ((,) ((,) ((,)
                                                               (GHC.Base.Just ((,)
                                                               a9 ((Prelude.+) 1
                                                               b12))) b3)
                                                               GHC.Base.Nothing) b7)
                                                               (FromRecvFinished
                                                               x3)) b))))
                                                               n})
                                                           ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                              (\_ -> Prelude.Right
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
                                                              GHC.Base.Nothing)))))))))))))
                                                              (\n0' -> Prelude.Right
                                                              (Prelude.Left ((,)
                                                              ((,) () n0') ((,) ((,)
                                                              ((,) ((,) ((,)
                                                              GHC.Base.Nothing b3)
                                                              GHC.Base.Nothing) b7)
                                                              (FromRecvFinished x3))
                                                              b))))
                                                              n) a3;
                                                        GHC.Base.False ->
                                                         option_branch (\x4 ->
                                                           case x4 of {
                                                            (,) a9 b12 ->
                                                             (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                               (\_ -> Prelude.Right
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
                                                               GHC.Base.Nothing)))))))))))))
                                                               (\n0' ->
                                                               Prelude.Right
                                                               (Prelude.Left ((,)
                                                               ((,) () n0') ((,)
                                                               ((,) ((,) ((,) ((,)
                                                               (GHC.Base.Just ((,)
                                                               a9 ((Prelude.+) 1
                                                               b12))) b3)
                                                               GHC.Base.Nothing) b7)
                                                               (RetAlert ((,)
                                                               I.AlertLevel_Fatal
                                                               I.UnexpectedMessage)))
                                                               b))))
                                                               n})
                                                           ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                              (\_ -> Prelude.Right
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
                                                              GHC.Base.Nothing)))))))))))))
                                                              (\n0' -> Prelude.Right
                                                              (Prelude.Left ((,)
                                                              ((,) () n0') ((,) ((,)
                                                              ((,) ((,) ((,)
                                                              GHC.Base.Nothing b3)
                                                              GHC.Base.Nothing) b7)
                                                              (RetAlert ((,)
                                                              I.AlertLevel_Fatal
                                                              I.UnexpectedMessage)))
                                                              b))))
                                                              n) a3})
                                                       (option_branch (\x3 ->
                                                         case recvType_beq a4
                                                                RClientHello of {
                                                          GHC.Base.True ->
                                                           option_branch (\x4 ->
                                                             case x4 of {
                                                              (,) a9 b12 ->
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
                                                                 GHC.Base.Nothing)))))))))))))
                                                                 (\n0' ->
                                                                 Prelude.Right
                                                                 (Prelude.Left ((,)
                                                                 ((,) () n0') ((,)
                                                                 ((,) ((,) ((,) ((,)
                                                                 (GHC.Base.Just ((,)
                                                                 a9 ((Prelude.+) 1
                                                                 b12))) b3)
                                                                 GHC.Base.Nothing)
                                                                 b7)
                                                                 (FromRecvClientHello
                                                                 ((,)
                                                                 (mconcat ((:) a7
                                                                   ((:) a6 [])))
                                                                 x3))) b))))
                                                                 n})
                                                             ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                                (\_ -> Prelude.Right
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
                                                                GHC.Base.Nothing)))))))))))))
                                                                (\n0' ->
                                                                Prelude.Right
                                                                (Prelude.Left ((,)
                                                                ((,) () n0') ((,)
                                                                ((,) ((,) ((,) ((,)
                                                                GHC.Base.Nothing b3)
                                                                GHC.Base.Nothing)
                                                                b7)
                                                                (FromRecvClientHello
                                                                ((,)
                                                                (mconcat ((:) a7
                                                                  ((:) a6 [])))
                                                                x3))) b))))
                                                                n) a3;
                                                          GHC.Base.False ->
                                                           option_branch (\x4 ->
                                                             case x4 of {
                                                              (,) a9 b12 ->
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
                                                                 GHC.Base.Nothing)))))))))))))
                                                                 (\n0' ->
                                                                 Prelude.Right
                                                                 (Prelude.Left ((,)
                                                                 ((,) () n0') ((,)
                                                                 ((,) ((,) ((,) ((,)
                                                                 (GHC.Base.Just ((,)
                                                                 a9 ((Prelude.+) 1
                                                                 b12))) b3)
                                                                 GHC.Base.Nothing)
                                                                 b7) (RetAlert ((,)
                                                                 I.AlertLevel_Fatal
                                                                 I.UnexpectedMessage)))
                                                                 b))))
                                                                 n})
                                                             ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                                (\_ -> Prelude.Right
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
                                                                GHC.Base.Nothing)))))))))))))
                                                                (\n0' ->
                                                                Prelude.Right
                                                                (Prelude.Left ((,)
                                                                ((,) () n0') ((,)
                                                                ((,) ((,) ((,) ((,)
                                                                GHC.Base.Nothing b3)
                                                                GHC.Base.Nothing)
                                                                b7) (RetAlert ((,)
                                                                I.AlertLevel_Fatal
                                                                I.UnexpectedMessage)))
                                                                b))))
                                                                n) a3})
                                                         (option_branch (\x3 ->
                                                           case x3 of {
                                                            (,) a9 b12 ->
                                                             (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                               (\_ -> Prelude.Right
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
                                                               GHC.Base.Nothing)))))))))))))
                                                               (\n0' ->
                                                               Prelude.Right
                                                               (Prelude.Left ((,)
                                                               ((,) () n0') ((,)
                                                               ((,) ((,) ((,) ((,)
                                                               (GHC.Base.Just ((,)
                                                               a9 ((Prelude.+) 1
                                                               b12))) b3)
                                                               GHC.Base.Nothing) b7)
                                                               (RetAlert ((,)
                                                               I.AlertLevel_Fatal
                                                               I.UnexpectedMessage)))
                                                               b))))
                                                               n})
                                                           ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                              (\_ -> Prelude.Right
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
                                                              GHC.Base.Nothing)))))))))))))
                                                              (\n0' -> Prelude.Right
                                                              (Prelude.Left ((,)
                                                              ((,) () n0') ((,) ((,)
                                                              ((,) ((,) ((,)
                                                              GHC.Base.Nothing b3)
                                                              GHC.Base.Nothing) b7)
                                                              (RetAlert ((,)
                                                              I.AlertLevel_Fatal
                                                              I.UnexpectedMessage)))
                                                              b))))
                                                              n) a3)
                                                         (clientHello b11))
                                                       (finished b11)})
                                                   (option_branch (\x2 ->
                                                     case x2 of {
                                                      (,) a9 b11 ->
                                                       (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                         (\_ -> Prelude.Right
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
                                                         GHC.Base.Nothing)))))))))))))
                                                         (\n0' -> Prelude.Right
                                                         (Prelude.Left ((,) ((,) ()
                                                         n0') ((,) ((,) ((,) ((,)
                                                         ((,) (GHC.Base.Just ((,) a9
                                                         ((Prelude.+) 1 b11))) b3)
                                                         GHC.Base.Nothing) b7)
                                                         (RetAlert ((,)
                                                         I.AlertLevel_Fatal
                                                         I.DecodeError))) b))))
                                                         n})
                                                     ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                        (\_ -> Prelude.Right
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
                                                        GHC.Base.Nothing)))))))))))))
                                                        (\n0' -> Prelude.Right
                                                        (Prelude.Left ((,) ((,) ()
                                                        n0') ((,) ((,) ((,) ((,)
                                                        ((,) GHC.Base.Nothing b3)
                                                        GHC.Base.Nothing) b7)
                                                        (RetAlert ((,)
                                                        I.AlertLevel_Fatal
                                                        I.DecodeError))) b))))
                                                        n) a3)
                                                   (isPSuccess
                                                     (parseHandshakeRecord b8 b10)))
                                                 (isPPartial
                                                   (parseHandshakeRecord b8 b10)))
                                               (isPError
                                                 (parseHandshakeRecord b8 b10));
                                            GHC.Base.False ->
                                             option_branch (\_ ->
                                               option_branch (\x2 ->
                                                 case x2 of {
                                                  (,) a9 b11 ->
                                                   (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                     (\_ -> Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     (Prelude.Right (Prelude.Right
                                                     GHC.Base.Nothing)))))))))))))
                                                     (\n0' -> Prelude.Right
                                                     (Prelude.Left ((,) ((,) () n0')
                                                     ((,) ((,) ((,) ((,) ((,)
                                                     (GHC.Base.Just ((,) a9
                                                     ((Prelude.+) 1 b11))) b3)
                                                     GHC.Base.Nothing) b7) (RetAlert
                                                     ((,) I.AlertLevel_Fatal
                                                     I.UnexpectedMessage))) b))))
                                                     n})
                                                 ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                    (\_ -> Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    GHC.Base.Nothing)))))))))))))
                                                    (\n0' -> Prelude.Right
                                                    (Prelude.Left ((,) ((,) () n0')
                                                    ((,) ((,) ((,) ((,) ((,)
                                                    GHC.Base.Nothing b3)
                                                    GHC.Base.Nothing) b7) (RetAlert
                                                    ((,) I.AlertLevel_Fatal
                                                    I.UnexpectedMessage))) b))))
                                                    n) a3)
                                               (case cProtocolType_beq a8
                                                       I.ProtocolType_ChangeCipherSpec of {
                                                 GHC.Base.True ->
                                                  (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                    (\_ -> Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    GHC.Base.Nothing)))))))))))))
                                                    (\n0' -> Prelude.Right
                                                    (Prelude.Left ((,) ((,) () n0')
                                                    ((,) ((,) ((,) ((,) ((,) a3 b3)
                                                    (GHC.Base.Just ((,) a4 b4))) b7)
                                                    b0) b))))
                                                    n;
                                                 GHC.Base.False ->
                                                  case cProtocolType_beq a8
                                                         I.ProtocolType_AppData of {
                                                   GHC.Base.True ->
                                                    case recvType_beq a4 RAppData of {
                                                     GHC.Base.True ->
                                                      option_branch (\x2 ->
                                                        case x2 of {
                                                         (,) a9 b11 ->
                                                          (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                            (\_ -> Prelude.Right
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
                                                            GHC.Base.Nothing)))))))))))))
                                                            (\n0' -> Prelude.Right
                                                            (Prelude.Left ((,) ((,)
                                                            () n0') ((,) ((,) ((,)
                                                            ((,) ((,) (GHC.Base.Just
                                                            ((,) a9 ((Prelude.+) 1
                                                            b11))) b3)
                                                            GHC.Base.Nothing) b7)
                                                            (FromRecvAppData b10))
                                                            b))))
                                                            n})
                                                        ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                           (\_ -> Prelude.Right
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
                                                           GHC.Base.Nothing)))))))))))))
                                                           (\n0' -> Prelude.Right
                                                           (Prelude.Left ((,) ((,)
                                                           () n0') ((,) ((,) ((,)
                                                           ((,) ((,)
                                                           GHC.Base.Nothing b3)
                                                           GHC.Base.Nothing) b7)
                                                           (FromRecvAppData b10))
                                                           b))))
                                                           n) a3;
                                                     GHC.Base.False ->
                                                      option_branch (\x2 ->
                                                        case x2 of {
                                                         (,) a9 b11 ->
                                                          (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                            (\_ -> Prelude.Right
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
                                                            GHC.Base.Nothing)))))))))))))
                                                            (\n0' -> Prelude.Right
                                                            (Prelude.Left ((,) ((,)
                                                            () n0') ((,) ((,) ((,)
                                                            ((,) ((,) (GHC.Base.Just
                                                            ((,) a9 ((Prelude.+) 1
                                                            b11))) b3)
                                                            GHC.Base.Nothing) b7)
                                                            (RetAlert ((,)
                                                            I.AlertLevel_Fatal
                                                            I.UnexpectedMessage)))
                                                            b))))
                                                            n})
                                                        ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                           (\_ -> Prelude.Right
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
                                                           GHC.Base.Nothing)))))))))))))
                                                           (\n0' -> Prelude.Right
                                                           (Prelude.Left ((,) ((,)
                                                           () n0') ((,) ((,) ((,)
                                                           ((,) ((,)
                                                           GHC.Base.Nothing b3)
                                                           GHC.Base.Nothing) b7)
                                                           (RetAlert ((,)
                                                           I.AlertLevel_Fatal
                                                           I.UnexpectedMessage)))
                                                           b))))
                                                           n) a3};
                                                   GHC.Base.False ->
                                                    option_branch (\x2 ->
                                                      case x2 of {
                                                       (,) a9 b11 ->
                                                        (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                          (\_ -> Prelude.Right
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
                                                          GHC.Base.Nothing)))))))))))))
                                                          (\n0' -> Prelude.Right
                                                          (Prelude.Left ((,) ((,) ()
                                                          n0') ((,) ((,) ((,) ((,)
                                                          ((,) (GHC.Base.Just ((,)
                                                          a9 ((Prelude.+) 1 b11)))
                                                          b3) GHC.Base.Nothing) b7)
                                                          (RetAlert ((,)
                                                          I.AlertLevel_Fatal
                                                          I.UnexpectedMessage)))
                                                          b))))
                                                          n})
                                                      ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                         (\_ -> Prelude.Right
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
                                                         GHC.Base.Nothing)))))))))))))
                                                         (\n0' -> Prelude.Right
                                                         (Prelude.Left ((,) ((,) ()
                                                         n0') ((,) ((,) ((,) ((,)
                                                         ((,) GHC.Base.Nothing b3)
                                                         GHC.Base.Nothing) b7)
                                                         (RetAlert ((,)
                                                         I.AlertLevel_Fatal
                                                         I.UnexpectedMessage)))
                                                         b))))
                                                         n) a3}}) b8}}}}}}}}}}})
                       (case doHandshake_step b b0 of {
                         Prelude.Left p0 ->
                          case p0 of {
                           (,) s o ->
                            case o of {
                             GHC.Base.Just s0 ->
                              case s0 of {
                               ExistT _ v ->
                                option_branch (\x1 ->
                                  (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                    (\_ -> Prelude.Right (Prelude.Right
                                    (Prelude.Right (Prelude.Right (Prelude.Right
                                    (Prelude.Right (Prelude.Right (Prelude.Right
                                    (Prelude.Right (Prelude.Right (Prelude.Right
                                    (Prelude.Right (Prelude.Right
                                    GHC.Base.Nothing)))))))))))))
                                    (\n0' -> Prelude.Right (Prelude.Left ((,) ((,)
                                    () n0') ((,) ((,) ((,) ((,) ((,) a3 b3)
                                    (GHC.Base.Just ((,) x1 ((,) empty
                                    GHC.Base.Nothing)))) b1) b0) s))))
                                    n)
                                  (option_branch (\x1 ->
                                    option_branch (\x2 ->
                                      case x2 of {
                                       (,) a4 b4 -> Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Left ((,) ((,) ((,)
                                        ((,) ((,) ((,) ((,) () n) b1) a3) s) x1) a4)
                                        b4)))))))}) (Prelude.Right (Prelude.Right
                                      (Prelude.Right (Prelude.Right (Prelude.Right
                                      (Prelude.Right (Prelude.Right (Prelude.Left
                                      ((,) ((,) ((,) ((,) ((,) () n) b1) a3) s)
                                      x1))))))))) b3)
                                    (option_branch (\x1 ->
                                      option_branch (\x2 ->
                                        case x2 of {
                                         (,) a4 b4 -> Prelude.Right (Prelude.Right
                                          (Prelude.Right (Prelude.Right
                                          (Prelude.Right (Prelude.Right
                                          (Prelude.Right (Prelude.Right
                                          (Prelude.Left ((,) ((,) ((,) ((,) ((,)
                                          ((,) ((,) () n) b1) a3) s) x1) a4)
                                          b4)))))))))}) (Prelude.Right
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Left ((,) ((,) ((,) ((,) ((,) () n)
                                        b1) a3) s) x1)))))))))))) b3)
                                      (option_branch (\x1 ->
                                        case x1 of {
                                         (,) a4 b4 ->
                                          case b4 of {
                                           GHC.Base.True ->
                                            (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                              (\_ -> Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right
                                              GHC.Base.Nothing)))))))))))))
                                              (\n0' -> Prelude.Right (Prelude.Left
                                              ((,) ((,) () n0') ((,) ((,) ((,) ((,)
                                              ((,) (GHC.Base.Just ((,) a4 0)) b3)
                                              GHC.Base.Nothing) b1) FromSetSecret)
                                              s))))
                                              n;
                                           GHC.Base.False ->
                                            (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                              (\_ -> Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right
                                              GHC.Base.Nothing)))))))))))))
                                              (\n0' -> Prelude.Right (Prelude.Left
                                              ((,) ((,) () n0') ((,) ((,) ((,) ((,)
                                              ((,) a3 (GHC.Base.Just ((,) a4 0)))
                                              GHC.Base.Nothing) b1) FromSetSecret)
                                              s))))
                                              n}}) (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Left ((,) ((,) ((,)
                                        ((,) ((,) ((,) () n) b1) a3) b3) s)
                                        v)))))))))))))) (isSetSecret v))
                                      (isCloseWith v)) (isSendPacket v))
                                  (isRecvPacket v)};
                             GHC.Base.Nothing -> Prelude.Right (Prelude.Right
                              (Prelude.Right (Prelude.Right (Prelude.Right
                              (Prelude.Right (Prelude.Right (Prelude.Right
                              (Prelude.Right (Prelude.Right (Prelude.Right
                              (Prelude.Right (Prelude.Right
                              GHC.Base.Nothing))))))))))))}};
                         Prelude.Right _ -> Prelude.Right (Prelude.Right
                          (Prelude.Right (Prelude.Right (Prelude.Right
                          (Prelude.Right (Prelude.Right (Prelude.Right
                          (Prelude.Right (Prelude.Right (Prelude.Right
                          (Prelude.Right (Prelude.Right GHC.Base.Nothing))))))))))))})
                       b2}}}}})
          (case p of {
            (,) a b ->
             case a of {
              (,) a0 b0 ->
               case a0 of {
                (,) a1 b1 ->
                 case a1 of {
                  (,) a2 b2 ->
                   case a2 of {
                    (,) a3 b3 ->
                     option_branch (\x1 ->
                       case x1 of {
                        (,) _ b4 ->
                         case ltb (blength b1) ((Prelude.+) 1 ((Prelude.+) 1
                                ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 0))))) of {
                          GHC.Base.True -> GHC.Base.Just (ExistT __ (RecvData ()));
                          GHC.Base.False ->
                           case bsplit ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                                  ((Prelude.+) 1 ((Prelude.+) 1 0))))) b1 of {
                            (,) a4 b5 ->
                             case decodeHeader a4 of {
                              Prelude.Left _ ->
                               (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                 (\_ -> GHC.Base.Nothing)
                                 (\_ -> GHC.Base.Just (ExistT __ (GetRandomBytes
                                 0)))
                                 n;
                              Prelude.Right b6 ->
                               case ltb maxCiphertextSize (hdReadLen b6) of {
                                GHC.Base.True ->
                                 (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                   (\_ -> GHC.Base.Nothing)
                                   (\_ -> GHC.Base.Just (ExistT __ (GetRandomBytes
                                   0)))
                                   n;
                                GHC.Base.False ->
                                 case ltb (blength b5) (hdReadLen b6) of {
                                  GHC.Base.True -> GHC.Base.Just (ExistT __
                                   (RecvData ()));
                                  GHC.Base.False ->
                                   case bsplit (hdReadLen b6) b5 of {
                                    (,) a5 _ ->
                                     case b4 of {
                                      (,) _ b7 ->
                                       case decodeRecord b6 a3 a5 of {
                                        Prelude.Left _ ->
                                         option_branch (\_ ->
                                           (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                             (\_ -> GHC.Base.Nothing)
                                             (\_ -> GHC.Base.Just (ExistT __
                                             (GetRandomBytes 0)))
                                             n)
                                           ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                              (\_ -> GHC.Base.Nothing)
                                              (\_ -> GHC.Base.Just (ExistT __
                                              (GetRandomBytes 0)))
                                              n) a3;
                                        Prelude.Right b8 ->
                                         case b8 of {
                                          (,) a6 b9 ->
                                           case cProtocolType_beq a6
                                                  I.ProtocolType_Handshake of {
                                            GHC.Base.True ->
                                             option_branch (\_ ->
                                               option_branch (\_ ->
                                                 (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                   (\_ -> GHC.Base.Nothing)
                                                   (\_ -> GHC.Base.Just (ExistT __
                                                   (GetRandomBytes 0)))
                                                   n)
                                                 ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                    (\_ -> GHC.Base.Nothing)
                                                    (\_ -> GHC.Base.Just (ExistT __
                                                    (GetRandomBytes 0)))
                                                    n) a3)
                                               (option_branch (\_ ->
                                                 option_branch (\_ ->
                                                   (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                     (\_ -> GHC.Base.Nothing)
                                                     (\_ -> GHC.Base.Just (ExistT __
                                                     (GetRandomBytes 0)))
                                                     n)
                                                   ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                      (\_ -> GHC.Base.Nothing)
                                                      (\_ -> GHC.Base.Just (ExistT
                                                      __ (GetRandomBytes 0)))
                                                      n) a3)
                                                 (option_branch (\x2 ->
                                                   case parseHandshake x2 of {
                                                    Prelude.Left _ ->
                                                     option_branch (\_ ->
                                                       (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                         (\_ ->
                                                         GHC.Base.Nothing)
                                                         (\_ -> GHC.Base.Just
                                                         (ExistT __ (GetRandomBytes
                                                         0)))
                                                         n)
                                                       ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                          (\_ ->
                                                          GHC.Base.Nothing)
                                                          (\_ -> GHC.Base.Just
                                                          (ExistT __ (GetRandomBytes
                                                          0)))
                                                          n) a3;
                                                    Prelude.Right b10 ->
                                                     option_branch (\_ ->
                                                       option_branch (\_ ->
                                                         (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                           (\_ ->
                                                           GHC.Base.Nothing)
                                                           (\_ -> GHC.Base.Just
                                                           (ExistT __
                                                           (GetRandomBytes 0)))
                                                           n)
                                                         ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                            (\_ ->
                                                            GHC.Base.Nothing)
                                                            (\_ -> GHC.Base.Just
                                                            (ExistT __
                                                            (GetRandomBytes 0)))
                                                            n) a3)
                                                       (option_branch (\_ ->
                                                         option_branch (\_ ->
                                                           (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                             (\_ ->
                                                             GHC.Base.Nothing)
                                                             (\_ -> GHC.Base.Just
                                                             (ExistT __
                                                             (GetRandomBytes 0)))
                                                             n)
                                                           ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                              (\_ ->
                                                              GHC.Base.Nothing)
                                                              (\_ -> GHC.Base.Just
                                                              (ExistT __
                                                              (GetRandomBytes 0)))
                                                              n) a3)
                                                         (option_branch (\_ ->
                                                           (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                             (\_ ->
                                                             GHC.Base.Nothing)
                                                             (\_ -> GHC.Base.Just
                                                             (ExistT __
                                                             (GetRandomBytes 0)))
                                                             n)
                                                           ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                              (\_ ->
                                                              GHC.Base.Nothing)
                                                              (\_ -> GHC.Base.Just
                                                              (ExistT __
                                                              (GetRandomBytes 0)))
                                                              n) a3)
                                                         (clientHello b10))
                                                       (finished b10)})
                                                   (option_branch (\_ ->
                                                     (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                       (\_ ->
                                                       GHC.Base.Nothing)
                                                       (\_ -> GHC.Base.Just (ExistT
                                                       __ (GetRandomBytes 0)))
                                                       n)
                                                     ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                        (\_ ->
                                                        GHC.Base.Nothing)
                                                        (\_ -> GHC.Base.Just (ExistT
                                                        __ (GetRandomBytes 0)))
                                                        n) a3)
                                                   (isPSuccess
                                                     (parseHandshakeRecord b7 b9)))
                                                 (isPPartial
                                                   (parseHandshakeRecord b7 b9)))
                                               (isPError
                                                 (parseHandshakeRecord b7 b9));
                                            GHC.Base.False ->
                                             option_branch (\_ ->
                                               option_branch (\_ ->
                                                 (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                   (\_ -> GHC.Base.Nothing)
                                                   (\_ -> GHC.Base.Just (ExistT __
                                                   (GetRandomBytes 0)))
                                                   n)
                                                 ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                    (\_ -> GHC.Base.Nothing)
                                                    (\_ -> GHC.Base.Just (ExistT __
                                                    (GetRandomBytes 0)))
                                                    n) a3)
                                               (case cProtocolType_beq a6
                                                       I.ProtocolType_ChangeCipherSpec of {
                                                 GHC.Base.True ->
                                                  (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                    (\_ -> GHC.Base.Nothing)
                                                    (\_ -> GHC.Base.Just (ExistT __
                                                    (GetRandomBytes 0)))
                                                    n;
                                                 GHC.Base.False ->
                                                  option_branch (\_ ->
                                                    (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                      (\_ -> GHC.Base.Nothing)
                                                      (\_ -> GHC.Base.Just (ExistT
                                                      __ (GetRandomBytes 0)))
                                                      n)
                                                    ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                                       (\_ ->
                                                       GHC.Base.Nothing)
                                                       (\_ -> GHC.Base.Just (ExistT
                                                       __ (GetRandomBytes 0)))
                                                       n) a3}) b7}}}}}}}}}}})
                       (case doHandshake_step b b0 of {
                         Prelude.Left p0 ->
                          case p0 of {
                           (,) _ o ->
                            case o of {
                             GHC.Base.Just s0 ->
                              case s0 of {
                               ExistT _ v ->
                                option_branch (\_ ->
                                  (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                    (\_ -> GHC.Base.Nothing)
                                    (\_ -> GHC.Base.Just (ExistT __ (GetRandomBytes
                                    0)))
                                    n)
                                  (option_branch (\x1 ->
                                    option_branch (\x2 -> GHC.Base.Just (ExistT __
                                      (SendData ((,) x1 (GHC.Base.Just x2)))))
                                      (GHC.Base.Just (ExistT __ (SendData ((,) x1
                                      GHC.Base.Nothing)))) b3)
                                    (option_branch (\x1 ->
                                      option_branch (\x2 ->
                                        case x2 of {
                                         (,) a4 b4 -> GHC.Base.Just (ExistT __
                                          (SendData ((,) (I.Alert13 ((:) x1 []))
                                          (GHC.Base.Just ((,) a4 b4)))))})
                                        (GHC.Base.Just (ExistT __ (SendData ((,)
                                        (I.Alert13 ((:) x1 [])) GHC.Base.Nothing))))
                                        b3)
                                      (option_branch (\_ ->
                                        (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                          (\_ -> GHC.Base.Nothing)
                                          (\_ -> GHC.Base.Just (ExistT __
                                          (GetRandomBytes 0)))
                                          n) (GHC.Base.Just (ExistT __ v))
                                        (isSetSecret v)) (isCloseWith v))
                                    (isSendPacket v)) (isRecvPacket v)};
                             GHC.Base.Nothing -> GHC.Base.Nothing}};
                         Prelude.Right _ -> GHC.Base.Nothing}) b2}}}}})))))
      (sum_merge
        (prod_curry
          (prod_curry
            (prod_curry
              (prod_curry
                (prod_curry
                  (prod_curry
                    (prod_curry
                      (prod_curry (\_ n d r b o o0 r0 p _ r1 -> Prelude.Left ((,)
                        (option_branch (\x1 ->
                          (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                            (\_ -> Prelude.Right (Prelude.Right (Prelude.Right
                            (Prelude.Right (Prelude.Right (Prelude.Right
                            (Prelude.Right (Prelude.Right (Prelude.Right
                            (Prelude.Right (Prelude.Right (Prelude.Right
                            (Prelude.Right GHC.Base.Nothing)))))))))))))
                            (\n0' -> Prelude.Right (Prelude.Left ((,) ((,) () n0')
                            ((,) ((,) ((,) ((,) ((,) o o0) (GHC.Base.Just ((,) r0
                            p))) (mconcat ((:) b ((:) x1 [])))) r) d))))
                            n)
                          (option_branch (\x1 -> Prelude.Right (Prelude.Right
                            (Prelude.Right (Prelude.Left ((,) () x1)))))
                            (Prelude.Right (Prelude.Right (Prelude.Right
                            (Prelude.Right (Prelude.Right (Prelude.Right
                            (Prelude.Right (Prelude.Right (Prelude.Right
                            (Prelude.Right (Prelude.Right (Prelude.Right
                            (Prelude.Right
                            (inhabitant option_inhabitant))))))))))))))
                            (retAlert r1)) (fromRecvData r1))
                        (option_branch (\_ ->
                          (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                            (\_ -> GHC.Base.Nothing)
                            (\_ -> GHC.Base.Just (ExistT __ (GetRandomBytes 0)))
                            n)
                          (option_branch (\x1 -> GHC.Base.Just (ExistT __ (CloseWith
                            x1))) GHC.Base.Nothing (retAlert r1)) (fromRecvData r1))))))))))))
        (sum_merge
          (prod_curry (\_ _ _ _ -> Prelude.Left ((,) (Prelude.Right (Prelude.Right
            (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
            (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
            (Prelude.Right (Prelude.Right (Prelude.Right
            (inhabitant option_inhabitant)))))))))))))) GHC.Base.Nothing)))
          (sum_merge
            (prod_curry
              (prod_curry
                (prod_curry
                  (prod_curry
                    (prod_curry
                      (prod_curry
                        (prod_curry
                          (prod_curry (\_ n d r b o o0 r0 p _ r1 -> Prelude.Left
                            ((,)
                            (option_branch (\x1 ->
                              (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                (\_ -> Prelude.Right (Prelude.Right (Prelude.Right
                                (Prelude.Right (Prelude.Right (Prelude.Right
                                (Prelude.Right (Prelude.Right (Prelude.Right
                                (Prelude.Right (Prelude.Right (Prelude.Right
                                (Prelude.Right GHC.Base.Nothing)))))))))))))
                                (\n0' -> Prelude.Right (Prelude.Left ((,) ((,) ()
                                n0') ((,) ((,) ((,) ((,) ((,) o o0) (GHC.Base.Just
                                ((,) r0 p))) (mconcat ((:) b ((:) x1 [])))) r)
                                d))))
                                n)
                              (option_branch (\x1 -> Prelude.Right (Prelude.Right
                                (Prelude.Right (Prelude.Right (Prelude.Right
                                (Prelude.Left ((,) () x1))))))) (Prelude.Right
                                (Prelude.Right (Prelude.Right (Prelude.Right
                                (Prelude.Right (Prelude.Right (Prelude.Right
                                (Prelude.Right (Prelude.Right (Prelude.Right
                                (Prelude.Right (Prelude.Right (Prelude.Right
                                (inhabitant option_inhabitant))))))))))))))
                                (retAlert r1)) (fromRecvData r1))
                            (option_branch (\_ ->
                              (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                (\_ -> GHC.Base.Nothing)
                                (\_ -> GHC.Base.Just (ExistT __ (GetRandomBytes
                                0)))
                                n)
                              (option_branch (\x1 -> GHC.Base.Just (ExistT __
                                (CloseWith x1))) GHC.Base.Nothing (retAlert r1))
                              (fromRecvData r1))))))))))))
            (sum_merge
              (prod_curry (\_ _ _ _ -> Prelude.Left ((,) (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                (inhabitant option_inhabitant)))))))))))))) GHC.Base.Nothing)))
              (sum_merge
                (prod_curry
                  (prod_curry
                    (prod_curry
                      (prod_curry
                        (prod_curry
                          (prod_curry
                            (prod_curry (\_ n b o d _ p n0 _ r -> Prelude.Left ((,)
                              ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                 (\_ -> Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right
                                 GHC.Base.Nothing)))))))))))))
                                 (\n0' -> Prelude.Right (Prelude.Left ((,) ((,) ()
                                 n0') ((,) ((,) ((,) ((,) ((,) o (GHC.Base.Just ((,)
                                 p ((Prelude.+) 1 n0)))) GHC.Base.Nothing) b) r)
                                 d))))
                                 n)
                              ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                 (\_ -> GHC.Base.Nothing)
                                 (\_ -> GHC.Base.Just (ExistT __ (GetRandomBytes
                                 0)))
                                 n))))))))))
                (sum_merge
                  (prod_curry
                    (prod_curry
                      (prod_curry
                        (prod_curry
                          (prod_curry (\_ n b o d _ _ r -> Prelude.Left ((,)
                            ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                               (\_ -> Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right GHC.Base.Nothing)))))))))))))
                               (\n0' -> Prelude.Right (Prelude.Left ((,) ((,) ()
                               n0') ((,) ((,) ((,) ((,) ((,) o GHC.Base.Nothing)
                               GHC.Base.Nothing) b) r) d))))
                               n)
                            ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                               (\_ -> GHC.Base.Nothing)
                               (\_ -> GHC.Base.Just (ExistT __ (GetRandomBytes 0)))
                               n))))))))
                  (sum_merge
                    (prod_curry
                      (prod_curry
                        (prod_curry
                          (prod_curry
                            (prod_curry
                              (prod_curry
                                (prod_curry (\_ n b o d p p0 n0 _ _ -> Prelude.Left
                                  ((,) (Prelude.Right (Prelude.Right (Prelude.Right
                                  (Prelude.Right (Prelude.Right (Prelude.Right
                                  (Prelude.Right (Prelude.Right (Prelude.Right
                                  (Prelude.Left ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                  () n) b) o) d) p) p0) n0))))))))))) (GHC.Base.Just
                                  (ExistT __ (CloseWith p))))))))))))
                    (sum_merge
                      (prod_curry
                        (prod_curry
                          (prod_curry
                            (prod_curry
                              (prod_curry
                                (prod_curry
                                  (prod_curry (\_ n b o d _ p n0 _ r -> Prelude.Left
                                    ((,)
                                    ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                       (\_ -> Prelude.Right (Prelude.Right
                                       (Prelude.Right (Prelude.Right (Prelude.Right
                                       (Prelude.Right (Prelude.Right (Prelude.Right
                                       (Prelude.Right (Prelude.Right (Prelude.Right
                                       (Prelude.Right (Prelude.Right
                                       GHC.Base.Nothing)))))))))))))
                                       (\n0' -> Prelude.Right (Prelude.Left ((,)
                                       ((,) () n0') ((,) ((,) ((,) ((,) ((,) o
                                       (GHC.Base.Just ((,) p ((Prelude.+) 1 n0))))
                                       GHC.Base.Nothing) b) r) d))))
                                       n)
                                    ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                       (\_ -> GHC.Base.Nothing)
                                       (\_ -> GHC.Base.Just (ExistT __
                                       (GetRandomBytes 0)))
                                       n))))))))))
                      (sum_merge
                        (prod_curry
                          (prod_curry
                            (prod_curry
                              (prod_curry
                                (prod_curry (\_ n b o d p _ _ -> Prelude.Left ((,)
                                  (Prelude.Right (Prelude.Right (Prelude.Right
                                  (Prelude.Right (Prelude.Right (Prelude.Right
                                  (Prelude.Right (Prelude.Right (Prelude.Right
                                  (Prelude.Right (Prelude.Right (Prelude.Left ((,)
                                  ((,) ((,) ((,) ((,) () n) b) o) d) p)))))))))))))
                                  (GHC.Base.Just (ExistT __ (CloseWith p))))))))))
                        (sum_merge
                          (prod_curry
                            (prod_curry
                              (prod_curry
                                (prod_curry
                                  (prod_curry (\_ n b o d _ _ r -> Prelude.Left ((,)
                                    ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                       (\_ -> Prelude.Right (Prelude.Right
                                       (Prelude.Right (Prelude.Right (Prelude.Right
                                       (Prelude.Right (Prelude.Right (Prelude.Right
                                       (Prelude.Right (Prelude.Right (Prelude.Right
                                       (Prelude.Right (Prelude.Right
                                       GHC.Base.Nothing)))))))))))))
                                       (\n0' -> Prelude.Right (Prelude.Left ((,)
                                       ((,) () n0') ((,) ((,) ((,) ((,) ((,) o
                                       GHC.Base.Nothing) GHC.Base.Nothing) b) r)
                                       d))))
                                       n)
                                    ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                       (\_ -> GHC.Base.Nothing)
                                       (\_ -> GHC.Base.Just (ExistT __
                                       (GetRandomBytes 0)))
                                       n))))))))
                          (sum_merge
                            (prod_curry
                              (prod_curry
                                (prod_curry
                                  (prod_curry
                                    (prod_curry
                                      (prod_curry (\_ n b o o0 d _ _ r ->
                                        Prelude.Left ((,)
                                        ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                           (\_ -> Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right (Prelude.Right
                                           (Prelude.Right
                                           GHC.Base.Nothing)))))))))))))
                                           (\n0' -> Prelude.Right (Prelude.Left ((,)
                                           ((,) () n0') ((,) ((,) ((,) ((,) ((,) o
                                           o0) GHC.Base.Nothing) b) r) d))))
                                           n)
                                        ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                           (\_ -> GHC.Base.Nothing)
                                           (\_ -> GHC.Base.Just (ExistT __
                                           (GetRandomBytes 0)))
                                           n))))))))) (\o _ _ -> Prelude.Right o)))))))))))))
    x __ x0

data Eff_conn =
   Accept
 | Perform
 | Receive
 | Skip

type Args_conn = Any

type Rets_conn = Any

isSetPSK :: Args_tls -> GHC.Base.Maybe ((,) Prelude.String I.SessionData)
isSetPSK x =
  case x of {
   SetPSK a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

isSessionResume :: Args_tls -> GHC.Base.Maybe Prelude.String
isSessionResume x =
  case x of {
   SessionResume a -> GHC.Base.Just a;
   _ -> GHC.Base.Nothing}

take_max :: ((,) Prelude.String a1) -> (Map a1) -> (Map a1) -> ((Map a1) -> Map 
            a1) -> (,) ((,) Prelude.String a1) (Map a1)
take_max d m' m ctx =
  case m of {
   Node d' l r -> take_max d' l r (\x -> ctx (Node d m' x));
   Leaf -> (,) d (ctx m')}

merge_map :: (Map a1) -> (Map a1) -> Map a1
merge_map l r =
  case l of {
   Node d l' r' -> case take_max d l' r' (\x -> x) of {
                    (,) d' m -> Node d' m r};
   Leaf -> r}

lookupAndDelete' :: Prelude.String -> (Map a1) -> ((Map a1) -> Map a1) -> (,)
                    (GHC.Base.Maybe a1) (Map a1)
lookupAndDelete' key m ctx =
  case m of {
   Node p l r ->
    case p of {
     (,) k v ->
      case compareString key k of {
       Eq -> (,) (GHC.Base.Just v) (ctx (merge_map l r));
       Lt -> lookupAndDelete' key l (\x -> ctx (Node ((,) k v) x r));
       Gt -> lookupAndDelete' key r (\x -> ctx (Node ((,) k v) l x))}};
   Leaf -> (,) GHC.Base.Nothing (ctx Leaf)}

lookupAndDelete :: Prelude.String -> (Map a1) -> (,) (GHC.Base.Maybe a1) (Map a1)
lookupAndDelete key m =
  lookupAndDelete' key m (\x -> x)

lift_conn :: Eff_conn -> (Rets_conn -> Prelude.Either a1 (GHC.Base.Maybe a2)) ->
             Eff_conn -> Rets_conn -> Prelude.Either a1 (GHC.Base.Maybe a2)
lift_conn e a e0 =
  case e of {
   Accept -> case e0 of {
              Accept -> a;
              _ -> (\_ -> Prelude.Right GHC.Base.Nothing)};
   Perform ->
    case e0 of {
     Perform -> a;
     _ -> (\_ -> Prelude.Right GHC.Base.Nothing)};
   Receive ->
    case e0 of {
     Receive -> a;
     _ -> (\_ -> Prelude.Right GHC.Base.Nothing)};
   Skip -> case e0 of {
            Skip -> a;
            _ -> (\_ -> Prelude.Right GHC.Base.Nothing)}}

main_loop_step :: (Prelude.Either
                  ((,)
                  ((,) ((,) ((,) ((,) () GHC.Base.Int) GHC.Base.Int) GHC.Base.Int)
                  CertificateChain) PrivateKey)
                  (Prelude.Either
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,) ((,) ((,) () GHC.Base.Int) GHC.Base.Int) CertificateChain)
                  PrivateKey) GHC.Base.Int) (Map I.SessionData))
                  (Map ReadWrite_state))
                  (Prelude.Either
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,) ((,) ((,) () GHC.Base.Int) GHC.Base.Int) CertificateChain)
                  PrivateKey) GHC.Base.Int) (Map I.SessionData))
                  (Map ReadWrite_state)) Prelude.String) ReadWrite_state) Args_tls)
                  (Prelude.Either
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,) ((,) ((,) () GHC.Base.Int) GHC.Base.Int) CertificateChain)
                  PrivateKey) GHC.Base.Int) (Map I.SessionData))
                  (Map ReadWrite_state))
                  (Prelude.Either
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,) ((,) ((,) () GHC.Base.Int) GHC.Base.Int) CertificateChain)
                  PrivateKey) GHC.Base.Int) (Map ReadWrite_state)) Prelude.String)
                  GHC.Base.Int) (Map I.SessionData)) ReadWrite_state) Args_tls)
                  (Prelude.Either
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,) ((,) ((,) () GHC.Base.Int) GHC.Base.Int) CertificateChain)
                  PrivateKey) GHC.Base.Int) (Map ReadWrite_state)) Prelude.String)
                  (Map I.SessionData)) ReadWrite_state) Args_tls)
                  (GHC.Base.Maybe ()))))))) -> Eff_conn -> Rets_conn ->
                  Prelude.Either
                  ((,)
                  (Prelude.Either
                  ((,)
                  ((,) ((,) ((,) ((,) () GHC.Base.Int) GHC.Base.Int) GHC.Base.Int)
                  CertificateChain) PrivateKey)
                  (Prelude.Either
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,) ((,) ((,) () GHC.Base.Int) GHC.Base.Int) CertificateChain)
                  PrivateKey) GHC.Base.Int) (Map I.SessionData))
                  (Map ReadWrite_state))
                  (Prelude.Either
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,) ((,) ((,) () GHC.Base.Int) GHC.Base.Int) CertificateChain)
                  PrivateKey) GHC.Base.Int) (Map I.SessionData))
                  (Map ReadWrite_state)) Prelude.String) ReadWrite_state) Args_tls)
                  (Prelude.Either
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,) ((,) ((,) () GHC.Base.Int) GHC.Base.Int) CertificateChain)
                  PrivateKey) GHC.Base.Int) (Map I.SessionData))
                  (Map ReadWrite_state))
                  (Prelude.Either
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,) ((,) ((,) () GHC.Base.Int) GHC.Base.Int) CertificateChain)
                  PrivateKey) GHC.Base.Int) (Map ReadWrite_state)) Prelude.String)
                  GHC.Base.Int) (Map I.SessionData)) ReadWrite_state) Args_tls)
                  (Prelude.Either
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,)
                  ((,) ((,) ((,) () GHC.Base.Int) GHC.Base.Int) CertificateChain)
                  PrivateKey) GHC.Base.Int) (Map ReadWrite_state)) Prelude.String)
                  (Map I.SessionData)) ReadWrite_state) Args_tls)
                  (GHC.Base.Maybe ())))))))
                  (GHC.Base.Maybe (SigT Eff_conn Args_conn))) (GHC.Base.Maybe ())
main_loop_step =
  sum_merge
    (prod_curry
      (prod_curry
        (prod_curry
          (prod_curry
            (prod_curry (\_ n n0 n1 c p _ _ -> Prelude.Left ((,)
              ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                 (\_ -> Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                 (Prelude.Right (Prelude.Right GHC.Base.Nothing))))))
                 (\n2 -> Prelude.Right (Prelude.Left ((,) ((,) ((,) ((,) ((,) ((,)
                 ((,) () n0) n1) c) p) n2) Leaf) Leaf)))
                 n)
              ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                 (\_ -> GHC.Base.Nothing)
                 (\_ -> GHC.Base.Just (ExistT Accept (unsafeCoerce ())))
                 n))))))))
    (sum_merge
      (prod_curry
        (prod_curry
          (prod_curry
            (prod_curry
              (prod_curry
                (prod_curry
                  (prod_curry (\_ n n0 c p n1 m m0 ->
                    lift_conn Accept (\r -> Prelude.Left ((,)
                      (option_branch (\x0 ->
                        case readWrite_step (Prelude.Left ((,) ((,) ((,) () n) c)
                               p)) (inhabitant sigT_rets_inhabit) of {
                         Prelude.Left p0 ->
                          case p0 of {
                           (,) s o ->
                            case o of {
                             GHC.Base.Just s0 ->
                              case s0 of {
                               ExistT _ v -> Prelude.Right (Prelude.Right
                                (Prelude.Left ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                ((,) ((,) ((,) () n) n0) c) p) n1) m) m0) x0) s)
                                v)))};
                             GHC.Base.Nothing -> Prelude.Right (Prelude.Right
                              (Prelude.Right (Prelude.Right (Prelude.Right
                              (Prelude.Right GHC.Base.Nothing)))))}};
                         Prelude.Right _ -> Prelude.Right (Prelude.Right
                          (Prelude.Right (Prelude.Right (Prelude.Right
                          (Prelude.Right GHC.Base.Nothing)))))}) (Prelude.Right
                        (Prelude.Right (Prelude.Right (Prelude.Left ((,) ((,) ((,)
                        ((,) ((,) ((,) ((,) () n) n0) c) p) n1) m) m0)))))
                        (unsafeCoerce r))
                      (option_branch (\x0 ->
                        case readWrite_step (Prelude.Left ((,) ((,) ((,) () n) c)
                               p)) (inhabitant sigT_rets_inhabit) of {
                         Prelude.Left p0 ->
                          case p0 of {
                           (,) _ o ->
                            case o of {
                             GHC.Base.Just s0 ->
                              case s0 of {
                               ExistT _ v -> GHC.Base.Just (ExistT Perform
                                (unsafeCoerce ((,) x0 v)))};
                             GHC.Base.Nothing -> GHC.Base.Nothing}};
                         Prelude.Right _ -> GHC.Base.Nothing}) (GHC.Base.Just
                        (ExistT Receive (unsafeCoerce ()))) (unsafeCoerce r))))))))))))
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
                          (prod_curry (\_ n n0 c p n1 m m0 s r _ ->
                            lift_conn Perform (\_ -> Prelude.Left ((,)
                              ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                 (\_ -> Prelude.Right (Prelude.Right (Prelude.Right
                                 (Prelude.Right (Prelude.Right (Prelude.Right
                                 GHC.Base.Nothing))))))
                                 (\n0' -> Prelude.Right (Prelude.Left ((,) ((,) ((,)
                                 ((,) ((,) ((,) ((,) () n) n0) c) p) n0') m)
                                 (insert s r m0))))
                                 n1)
                              ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                 (\_ -> GHC.Base.Nothing)
                                 (\_ -> GHC.Base.Just (ExistT Accept
                                 (unsafeCoerce ())))
                                 n1))))))))))))))
        (sum_merge
          (prod_curry
            (prod_curry
              (prod_curry
                (prod_curry
                  (prod_curry
                    (prod_curry
                      (prod_curry (\_ n n0 c p n1 m m0 ->
                        lift_conn Receive (\r -> Prelude.Left ((,)
                          (option_branch (\x0 ->
                            case x0 of {
                             (,) a b ->
                              option_branch (\x1 ->
                                (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                  (\_ -> Prelude.Right (Prelude.Right (Prelude.Right
                                  (Prelude.Right (Prelude.Right (Prelude.Right
                                  GHC.Base.Nothing))))))
                                  (\n2 ->
                                  case readWrite_step x1 b of {
                                   Prelude.Left p0 ->
                                    case p0 of {
                                     (,) s o ->
                                      case o of {
                                       GHC.Base.Just s0 ->
                                        case s0 of {
                                         ExistT _ v -> Prelude.Right (Prelude.Right
                                          (Prelude.Right (Prelude.Right
                                          (Prelude.Left ((,) ((,) ((,) ((,) ((,)
                                          ((,) ((,) ((,) ((,) ((,) ((,) () n) n0) c)
                                          p) n1) m0) a) n2) m) s) v)))))};
                                       GHC.Base.Nothing -> Prelude.Right
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Right
                                        GHC.Base.Nothing)))))}};
                                   Prelude.Right _ -> Prelude.Right (Prelude.Right
                                    (Prelude.Right (Prelude.Right (Prelude.Right
                                    (Prelude.Right GHC.Base.Nothing)))))})
                                  n0)
                                ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                   (\_ -> Prelude.Right (Prelude.Right
                                   (Prelude.Right (Prelude.Right (Prelude.Right
                                   (Prelude.Right GHC.Base.Nothing))))))
                                   (\n0' -> Prelude.Right (Prelude.Left ((,) ((,)
                                   ((,) ((,) ((,) ((,) ((,) () n) n0) c) p) n0') m)
                                   m0)))
                                   n1) (bsearch a m0)})
                            ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                               (\_ -> Prelude.Right (Prelude.Right (Prelude.Right
                               (Prelude.Right (Prelude.Right (Prelude.Right
                               GHC.Base.Nothing))))))
                               (\n0' -> Prelude.Right (Prelude.Left ((,) ((,) ((,)
                               ((,) ((,) ((,) ((,) () n) n0) c) p) n0') m) m0)))
                               n1) (unsafeCoerce r))
                          (option_branch (\x0 ->
                            case x0 of {
                             (,) a b ->
                              option_branch (\x1 ->
                                (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                  (\_ -> GHC.Base.Nothing)
                                  (\_ ->
                                  case readWrite_step x1 b of {
                                   Prelude.Left p0 ->
                                    case p0 of {
                                     (,) _ o ->
                                      case o of {
                                       GHC.Base.Just _ -> GHC.Base.Just (ExistT Skip
                                        (unsafeCoerce ()));
                                       GHC.Base.Nothing -> GHC.Base.Nothing}};
                                   Prelude.Right _ -> GHC.Base.Nothing})
                                  n0)
                                ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                   (\_ -> GHC.Base.Nothing)
                                   (\_ -> GHC.Base.Just (ExistT Accept
                                   (unsafeCoerce ())))
                                   n1) (bsearch a m0)})
                            ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                               (\_ -> GHC.Base.Nothing)
                               (\_ -> GHC.Base.Just (ExistT Accept
                               (unsafeCoerce ())))
                               n1) (unsafeCoerce r))))))))))))
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
                                (prod_curry (\_ n n0 c p n1 m s n2 m0 r a ->
                                  lift_conn Skip (\_ -> Prelude.Left ((,)
                                    (option_branch (\x0 ->
                                      case x0 of {
                                       (,) a0 b ->
                                        (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                          (\_ -> Prelude.Right (Prelude.Right
                                          (Prelude.Right (Prelude.Right
                                          (Prelude.Right (Prelude.Right
                                          GHC.Base.Nothing))))))
                                          (\n0' ->
                                          case readWrite_step r FromSetPSK of {
                                           Prelude.Left p0 ->
                                            case p0 of {
                                             (,) s0 o ->
                                              case o of {
                                               GHC.Base.Just s1 ->
                                                case s1 of {
                                                 ExistT _ v -> Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Left ((,)
                                                  ((,) ((,) ((,) ((,) ((,) ((,) ((,)
                                                  ((,) ((,) ((,) () n) n0) c) p) n1)
                                                  m) s) n0') (insert a0 b m0)) s0)
                                                  v)))))};
                                               GHC.Base.Nothing -> Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right (Prelude.Right
                                                (Prelude.Right GHC.Base.Nothing)))))}};
                                           Prelude.Right _ -> Prelude.Right
                                            (Prelude.Right (Prelude.Right
                                            (Prelude.Right (Prelude.Right
                                            (Prelude.Right GHC.Base.Nothing)))))})
                                          n2})
                                      (option_branch (\x0 ->
                                        case lookupAndDelete x0 m0 of {
                                         (,) a0 b ->
                                          (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                            (\_ -> Prelude.Right (Prelude.Right
                                            (Prelude.Right (Prelude.Right
                                            (Prelude.Right (Prelude.Right
                                            GHC.Base.Nothing))))))
                                            (\n0' ->
                                            case readWrite_step r (FromSessionResume
                                                   a0) of {
                                             Prelude.Left p0 ->
                                              case p0 of {
                                               (,) s0 o ->
                                                case o of {
                                                 GHC.Base.Just s1 ->
                                                  case s1 of {
                                                   ExistT _ v -> Prelude.Right
                                                    (Prelude.Right (Prelude.Right
                                                    (Prelude.Right (Prelude.Left
                                                    ((,) ((,) ((,) ((,) ((,) ((,)
                                                    ((,) ((,) ((,) ((,) ((,) () n)
                                                    n0) c) p) n1) m) s) n0') b) s0)
                                                    v)))))};
                                                 GHC.Base.Nothing -> Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right (Prelude.Right
                                                  (Prelude.Right
                                                  GHC.Base.Nothing)))))}};
                                             Prelude.Right _ -> Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right (Prelude.Right
                                              (Prelude.Right GHC.Base.Nothing)))))})
                                            n2}) (Prelude.Right (Prelude.Right
                                        (Prelude.Right (Prelude.Right (Prelude.Right
                                        (Prelude.Left ((,) ((,) ((,) ((,) ((,) ((,)
                                        ((,) ((,) ((,) ((,) () n) n0) c) p) n1) m)
                                        s) m0) r) a))))))) (isSessionResume a))
                                      (isSetPSK a))
                                    (option_branch (\_ ->
                                      (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                        (\_ -> GHC.Base.Nothing)
                                        (\_ ->
                                        case readWrite_step r FromSetPSK of {
                                         Prelude.Left p0 ->
                                          case p0 of {
                                           (,) _ o ->
                                            case o of {
                                             GHC.Base.Just _ -> GHC.Base.Just
                                              (ExistT Skip (unsafeCoerce ()));
                                             GHC.Base.Nothing -> GHC.Base.Nothing}};
                                         Prelude.Right _ -> GHC.Base.Nothing})
                                        n2)
                                      (option_branch (\x0 ->
                                        case lookupAndDelete x0 m0 of {
                                         (,) a0 _ ->
                                          (\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                            (\_ -> GHC.Base.Nothing)
                                            (\_ ->
                                            case readWrite_step r (FromSessionResume
                                                   a0) of {
                                             Prelude.Left p0 ->
                                              case p0 of {
                                               (,) _ o ->
                                                case o of {
                                                 GHC.Base.Just _ -> GHC.Base.Just
                                                  (ExistT Skip (unsafeCoerce ()));
                                                 GHC.Base.Nothing ->
                                                  GHC.Base.Nothing}};
                                             Prelude.Right _ -> GHC.Base.Nothing})
                                            n2}) (GHC.Base.Just (ExistT Perform
                                        (unsafeCoerce ((,) s a))))
                                        (isSessionResume a)) (isSetPSK a))))))))))))))))
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
                                (prod_curry (\_ n n0 c p n1 m s m0 r _ ->
                                  lift_conn Perform (\_ -> Prelude.Left ((,)
                                    ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                       (\_ -> Prelude.Right (Prelude.Right
                                       (Prelude.Right (Prelude.Right (Prelude.Right
                                       (Prelude.Right GHC.Base.Nothing))))))
                                       (\n0' -> Prelude.Right (Prelude.Left ((,)
                                       ((,) ((,) ((,) ((,) ((,) ((,) () n) n0) c) p)
                                       n0') m0) (replace_map s r m))))
                                       n1)
                                    ((\fO fS n -> if n GHC.Base.==0 then fO () else fS (n Prelude.- 1))
                                       (\_ -> GHC.Base.Nothing)
                                       (\_ -> GHC.Base.Just (ExistT Accept
                                       (unsafeCoerce ())))
                                       n1)))))))))))))) (\o _ _ -> Prelude.Right o))))))

