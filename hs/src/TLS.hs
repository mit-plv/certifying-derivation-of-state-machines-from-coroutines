{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module TLS where

import qualified Prelude
import qualified Network.TLS as T
import qualified Network.TLS.Internal as I
import qualified Data.ByteString as B
import qualified Helper

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

kSgroup :: I.KeyShareEntry -> T.Group
kSgroup k =
  case k of {
   I.KeyShareEntry kSgroup0 _ -> kSgroup0}

type ExtensionRaw = I.ExtensionRaw

type Session = I.Session

type CipherID = T.CipherID

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
    case find (\k -> group_beq (kSgroup k) g) ks of {
     GHC.Base.Just k -> GHC.Base.Just k;
     GHC.Base.Nothing -> findKeyShare ks gs'}}

extension_KeyShare :: (([]) ExtensionRaw) -> GHC.Base.Maybe (([]) I.KeyShareEntry)
extension_KeyShare = (\exts -> case Helper.extensionLookup I.extensionID_KeyShare exts GHC.Base.>>= I.extensionDecode I.MsgTClientHello of { GHC.Base.Just (I.KeyShareClientHello kses) -> GHC.Base.return kses})

type Handshake13 = I.Handshake13

type Packet13 = I.Packet13

data Eff_tls =
   RecvClientHello
 | GetRandomBytes
 | SendPacket

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
   GetRandomBytes ->
    case e0 of {
     GetRandomBytes -> a;
     _ -> (\_ -> Prelude.Right GHC.Base.Nothing)};
   SendPacket ->
    case e0 of {
     SendPacket -> a;
     _ -> (\_ -> Prelude.Right GHC.Base.Nothing)}}

type Version = T.Version

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

doHandshake_step :: (Prelude.Either ()
                    (Prelude.Either ()
                    (Prelude.Either ((,) ((,) () ClientHelloMsg) I.KeyShareEntry)
                    (Prelude.Either
                    ((,) ((,) ((,) () ClientHelloMsg) I.KeyShareEntry) CipherID)
                    (Prelude.Either
                    ((,)
                    ((,) ((,) ((,) () ClientHelloMsg) I.KeyShareEntry) CipherID)
                    ByteString) (GHC.Base.Maybe ())))))) -> Eff_tls -> Rets_tls ->
                    Prelude.Either
                    ((,)
                    (Prelude.Either ()
                    (Prelude.Either ()
                    (Prelude.Either ((,) ((,) () ClientHelloMsg) I.KeyShareEntry)
                    (Prelude.Either
                    ((,) ((,) ((,) () ClientHelloMsg) I.KeyShareEntry) CipherID)
                    (Prelude.Either
                    ((,)
                    ((,) ((,) ((,) () ClientHelloMsg) I.KeyShareEntry) CipherID)
                    ByteString) (GHC.Base.Maybe ()))))))
                    (GHC.Base.Maybe (SigT Eff_tls Args_tls))) (GHC.Base.Maybe ())
doHandshake_step =
  sum_merge (\_ _ _ -> Prelude.Left ((,) (Prelude.Right (Prelude.Left ()))
    (GHC.Base.Just (ExistT RecvClientHello (unsafeCoerce ())))))
    (sum_merge (\_ ->
      lift_tls RecvClientHello (\r -> Prelude.Left ((,)
        (case extension_KeyShare (chExtension (unsafeCoerce r)) of {
          GHC.Base.Just a ->
           case findKeyShare a serverGroups of {
            GHC.Base.Just a0 -> Prelude.Right (Prelude.Right (Prelude.Left ((,) ((,)
             () (unsafeCoerce r)) a0)));
            GHC.Base.Nothing -> Prelude.Right (Prelude.Right (Prelude.Right
             (Prelude.Right (Prelude.Right GHC.Base.Nothing))))};
          GHC.Base.Nothing -> Prelude.Right (Prelude.Right (Prelude.Right
           (Prelude.Right (Prelude.Right GHC.Base.Nothing))))})
        (case extension_KeyShare (chExtension (unsafeCoerce r)) of {
          GHC.Base.Just a ->
           case findKeyShare a serverGroups of {
            GHC.Base.Just _ -> GHC.Base.Just (ExistT GetRandomBytes
             (unsafeCoerce ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
               ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
               ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
               ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
               ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
               ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
               ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
               ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
               ((Prelude.+) 1 0))))))))))))))))))))))))))))))))));
            GHC.Base.Nothing -> GHC.Base.Nothing};
          GHC.Base.Nothing -> GHC.Base.Nothing}))))
      (sum_merge
        (prod_curry
          (prod_curry (\_ r k ->
            lift_tls GetRandomBytes (\_ -> Prelude.Left ((,)
              (case hd_error (chCiphers r) of {
                GHC.Base.Just a -> Prelude.Right (Prelude.Right (Prelude.Right
                 (Prelude.Left ((,) ((,) ((,) () r) k) a))));
                GHC.Base.Nothing -> Prelude.Right (Prelude.Right (Prelude.Right
                 (Prelude.Right (Prelude.Right GHC.Base.Nothing))))})
              (case hd_error (chCiphers r) of {
                GHC.Base.Just _ -> GHC.Base.Just (ExistT GetRandomBytes
                 (unsafeCoerce ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                   ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1 ((Prelude.+) 1
                   ((Prelude.+) 1 0))))))))))))))))))))))))))))))))));
                GHC.Base.Nothing -> GHC.Base.Nothing}))))))
        (sum_merge
          (prod_curry
            (prod_curry
              (prod_curry (\_ r k c ->
                lift_tls GetRandomBytes (\r0 -> Prelude.Left ((,) (Prelude.Right
                  (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Left ((,)
                  ((,) ((,) ((,) () r) k) c) (unsafeCoerce r0))))))) (GHC.Base.Just
                  (ExistT SendPacket
                  (unsafeCoerce handshake13 ((:)
                    (serverHello13 (unsafeCoerce r0) (chSession r) c ((:)
                      (extensionRaw_KeyShare (extensionEncode_KeyShare k)) ((:)
                      (extensionRaw_SupportedVersions
                        (extensionEncode_SupportedVersions tLS13)) []))) []))))))))))
          (sum_merge
            (prod_curry
              (prod_curry
                (prod_curry
                  (prod_curry (\_ _ _ _ _ ->
                    lift_tls SendPacket (\_ -> Prelude.Left ((,) (Prelude.Right
                      (Prelude.Right (Prelude.Right (Prelude.Right (Prelude.Right
                      (GHC.Base.Just ())))))) GHC.Base.Nothing))))))) (\o _ _ ->
            Prelude.Right o)))))

