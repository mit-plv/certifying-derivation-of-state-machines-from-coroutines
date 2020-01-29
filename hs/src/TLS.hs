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

list_rect :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rect f f0 l =
  case l of {
   [] -> f;
   (:) y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rec =
  list_rect

data SigT a p =
   ExistT a p

hd_error :: (([]) a1) -> GHC.Base.Maybe a1
hd_error l =
  case l of {
   [] -> GHC.Base.Nothing;
   (:) x _ -> GHC.Base.Just x}

in_dec :: (a1 -> a1 -> GHC.Base.Bool) -> a1 -> (([]) a1) -> GHC.Base.Bool
in_dec h a l =
  list_rec GHC.Base.False (\a0 _ iHl ->
    let {s = h a0 a} in
    case s of {
     GHC.Base.True -> GHC.Base.True;
     GHC.Base.False -> iHl}) l

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

type String = B.ByteString

group_beq :: T.Group -> T.Group -> GHC.Base.Bool
group_beq = (GHC.Base.==)

group_eq_dec :: T.Group -> T.Group -> GHC.Base.Bool
group_eq_dec = (GHC.Base.==)

kSgroup :: Helper.KeyShare -> T.Group
kSgroup k =
  case k of {
   Helper.Build_KeyShare kSgroup0 _ -> kSgroup0}

type ExtensionRaw = I.ExtensionRaw

type ClientHelloMsg =
  ([]) ExtensionRaw
  -- singleton inductive, whose constructor was Build_ClientHelloMsg
  
cHextension :: ClientHelloMsg -> ([]) ExtensionRaw
cHextension c =
  c

type Context = T.Context

serverGroups :: Context -> ([]) T.Group
serverGroups = Helper.serverGroups

findKeyShare :: (([]) Helper.KeyShare) -> (([]) T.Group) -> GHC.Base.Maybe
                Helper.KeyShare
findKeyShare ks gs =
  case gs of {
   [] -> GHC.Base.Nothing;
   (:) g gs' ->
    case find (\k -> group_beq (kSgroup k) g) ks of {
     GHC.Base.Just k -> GHC.Base.Just k;
     GHC.Base.Nothing -> findKeyShare ks gs'}}

intersect :: (([]) T.Group) -> (([]) T.Group) -> ([]) T.Group
intersect xs ys =
  filter (\x ->
    case in_dec group_eq_dec x ys of {
     GHC.Base.True -> GHC.Base.True;
     GHC.Base.False -> GHC.Base.False}) xs

extension_KeyShare :: (([]) ExtensionRaw) -> GHC.Base.Maybe (([]) Helper.KeyShare)
extension_KeyShare = Helper.extension_KeyShare

extension_NegotiatedGroups :: (([]) ExtensionRaw) -> ([]) T.Group
extension_NegotiatedGroups = Helper.extension_NegotiatedGroups

data Eff_tls =
   RecvClientHello
 | GenerateRND

type Args_tls = Any

type Rets_tls = Any

lift_tls :: Eff_tls -> (Rets_tls -> Prelude.Either a1 (GHC.Base.Maybe a2)) ->
            Eff_tls -> Rets_tls -> Prelude.Either a1 (GHC.Base.Maybe a2)
lift_tls e a e0 =
  case e of {
   RecvClientHello ->
    case e0 of {
     RecvClientHello -> a;
     GenerateRND -> (\_ -> Prelude.Right GHC.Base.Nothing)};
   GenerateRND ->
    case e0 of {
     RecvClientHello -> (\_ -> Prelude.Right GHC.Base.Nothing);
     GenerateRND -> a}}

pickKeyShare_step :: (Prelude.Either ((,) () Context)
                     (Prelude.Either ((,) () Context)
                     (Prelude.Either ((,) () Context)
                     (GHC.Base.Maybe ((,) ClientHelloMsg Helper.KeyShare))))) ->
                     Eff_tls -> Rets_tls -> Prelude.Either
                     ((,)
                     (Prelude.Either ((,) () Context)
                     (Prelude.Either ((,) () Context)
                     (Prelude.Either ((,) () Context)
                     (GHC.Base.Maybe ((,) ClientHelloMsg Helper.KeyShare)))))
                     (GHC.Base.Maybe (SigT Eff_tls Args_tls)))
                     (GHC.Base.Maybe ((,) ClientHelloMsg Helper.KeyShare))
pickKeyShare_step ctx =
  sum_merge
    (prod_curry (\_ c _ _ -> Prelude.Left ((,) (Prelude.Right (Prelude.Left ((,) ()
      c))) (GHC.Base.Just (ExistT RecvClientHello (unsafeCoerce c))))))
    (sum_merge
      (prod_curry (\_ c ->
        lift_tls RecvClientHello (\r -> Prelude.Left ((,)
          (case extension_KeyShare (cHextension (unsafeCoerce r)) of {
            GHC.Base.Just a ->
             case findKeyShare a (serverGroups c) of {
              GHC.Base.Just a0 -> Prelude.Right (Prelude.Right (Prelude.Right
               (GHC.Base.Just ((,) (unsafeCoerce r) a0))));
              GHC.Base.Nothing ->
               case hd_error
                      (intersect (serverGroups c)
                        (extension_NegotiatedGroups (cHextension (unsafeCoerce r)))) of {
                GHC.Base.Just _ -> Prelude.Right (Prelude.Right (Prelude.Left ((,)
                 () c)));
                GHC.Base.Nothing -> Prelude.Right (Prelude.Right (Prelude.Right
                 GHC.Base.Nothing))}};
            GHC.Base.Nothing -> Prelude.Right (Prelude.Right (Prelude.Right
             GHC.Base.Nothing))})
          (case extension_KeyShare (cHextension (unsafeCoerce r)) of {
            GHC.Base.Just a ->
             case findKeyShare a (serverGroups c) of {
              GHC.Base.Just _ -> GHC.Base.Nothing;
              GHC.Base.Nothing ->
               case hd_error
                      (intersect (serverGroups c)
                        (extension_NegotiatedGroups (cHextension (unsafeCoerce r)))) of {
                GHC.Base.Just _ -> GHC.Base.Just (ExistT RecvClientHello
                 (unsafeCoerce c));
                GHC.Base.Nothing -> GHC.Base.Nothing}};
            GHC.Base.Nothing -> GHC.Base.Nothing})))))
      (sum_merge
        (prod_curry (\_ c ->
          lift_tls RecvClientHello (\r -> Prelude.Left ((,)
            (case extension_KeyShare (cHextension (unsafeCoerce r)) of {
              GHC.Base.Just a ->
               case findKeyShare a (serverGroups c) of {
                GHC.Base.Just a0 -> Prelude.Right (Prelude.Right (Prelude.Right
                 (GHC.Base.Just ((,) (unsafeCoerce r) a0))));
                GHC.Base.Nothing -> Prelude.Right (Prelude.Right (Prelude.Right
                 GHC.Base.Nothing))};
              GHC.Base.Nothing -> Prelude.Right (Prelude.Right (Prelude.Right
               GHC.Base.Nothing))}) GHC.Base.Nothing)))) (\o _ _ -> Prelude.Right
        o))) ctx

