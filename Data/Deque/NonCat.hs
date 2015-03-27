{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -Wall #-}

module Data.Deque.NonCat where

import Data.Type.Bool
import Data.Type.Equality

data Nat = Z | S Nat deriving (Read, Show, Eq, Ord)
data Color = Red | Yellow | Green deriving (Read, Show, Eq, Ord)
data Trend = Lo | Hi deriving (Read, Show, Eq, Ord)

type T = True
type F = False

data Buffer v w x y z q i j where
  B :: {-# UNPACK #-} !(Tag n1 n2 n3 n4 n5 n m l k j i)
    -> {-# UNPACK #-} !(If n1 q (:~:) m n)
    -> {-# UNPACK #-} !(If n2 q (:~:) l m)
    -> {-# UNPACK #-} !(If n3 q (:~:) k l)
    -> {-# UNPACK #-} !(If n4 q (:~:) j k)
    -> {-# UNPACK #-} !(If n5 q (:~:) i j)
    -> Buffer n1 n2 n3 n4 n5 q i n


pattern B0 = B Zero Refl Refl Refl Refl Refl
pattern B1 a = B One a Refl Refl Refl Refl
pattern B2 a b = B Two a b Refl Refl Refl
pattern B3 a b c = B Three a b c Refl Refl
pattern B4 a b c d = B Four a b c d Refl
pattern B5 a b c d e = B Five a b c d e

data Tag n1 n2 n3 n4 n5 n m l k j i where
  Zero :: Tag F F F F F n n n n n n
  One :: Tag T F F F F n m m m m m
  Two :: Tag T T F F F n m l l l l
  Three :: Tag T T T F F n m l k k k
  Four :: Tag T T T T F n m l k j j
  Five :: Tag T T T T T n m l k j i

instance Show (Buffer v w x y z q i j) where
  show B0{} = "B0"
  show B1{} = "B1"
  show B2{} = "B2"
  show B3{} = "B3"
  show B4{} = "B4"
  show B5{} = "B5"

data Pair q i k where
  P :: !(q j k) -> !(q i j) -> Pair q i k

data HPair q r i k where
  H :: !(q j k) -> !(r i j) -> HPair q r i k

pushB :: q j k -> Buffer v w x y F q i j -> Buffer T v w x y q i k
pushB a (B Zero _ _ _ _ _) = B1 a
pushB a (B One b _ _ _ _) = B2 a b
pushB a (B Two b c _ _ _) = B3 a b c
pushB a (B Three b c d _ _) = B4 a b c d
pushB a (B Four b c d e _) = B5 a b c d e
{-- INLINE pushB #-}

popB :: Buffer T w x y z q i j -> HPair q (Buffer w x y z F q) i j
popB (B One a _ _ _ _) = a `H` B0
popB (B Two a b _ _ _) = a `H` B1 b
popB (B Three a b c _ _) = a `H` B2 b c
popB (B Four a b c d _) = a `H` B3 b c d
popB (B Five a b c d e) = a `H` B4 b c d e
{-- INLINE popB #-}

pushB2 :: Pair q j k -> Buffer v w x F F q i j -> Buffer T T v w x q i k
pushB2 (P a b) cs = pushB a (pushB b cs)
{-- INLINE pushB2 #-}

popB2 :: Buffer T T x y z q i j -> HPair (Pair q) (Buffer x y z F F q) i j
popB2 as =
  case popB as of
    a `H` bs -> case popB bs of
      b `H` cs -> P a b `H` cs
{-- INLINE popB2 #-}

injectB :: Buffer v w x y F q j k -> q i j -> Buffer T v w x y q i k
injectB (B Zero _ _ _ _ _) a = B1 a
injectB (B One a _ _ _ _) b = B2 a b
injectB (B Two a b _ _ _) c = B3 a b c
injectB (B Three a b c _ _) d = B4 a b c d
injectB (B Four a b c d _) e = B5 a b c d e
{-- INLINE injectB #-}

ejectB :: Buffer T w x y z q i j -> HPair (Buffer w x y z F q) q i j
ejectB (B One a _ _ _ _) = B0 `H` a
ejectB (B Two a b _ _ _) = B1 a `H` b
ejectB (B Three a b c _ _) = B2 a b `H` c
ejectB (B Four a b c d _) = B3 a b c `H` d
ejectB (B Five a b c d e) = B4 a b c d `H` e
{-- INLINE ejectB #-}

injectB2 :: Buffer v w x F F q j k -> Pair q i j -> Buffer T T v w x q i k
injectB2 as (P b c) = injectB (injectB as b) c
{-- INLINE injectB2 #-}

ejectB2 :: Buffer T T x y z q i j -> HPair (Buffer x y z F F q) (Pair q) i j
ejectB2 cs = case ejectB cs of
  bs `H` c -> case ejectB bs of
    as `H` b -> as `H` P b c
{-- INLINE ejectB2 #-}

data OverUnder (v :: Bool) (w :: Bool) (x :: Bool) (y :: Bool) (z :: Bool) (q :: * -> * -> *) i j where
  Under :: Buffer v F F F F q i j -> OverUnder v w x y z q i j
  Okay :: Buffer T T x F F q i j -> OverUnder v w x y z q i j
  Over :: Buffer T T T T z q i j -> OverUnder v w x y z q i j

overUnder :: Buffer v w x y z q i j -> OverUnder v w x y z q i j
overUnder bu@(B Zero _ _ _ _ _) = Under bu
overUnder bu@(B One _ _ _ _ _) = Under bu
overUnder bu@(B Two _ _ _ _ _) = Okay bu
overUnder bu@(B Three _ _ _ _ _) = Okay bu
overUnder bu@(B Four _ _ _ _ _) = Over bu
overUnder bu@(B Five _ _ _ _ _) = Over bu
{-- INLINE overUnder #-}

data Nope i j where

data Fringe r y g q i j k l where
  RX :: !(Buffer n n n n n q k l) -> !(Buffer v w x y z q i j) -> Fringe T F F q i j k l
  XR :: !(Buffer T v w x F q k l) -> !(Buffer n n n n n q i j) -> Fringe T F F q i j k l
  YX :: !(Buffer T n n n F q k l) -> !(Buffer T x y z F q i j) -> Fringe F T F q i j k l
  GY :: !(Buffer T T x F F q k l) -> !(Buffer T n n n F q i j) -> Fringe F T F q i j k l
  GG :: !(Buffer T T x F F q k l) -> !(Buffer T T z F F q i j) -> Fringe F F T q i j k l

deriving instance Show (Fringe r y g q i j k l)

data Yellows q r i j k l where
  N :: Yellows q q i i l l
  Y :: !(Fringe F T F q i m n l) -> !(Yellows (Pair q) r m j k n) -> Yellows q r i j k l
  Y1 :: !(Buffer T n n n F q i j) -> Yellows q Nope i j j j

deriving instance Show (Yellows q r i j k l)

data Level r y g q i j where
  LEmpty :: Level F F c q i i
  TinyH :: !(Buffer T T T T r q i j) -> Level r (Not r) F q i j
  TinyL :: !(Buffer r y g F F q i j) -> Level F F T q i j
  BigG :: !(Fringe F F T q i j m n) -> !(Yellows (Pair q) r j k l m) -> !(Level c1 F c2 r k l) -> Level F F T q i n
  BigY :: !(Fringe F T F q i j m n) -> !(Yellows (Pair q) r j k l m) -> !(Level c1 F c2 r k l) -> Level c1 T c2 q i n
  BigR :: !(Fringe T F F q i j m n) -> !(Yellows (Pair q) r j k l m) -> !(Level F F c r k l) -> Level T F F q i n

deriving instance Show (Level r y g q i j)

data Deque q i j where
  Deque :: !(Level F y g q i j) -> Deque q i j

deriving instance Show (Deque q i j)

toFringe :: (r ~ (Not v || z || Not a || e), ye ~ (Not r && (Not w || y || Not b || d)), g ~ (Not r && Not ye)) => Buffer v w x y z q k l -> Buffer a b c d e q i j -> Fringe r ye g q i j k l
toFringe a@(B Zero _ _ _ _ _) b@(B Zero _ _ _ _ _) = RX a b
toFringe a@(B Zero _ _ _ _ _) b@(B One _ _ _ _ _) = RX a b
toFringe a@(B Zero _ _ _ _ _) b@(B Two _ _ _ _ _) = RX a b
toFringe a@(B Zero _ _ _ _ _) b@(B Three _ _ _ _ _) = RX a b
toFringe a@(B Zero _ _ _ _ _) b@(B Four _ _ _ _ _) = RX a b
toFringe a@(B Zero _ _ _ _ _) b@(B Five _ _ _ _ _) = RX a b
toFringe a@(B Five _ _ _ _ _) b@(B Zero _ _ _ _ _) = RX a b
toFringe a@(B Five _ _ _ _ _) b@(B One _ _ _ _ _) = RX a b
toFringe a@(B Five _ _ _ _ _) b@(B Two _ _ _ _ _) = RX a b
toFringe a@(B Five _ _ _ _ _) b@(B Three _ _ _ _ _) = RX a b
toFringe a@(B Five _ _ _ _ _) b@(B Four _ _ _ _ _) = RX a b
toFringe a@(B Five _ _ _ _ _) b@(B Five _ _ _ _ _) = RX a b
toFringe a@(B One _ _ _ _ _) b@(B Zero _ _ _ _ _) = XR a b
toFringe a@(B Two _ _ _ _ _) b@(B Zero _ _ _ _ _) = XR a b
toFringe a@(B Three _ _ _ _ _) b@(B Zero _ _ _ _ _) = XR a b
toFringe a@(B Four _ _ _ _ _) b@(B Zero _ _ _ _ _) = XR a b
toFringe a@(B One _ _ _ _ _) b@(B Five _ _ _ _ _) = XR a b
toFringe a@(B Two _ _ _ _ _) b@(B Five _ _ _ _ _) = XR a b
toFringe a@(B Three _ _ _ _ _) b@(B Five _ _ _ _ _) = XR a b
toFringe a@(B Four _ _ _ _ _) b@(B Five _ _ _ _ _) = XR a b
toFringe a@(B One _ _ _ _ _) b@(B One _ _ _ _ _) = YX a b
toFringe a@(B One _ _ _ _ _) b@(B Two _ _ _ _ _) = YX a b
toFringe a@(B One _ _ _ _ _) b@(B Three _ _ _ _ _) = YX a b
toFringe a@(B One _ _ _ _ _) b@(B Four _ _ _ _ _) = YX a b
toFringe a@(B Four _ _ _ _ _) b@(B One _ _ _ _ _) = YX a b
toFringe a@(B Four _ _ _ _ _) b@(B Two _ _ _ _ _) = YX a b
toFringe a@(B Four _ _ _ _ _) b@(B Three _ _ _ _ _) = YX a b
toFringe a@(B Four _ _ _ _ _) b@(B Four _ _ _ _ _) = YX a b
toFringe a@(B Two  _ _ _ _ _) b@(B One _ _ _ _ _) = GY a b
toFringe a@(B Two _ _ _ _ _) b@(B Four _ _ _ _ _) = GY a b
toFringe a@(B Three _ _ _ _ _) b@(B One _ _ _ _ _) = GY a b
toFringe a@(B Three _ _ _ _ _) b@(B Four _ _ _ _ _) = GY a b
toFringe a@(B Two _ _ _ _ _) b@(B Two _ _ _ _ _) = GG a b
toFringe a@(B Two _ _ _ _ _) b@(B Three _ _ _ _ _) = GG a b
toFringe a@(B Three _ _ _ _ _) b@(B Two _ _ _ _ _) = GG a b
toFringe a@(B Three _ _ _ _ _) b@(B Three _ _ _ _ _) = GG a b
{-- INLINE toFringe #-}

combine :: ((r && r') ~ F) => Fringe r y g q i j m n -> Level r' y' g' (Pair q) j m -> Level (r || (y && r')) y (g || (y && g')) q i n
combine f@(RX _ _) LEmpty = BigR f N LEmpty
combine f@(XR _ _) LEmpty = BigR f N LEmpty
combine f@(YX _ _) LEmpty = BigY f N LEmpty
combine f@(GY _ _) LEmpty = BigY f N LEmpty
combine f@(GG _ _) LEmpty = BigG f N LEmpty
combine f@(RX _ _) (BigY y ys ls) = BigR f (Y y ys) ls
combine f@(XR _ _) (BigY y ys ls) = BigR f (Y y ys) ls
combine f@(YX _ _) (BigY y ys ls) = BigY f (Y y ys) ls
combine f@(GY _ _) (BigY y ys ls) = BigY f (Y y ys) ls
combine f@(GG _ _) (BigY y ys ls) = BigG f (Y y ys) ls
combine f@(RX _ _) ls@(BigG _ _ _) = BigR f N ls
combine f@(XR _ _) ls@(BigG _ _ _) = BigR f N ls
combine f@(YX _ _) ls@(BigG _ _ _) = BigY f N ls
combine f@(GY _ _) ls@(BigG _ _ _) = BigY f N ls
combine f@(GG _ _) ls@(BigG _ _ _) = BigG f N ls
combine f@(YX _ _) ls@(BigR _ _ _) = BigY f N ls
combine f@(GY _ _) ls@(BigR _ _ _) = BigY f N ls
combine f@(GG _ _) ls@(BigR _ _ _) = BigG f N ls
combine f@(RX _ _) (TinyH b@B4{}) = BigR f (Y1 b) LEmpty
combine f@(RX _ _) g@TinyL{} = BigR f N g
combine f@(XR _ _) (TinyH b@B4{}) = BigR f (Y1 b) LEmpty
combine f@(XR _ _) g@TinyL{} = BigR f N g
combine f@(YX _ _) ls@(TinyH B5{}) = BigY f N ls
combine f@(YX _ _) ls@TinyL{} = BigY f N ls
combine f@(YX _ _) (TinyH b@B4{}) = BigY f (Y1 b) LEmpty
combine f@(GY _ _) ls@(TinyH B5{}) = BigY f N ls
combine f@(GY _ _) ls@TinyL{} = BigY f N ls
combine f@(GY _ _) (TinyH b@B4{}) = BigY f (Y1 b) LEmpty
combine f@(GG _ _) ls@(TinyH B5{}) = BigG f N ls
combine f@(GG _ _) ls@TinyL{} = BigG f N ls
combine f@(GG _ _) (TinyH b@B4{}) = BigG f (Y1 b) LEmpty
{-- INLINE combine #-}

combineGG :: Fringe F F T q i j m n -> Level r' y' g' (Pair q) j m -> Level F F T q i n
combineGG f LEmpty = BigG f N LEmpty
combineGG f (BigY y ys ls) = BigG f (Y y ys) ls
combineGG f ls@(BigG _ _ _) = BigG f N ls
combineGG f ls@(BigR _ _ _) = BigG f N ls
combineGG f ls@(TinyH B5{}) = BigG f N ls
combineGG f ls@TinyL{} = BigG f N ls
combineGG f (TinyH b@B4{}) = BigG f (Y1 b) LEmpty
{-- INLINE combineGG #-}

data LCons r y g q i n where
  LR :: !(Fringe r y g q i j m n) -> !(Level T y' g' (Pair q) j m) -> LCons r y g q i n
  LGY :: !(Fringe r y g q i j m n) -> !(Level F y' g' (Pair q) j m) -> LCons r y g q i n
  LLEmpty :: LCons r y g q i n

toTiny :: Buffer a b c d e q i j -> Level e (d && Not e) (Not d && Not e) q i j
toTiny b@(B Zero _ _ _ _ _) = TinyL b
toTiny b@(B One _ _ _ _ _) = TinyL b
toTiny b@(B Two _ _ _ _ _) = TinyL b
toTiny b@(B Three _ _ _ _ _) = TinyL b
toTiny b@(B Four _ _ _ _ _) = TinyH b
toTiny b@(B Five _ _ _ _ _) = TinyH b
{-- INLINE toTiny #-}

popL :: Level r y g q i j -> LCons (r && Not y) y (g && Not y) q i j
popL LEmpty = LLEmpty
popL (TinyH _) = LLEmpty
popL (TinyL _) = LLEmpty
popL (BigG f N ls@LEmpty) = LGY f ls
popL (BigG f N ls@(TinyH B5{})) = LR f ls
popL (BigG f N ls@(TinyL{})) = LGY f ls
popL (BigG f N ls@(BigR _ _ _)) = LR f ls
popL (BigG f N ls@(BigG _ _ _)) = LGY f ls
popL (BigG f (Y1 b) LEmpty) = LGY f (toTiny b)
popL (BigG f (Y y ys) ls@LEmpty) = LGY f (BigY y ys ls)
popL (BigG f (Y y ys) ls@(TinyH B5{})) = LR f (BigY y ys ls)
popL (BigG f (Y y ys) ls@(TinyL{})) = LGY f (BigY y ys ls)
popL (BigG f (Y y ys) ls@(BigR _ _ _)) = LR f (BigY y ys ls)
popL (BigG f (Y y ys) ls@(BigG _ _ _)) = LGY f (BigY y ys ls)
popL (BigY f N ls@LEmpty) = LGY f ls
popL (BigY f N ls@(TinyH B5{})) = LR f ls
popL (BigY f N ls@(TinyL{})) = LGY f ls
popL (BigY f N ls@(BigR _ _ _)) = LR f ls
popL (BigY f N ls@(BigG _ _ _)) = LGY f ls
popL (BigY f (Y1 b) LEmpty) = LGY f (toTiny b)
popL (BigY f (Y y ys) ls@LEmpty) = LGY f (BigY y ys ls)
popL (BigY f (Y y ys) ls@(TinyH B5{})) = LR f (BigY y ys ls)
popL (BigY f (Y y ys) ls@(TinyL{})) = LGY f (BigY y ys ls)
popL (BigY f (Y y ys) ls@(BigR _ _ _)) = LR f (BigY y ys ls)
popL (BigY f (Y y ys) ls@(BigG _ _ _)) = LGY f (BigY y ys ls)
popL (BigR f N ls@LEmpty) = LGY f ls
popL (BigR f N ls@(TinyL{})) = LGY f ls
popL (BigR f N ls@(BigG _ _ _)) = LGY f ls
popL (BigR f (Y1 b) LEmpty) = LGY f (toTiny b)
popL (BigR f (Y y ys) ls@LEmpty) = LGY f (BigY y ys ls)
popL (BigR f (Y y ys) ls@(TinyL{})) = LGY f (BigY y ys ls)
popL (BigR f (Y y ys) ls@(BigG _ _ _)) = LGY f (BigY y ys ls)
{-- INLINE popL #-}

moveUpL :: Buffer v w x F F q j k -> Buffer T b c d e (Pair q) i j -> HPair (Buffer T T v w x q) (Buffer b c d e F (Pair q)) i k
moveUpL b1 b2 = case popB b2 of H p b2' -> injectB2 b1 p `H` b2'
{-- INLINE moveUpL #-}

moveDownL :: Buffer T T x y z q j k -> Buffer a b c d F (Pair q) i j -> HPair (Buffer x y z F F q) (Buffer T a b c d (Pair q)) i k
moveDownL b1 b2 = case ejectB2 b1 of H b1' p -> b1' `H` pushB p b2
{-- INLINE moveDownL #-}

moveDownR :: Buffer v w x y F (Pair q) j k -> Buffer T T c d e q i j -> HPair (Buffer T v w x y (Pair q)) (Buffer c d e F F q) i k
moveDownR b1 b2 = case popB2 b2 of H p b2' -> injectB b1 p `H` b2'
{-- INLINE moveDownR #-}

moveUpR :: Buffer T w x y z (Pair q) j k -> Buffer a b c F F q i j -> HPair (Buffer w x y z F (Pair q)) (Buffer T T a b c q) i k
moveUpR b1 b2 = case ejectB b1 of H b1' p -> b1' `H` pushB2 p b2
{-- INLINE moveUpR #-}

fixup :: Yellows q r i j k l -> Level T F F r j k -> Deque q i l
fixup y z = implant y (fixup' z)
{-- INLINE fixup #-}

fixup' :: Level T F F q i j -> Level F F T q i j
fixup' (popL -> LGY f1 (popL -> LGY f2 ls)) = case (f1, f2) of
  (RX b1 b2, YX b3 b4) -> case b1 of
    (B Zero _ _ _ _ _) -> case overUnder b2 of
      Under b2' -> let l = moveUpL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveUpL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveUpL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    (B Five _ _ _ _ _) -> case overUnder b2 of
      Under b2' -> let l = moveDownL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveDownL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveDownL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
  (RX b1 b2, GY b3 b4) -> case b1 of
    (B Zero _ _ _ _ _) -> case overUnder b2 of
      Under b2' -> let l = moveUpL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveUpL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveUpL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    (B Five _ _ _ _ _) -> case overUnder b2 of
      Under b2' -> let l = moveDownL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveDownL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveDownL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
  (RX b1 b2, GG b3 b4) -> case b1 of
    (B Zero _ _ _ _ _) -> case overUnder b2 of
      Under b2' -> let l = moveUpL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveUpL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveUpL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    (B Five _ _ _ _ _) -> case overUnder b2 of
      Under b2' -> let l = moveDownL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveDownL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveDownL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
  (XR b1 b2, YX b3 b4) -> case overUnder b1 of
    Under b1' -> case b2 of
      (B Zero _ _ _ _ _) -> let l = moveUpL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      (B Five _ _ _ _ _) -> let l = moveUpL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    Okay b1' -> case b2 of
      (B Zero _ _ _ _ _) -> let r = moveUpR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
      (B Five _ _ _ _ _) -> let r = moveDownR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
    Over b1' -> case b2 of
      (B Zero _ _ _ _ _) -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      (B Five _ _ _ _ _) -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
  (XR b1 b2, GY b3 b4) -> case overUnder b1 of
    Under b1' -> case b2 of
      (B Zero _ _ _ _ _) -> let l = moveUpL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      (B Five _ _ _ _ _) -> let l = moveUpL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    Okay b1' -> case b2 of
      (B Zero _ _ _ _ _) -> let r = moveUpR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
      (B Five _ _ _ _ _) -> let r = moveDownR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
    Over b1' -> case b2 of
      (B Zero _ _ _ _ _) -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      (B Five _ _ _ _ _) -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
  (XR b1 b2, GG b3 b4) -> case overUnder b1 of
    Under b1' -> case b2 of
      (B Zero _ _ _ _ _) -> let l = moveUpL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      (B Five _ _ _ _ _) -> let l = moveUpL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    Okay b1' -> case b2 of
      (B Zero _ _ _ _ _) -> let r = moveUpR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
      (B Five _ _ _ _ _) -> let r = moveDownR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
    Over b1' -> case b2 of
      (B Zero _ _ _ _ _) -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      (B Five _ _ _ _ _) -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
fixup' (popL -> LGY f1 (popL -> LR f2 ls)) = case (f1, f2) of
  (RX b1 b2, GG b3 b4) -> case b1 of
    (B Zero _ _ _ _ _) -> case overUnder b2 of
      Under b2' -> let l = moveUpL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveUpL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveUpL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    (B Five _ _ _ _ _) -> case overUnder b2 of
      Under b2' -> let l = moveDownL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveDownL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveDownL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
  (XR b1 b2, GG b3 b4) -> case overUnder b1 of
    Under b1' -> case b2 of
      (B Zero _ _ _ _ _) -> let l = moveUpL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      (B Five _ _ _ _ _) -> let l = moveUpL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    Okay b1' -> case b2 of
      (B Zero _ _ _ _ _) -> let r = moveUpR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
      (B Five _ _ _ _ _) -> let r = moveDownR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
    Over b1' -> case b2 of
      (B Zero _ _ _ _ _) -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      (B Five _ _ _ _ _) -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
fixup' a = fixup2' a
{-- INLINE fixup' #-}

fixup2' :: Level T F F q i j -> Level F F T q i j
fixup2' (TinyH (B5 a b c d e))                                                                     = go5 a b c d e
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Zero _ _ _ _ _))                       N LEmpty)                                         = LEmpty
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B One n _ _ _ _))                     N LEmpty)                                         = go1 n
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Two n o _ _ _))                   N LEmpty)                                         = go2 n o
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Three n o p _ _))                 N LEmpty)                                         = go3 n o p
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Four n o p q _))               N LEmpty)                                         = go4 n o p q
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Five n o p q r))             N LEmpty)                                         = go5 n o p q r
fixup2' (BigR (RX (B Five a b c d e) (B Zero _ _ _ _ _))           N LEmpty)                                         = go5 a b c d e
fixup2' (BigR (RX (B Five a b c d e) (B One n _ _ _ _))         N LEmpty)                                         = go6 a b c d e n
fixup2' (BigR (RX (B Five a b c d e) (B Two n o _ _ _))       N LEmpty)                                         = go7 a b c d e n o
fixup2' (BigR (RX (B Five a b c d e) (B Three n o p _ _))     N LEmpty)                                         = go8 a b c d e n o p
fixup2' (BigR (RX (B Five a b c d e) (B Four n o p q _))   N LEmpty)                                         = go9 a b c d e n o p q
fixup2' (BigR (RX (B Five a b c d e) (B Five n o p q r)) N LEmpty)                                         = go10 a b c d e n o p q r
fixup2' (BigR (XR (B One a _ _ _ _) (B Zero _ _ _ _ _))                   N LEmpty)                                         = go1 a
fixup2' (BigR (XR (B One a _ _ _ _) (B Five n o p q r))         N LEmpty)                                         = go6 a n o p q r
fixup2' (BigR (XR (B Two a b _ _ _) (B Zero _ _ _ _ _))                 N LEmpty)                                         = go2 a b
fixup2' (BigR (XR (B Two a b _ _ _) (B Five n o p q r))       N LEmpty)                                         = go7 a b n o p q r
fixup2' (BigR (XR (B Three a b c _ _) (B Zero _ _ _ _ _))               N LEmpty)                                         = go3 a b c
fixup2' (BigR (XR (B Three a b c _ _) (B Five n o p q r))     N LEmpty)                                         = go8 a b c n o p q r
fixup2' (BigR (XR (B Four a b c d _) (B Zero _ _ _ _ _))             N LEmpty)                                         = go4 a b c d
fixup2' (BigR (XR (B Four a b c d _) (B Five n o p q r))   N LEmpty)                                         = go9 a b c d n o p q r
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Zero _ _ _ _ _))                       (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go2 s t
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B One n _ _ _ _))                     (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go3 s t n
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Two n o _ _ _))                   (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go4 s t n o
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Three n o p _ _))                 (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go5 s t n o p
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Four n o p q _))               (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go6 s t n o p q
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Five n o p q r))             (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go7 s t n o p q r
fixup2' (BigR (RX (B Five a b c d e) (B Zero _ _ _ _ _))           (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go7 a b c d e s t
fixup2' (BigR (RX (B Five a b c d e) (B One n _ _ _ _))         (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go8 a b c d e s t n
fixup2' (BigR (RX (B Five a b c d e) (B Two n o _ _ _))       (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go9 a b c d e s t n o
fixup2' (BigR (RX (B Five a b c d e) (B Three n o p _ _))     (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go10 a b c d e s t n o p
fixup2' (BigR (RX (B Five a b c d e) (B Four n o p q _))   (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go11 a b c d e s t n o p q
fixup2' (BigR (RX (B Five a b c d e) (B Five n o p q r)) (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go12 a b c d e s t n o p q r
fixup2' (BigR (XR (B One a _ _ _ _) (B Zero _ _ _ _ _))                   (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go3 a s t
fixup2' (BigR (XR (B One a _ _ _ _) (B Five n o p q r))         (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go8 a s t n o p q r
fixup2' (BigR (XR (B Two a b _ _ _) (B Zero _ _ _ _ _))                 (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go4 a b s t
fixup2' (BigR (XR (B Two a b _ _ _) (B Five n o p q r))       (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go9 a b s t n o p q r
fixup2' (BigR (XR (B Three a b c _ _) (B Zero _ _ _ _ _))               (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go5 a b c s t
fixup2' (BigR (XR (B Three a b c _ _) (B Five n o p q r))     (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go10 a b c s t n o p q r
fixup2' (BigR (XR (B Four a b c d _) (B Zero _ _ _ _ _))             (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go6 a b c d s t
fixup2' (BigR (XR (B Four a b c d _) (B Five n o p q r))   (Y1 (B One (P s t) _ _ _ _)) LEmpty)                         = go11 a b c d s t n o p q r
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Zero _ _ _ _ _))                       (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go8 s t u v w x y z
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B One n _ _ _ _))                     (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go9 s t u v w x y z n
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Two n o _ _ _))                   (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go10 s t u v w x y z n o
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Three n o p _ _))                 (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go11 s t u v w x y z n o p
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Four n o p q _))               (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go12 s t u v w x y z n o p q
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Five n o p q r))             (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go13 s t u v w x y z n o p q r
fixup2' (BigR (RX (B Five a b c d e) (B Zero _ _ _ _ _))           (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go13 a b c d e s t u v w x y z
fixup2' (BigR (RX (B Five a b c d e) (B One n _ _ _ _))         (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go14 a b c d e s t u v w x y z n
fixup2' (BigR (RX (B Five a b c d e) (B Two n o _ _ _))       (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go15 a b c d e s t u v w x y z n o
fixup2' (BigR (RX (B Five a b c d e) (B Three n o p _ _))     (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go16 a b c d e s t u v w x y z n o p
fixup2' (BigR (RX (B Five a b c d e) (B Four n o p q _))   (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go17 a b c d e s t u v w x y z n o p q
fixup2' (BigR (RX (B Five a b c d e) (B Five n o p q r)) (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go18 a b c d e s t u v w x y z n o p q r
fixup2' (BigR (XR (B One a _ _ _ _) (B Zero _ _ _ _ _))                   (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go9 a s t u v w x y z
fixup2' (BigR (XR (B One a _ _ _ _) (B Five n o p q r))         (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go14 a s t u v w x y z n o p q r
fixup2' (BigR (XR (B Two a b _ _ _) (B Zero _ _ _ _ _))                 (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go10 a b s t u v w x y z
fixup2' (BigR (XR (B Two a b _ _ _) (B Five n o p q r))       (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go15 a b s t u v w x y z n o p q r
fixup2' (BigR (XR (B Three a b c _ _) (B Zero _ _ _ _ _))               (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go11 a b c s t u v w x y z
fixup2' (BigR (XR (B Three a b c _ _) (B Five n o p q r))     (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go16 a b c s t u v w x y z n o p q r
fixup2' (BigR (XR (B Four a b c d _) (B Zero _ _ _ _ _))             (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go12 a b c d s t u v w x y z
fixup2' (BigR (XR (B Four a b c d _) (B Five n o p q r))   (Y1 (B Four (P s t) (P u v) (P w x) (P y z) _)) LEmpty) = go17 a b c d s t u v w x y z n o p q r
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Zero _ _ _ _ _))                       N (TinyL (B Zero _ _ _ _ _)))                           = LEmpty
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B One n _ _ _ _))                     N (TinyL (B Zero _ _ _ _ _)))                           = go1 n
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Two n o _ _ _))                   N (TinyL (B Zero _ _ _ _ _)))                           = go2 n o
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Three n o p _ _))                 N (TinyL (B Zero _ _ _ _ _)))                           = go3 n o p
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Four n o p q _))               N (TinyL (B Zero _ _ _ _ _)))                           = go4 n o p q
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Five n o p q r))             N (TinyL (B Zero _ _ _ _ _)))                           = go5 n o p q r
fixup2' (BigR (RX (B Five a b c d e) (B Zero _ _ _ _ _))           N (TinyL (B Zero _ _ _ _ _)))                           = go5 a b c d e
fixup2' (BigR (RX (B Five a b c d e) (B One n _ _ _ _))         N (TinyL (B Zero _ _ _ _ _)))                           = go6 a b c d e n
fixup2' (BigR (RX (B Five a b c d e) (B Two n o _ _ _))       N (TinyL (B Zero _ _ _ _ _)))                           = go7 a b c d e n o
fixup2' (BigR (RX (B Five a b c d e) (B Three n o p _ _))     N (TinyL (B Zero _ _ _ _ _)))                           = go8 a b c d e n o p
fixup2' (BigR (RX (B Five a b c d e) (B Four n o p q _))   N (TinyL (B Zero _ _ _ _ _)))                           = go9 a b c d e n o p q
fixup2' (BigR (RX (B Five a b c d e) (B Five n o p q r)) N (TinyL (B Zero _ _ _ _ _)))                           = go10 a b c d e n o p q r
fixup2' (BigR (XR (B One a _ _ _ _) (B Zero _ _ _ _ _))                   N (TinyL (B Zero _ _ _ _ _)))                           = go1 a
fixup2' (BigR (XR (B One a _ _ _ _) (B Five n o p q r))         N (TinyL (B Zero _ _ _ _ _)))                           = go6 a n o p q r
fixup2' (BigR (XR (B Two a b _ _ _) (B Zero _ _ _ _ _))                 N (TinyL (B Zero _ _ _ _ _)))                           = go2 a b
fixup2' (BigR (XR (B Two a b _ _ _) (B Five n o p q r))       N (TinyL (B Zero _ _ _ _ _)))                           = go7 a b n o p q r
fixup2' (BigR (XR (B Three a b c _ _) (B Zero _ _ _ _ _))               N (TinyL (B Zero _ _ _ _ _)))                           = go3 a b c
fixup2' (BigR (XR (B Three a b c _ _) (B Five n o p q r))     N (TinyL (B Zero _ _ _ _ _)))                           = go8 a b c n o p q r
fixup2' (BigR (XR (B Four a b c d _) (B Zero _ _ _ _ _))             N (TinyL (B Zero _ _ _ _ _)))                           = go4 a b c d
fixup2' (BigR (XR (B Four a b c d _) (B Five n o p q r))   N (TinyL (B Zero _ _ _ _ _)))                           = go9 a b c d n o p q r
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Zero _ _ _ _ _))                       N (TinyL (B One (P s t) _ _ _ _)))                           = go2 s t
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B One n _ _ _ _))                     N (TinyL (B One (P s t) _ _ _ _)))                           = go3 s t n
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Two n o _ _ _))                   N (TinyL (B One (P s t) _ _ _ _)))                           = go4 s t n o
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Three n o p _ _))                 N (TinyL (B One (P s t) _ _ _ _)))                           = go5 s t n o p
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Four n o p q _))               N (TinyL (B One (P s t) _ _ _ _)))                           = go6 s t n o p q
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Five n o p q r))             N (TinyL (B One (P s t) _ _ _ _)))                           = go7 s t n o p q r
fixup2' (BigR (RX (B Five a b c d e) (B Zero _ _ _ _ _))           N (TinyL (B One (P s t) _ _ _ _)))                           = go7 a b c d e s t
fixup2' (BigR (RX (B Five a b c d e) (B One n _ _ _ _))         N (TinyL (B One (P s t) _ _ _ _)))                           = go8 a b c d e s t n
fixup2' (BigR (RX (B Five a b c d e) (B Two n o _ _ _))       N (TinyL (B One (P s t) _ _ _ _)))                           = go9 a b c d e s t n o
fixup2' (BigR (RX (B Five a b c d e) (B Three n o p _ _))     N (TinyL (B One (P s t) _ _ _ _)))                           = go10 a b c d e s t n o p
fixup2' (BigR (RX (B Five a b c d e) (B Four n o p q _))   N (TinyL (B One (P s t) _ _ _ _)))                           = go11 a b c d e s t n o p q
fixup2' (BigR (RX (B Five a b c d e) (B Five n o p q r)) N (TinyL (B One (P s t) _ _ _ _)))                           = go12 a b c d e s t n o p q r
fixup2' (BigR (XR (B One a _ _ _ _) (B Zero _ _ _ _ _))                   N (TinyL (B One (P s t) _ _ _ _)))                           = go3 a s t
fixup2' (BigR (XR (B One a _ _ _ _) (B Five n o p q r))         N (TinyL (B One (P s t) _ _ _ _)))                           = go8 a s t n o p q r
fixup2' (BigR (XR (B Two a b _ _ _) (B Zero _ _ _ _ _))                 N (TinyL (B One (P s t) _ _ _ _)))                           = go4 a b s t
fixup2' (BigR (XR (B Two a b _ _ _) (B Five n o p q r))       N (TinyL (B One (P s t) _ _ _ _)))                           = go9 a b s t n o p q r
fixup2' (BigR (XR (B Three a b c _ _) (B Zero _ _ _ _ _))               N (TinyL (B One (P s t) _ _ _ _)))                           = go5 a b c s t
fixup2' (BigR (XR (B Three a b c _ _) (B Five n o p q r))     N (TinyL (B One (P s t) _ _ _ _)))                           = go10 a b c s t n o p q r
fixup2' (BigR (XR (B Four a b c d _) (B Zero _ _ _ _ _))             N (TinyL (B One (P s t) _ _ _ _)))                           = go6 a b c d s t
fixup2' (BigR (XR (B Four a b c d _) (B Five n o p q r))   N (TinyL (B One (P s t) _ _ _ _)))                           = go11 a b c d s t n o p q r
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Zero _ _ _ _ _))                       N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go4 s t u v
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B One n _ _ _ _))                     N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go5 s t u v n
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Two n o _ _ _))                   N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go6 s t u v n o
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Three n o p _ _))                 N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go7 s t u v n o p
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Four n o p q _))               N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go8 s t u v n o p q
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Five n o p q r))             N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go9 s t u v n o p q r
fixup2' (BigR (RX (B Five a b c d e) (B Zero _ _ _ _ _))           N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go9 a b c d e s t u v
fixup2' (BigR (RX (B Five a b c d e) (B One n _ _ _ _))         N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go10 a b c d e s t u v n
fixup2' (BigR (RX (B Five a b c d e) (B Two n o _ _ _))       N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go11 a b c d e s t u v n o
fixup2' (BigR (RX (B Five a b c d e) (B Three n o p _ _))     N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go12 a b c d e s t u v n o p
fixup2' (BigR (RX (B Five a b c d e) (B Four n o p q _))   N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go13 a b c d e s t u v n o p q
fixup2' (BigR (RX (B Five a b c d e) (B Five n o p q r)) N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go14 a b c d e s t u v n o p q r
fixup2' (BigR (XR (B One a _ _ _ _) (B Zero _ _ _ _ _))                   N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go5 a s t u v
fixup2' (BigR (XR (B One a _ _ _ _) (B Five n o p q r))         N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go10 a s t u v n o p q r
fixup2' (BigR (XR (B Two a b _ _ _) (B Zero _ _ _ _ _))                 N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go6 a b s t u v
fixup2' (BigR (XR (B Two a b _ _ _) (B Five n o p q r))       N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go11 a b s t u v n o p q r
fixup2' (BigR (XR (B Three a b c _ _) (B Zero _ _ _ _ _))               N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go7 a b c s t u v
fixup2' (BigR (XR (B Three a b c _ _) (B Five n o p q r))     N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go12 a b c s t u v n o p q r
fixup2' (BigR (XR (B Four a b c d _) (B Zero _ _ _ _ _))             N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go8 a b c d s t u v
fixup2' (BigR (XR (B Four a b c d _) (B Five n o p q r))   N (TinyL (B Two (P s t) (P u v) _ _ _)))                   = go13 a b c d s t u v n o p q r
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Zero _ _ _ _ _))                       N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go6 s t u v w x
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B One n _ _ _ _))                     N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go7 s t u v w x n
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Two n o _ _ _))                   N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go8 s t u v w x n o
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Three n o p _ _))                 N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go9 s t u v w x n o p
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Four n o p q _))               N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go10 s t u v w x n o p q
fixup2' (BigR (RX (B Zero _ _ _ _ _) (B Five n o p q r))             N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go11 s t u v w x n o p q r
fixup2' (BigR (RX (B Five a b c d e) (B Zero _ _ _ _ _))           N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go11 a b c d e s t u v w x
fixup2' (BigR (RX (B Five a b c d e) (B One n _ _ _ _))         N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go12 a b c d e s t u v w x n
fixup2' (BigR (RX (B Five a b c d e) (B Two n o _ _ _))       N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go13 a b c d e s t u v w x n o
fixup2' (BigR (RX (B Five a b c d e) (B Three n o p _ _))     N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go14 a b c d e s t u v w x n o p
fixup2' (BigR (RX (B Five a b c d e) (B Four n o p q _))   N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go15 a b c d e s t u v w x n o p q
fixup2' (BigR (RX (B Five a b c d e) (B Five n o p q r)) N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go16 a b c d e s t u v w x n o p q r
fixup2' (BigR (XR (B One a _ _ _ _) (B Zero _ _ _ _ _))                   N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go7 a s t u v w x
fixup2' (BigR (XR (B One a _ _ _ _) (B Five n o p q r))         N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go12 a s t u v w x n o p q r
fixup2' (BigR (XR (B Two a b _ _ _) (B Zero _ _ _ _ _))                 N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go8 a b s t u v w x
fixup2' (BigR (XR (B Two a b _ _ _) (B Five n o p q r))       N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go13 a b s t u v w x n o p q r
fixup2' (BigR (XR (B Three a b c _ _) (B Zero _ _ _ _ _))               N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go9 a b c s t u v w x
fixup2' (BigR (XR (B Three a b c _ _) (B Five n o p q r))     N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go14 a b c s t u v w x n o p q r
fixup2' (BigR (XR (B Four a b c d _) (B Zero _ _ _ _ _))             N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go10 a b c d s t u v w x
fixup2' (BigR (XR (B Four a b c d _) (B Five n o p q r))   N (TinyL (B Three (P s t) (P u v) (P w x) _ _)))           = go15 a b c d s t u v w x n o p q r
{-# NOINLINE fixup2' #-}

go1 :: q a b -> Level F F T q a b
go1 a = TinyL (B1 a)
go2 :: q b c -> q a b -> Level F F T q a c
go2 a b                                              = TinyL (B2 a b)
go3 :: q c d -> q b c -> q a b -> Level F F T q a d
go3 a b c                                            = TinyL (B3 a b c)
go4 :: q d e -> q c d -> q b c -> q a b -> Level F F T q a e
go4 a b c d                                          = BigG (GG (B2 a b) (B2 c d)) N LEmpty
go5 :: q e f -> q d e -> q c d -> q b c -> q a b -> Level F F T q a f
go5 a b c d e                                        = BigG (GG (B2 a b) (B3 c d e)) N LEmpty
go6 :: q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level F F T q a g
go6 a b c d e f                                      = BigG (GG (B3 a b c) (B3 d e f)) N LEmpty
go7 :: q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level F F T q a h
go7 a b c d e f g                                    = BigG (GG (B3 a b c) (B2 f g)) (Y1 (B1 (P d e))) LEmpty
go8 :: q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level F F T q a i
go8 a b c d e f g h                                  = BigG (GG (B3 a b c) (B3 f g h)) (Y1 (B1 (P d e))) LEmpty
go9 :: q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level F F T q a j
go9 a b c d e f g h i                                = BigG (GG (B3 a b c) (B2 h i)) (Y (YX (B1 (P d e)) (B1 (P f g))) N) LEmpty
go10 :: q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level F F T q a k
go10 a b c d e f g h i j                             = BigG (GG (B3 a b c) (B3 h i j)) (Y (YX (B1 (P d e)) (B1 (P f g))) N) LEmpty
go11 :: q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level F F T q a l
go11 a b c d e f g h i j k                           = BigG (GG (B3 a b c) (B2 j k)) (Y (YX (B1 (P d e)) (B2 (P f g) (P h i))) N) LEmpty
go12 :: q l m -> q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level F F T q a m
go12 a b c d e f g h i j k l                         = BigG (GG (B3 a b c) (B3 j k l)) (Y (YX (B1 (P d e)) (B2 (P f g) (P h i))) N) LEmpty
go13 :: q m n -> q l m -> q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level F F T q a n
go13 a b c d e f g h i j k l m                       = BigG (GG (B3 a b c) (B2 l m)) (Y (YX (B1 (P d e)) (B3 (P f g) (P h i) (P j k))) N) LEmpty
go14 :: q n o -> q m n -> q l m -> q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level F F T q a o
go14 a b c d e f g h i j k l m n                     = BigG (GG (B3 a b c) (B3 l m n)) (Y (YX (B1 (P d e)) (B3 (P f g) (P h i) (P j k))) N) LEmpty
go15 :: q o p -> q n o -> q m n -> q l m -> q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level F F T q a p
go15 a b c d e f g h i j k l m n o                   = BigG (GG (B3 a b c) (B2 n o)) (Y (YX (B1 (P d e)) (B4 (P f g) (P h i) (P j k) (P l m))) N) LEmpty
go16 :: q p r -> q o p -> q n o -> q m n -> q l m -> q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level F F T q a r
go16 a b c d e f g h i j k l m n o p                 = BigG (GG (B3 a b c) (B3 n o p)) (Y (YX (B1 (P d e)) (B4 (P f g) (P h i) (P j k) (P l m))) N) LEmpty
go17 :: q r s -> q p r -> q o p -> q n o -> q m n -> q l m -> q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level F F T q a s
go17 a b c d e f g h i j k l m n o p q               = BigG (GG (B3 a b c) (B2 p q)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B2 (P l m) (P n o))) N) LEmpty
go18 :: q s t -> q r s -> q p r -> q o p -> q n o -> q m n -> q l m -> q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level F F T q a t
go18 a b c d e f g h i j k l m n o p q r             = BigG (GG (B3 a b c) (B3 p q r)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B2 (P l m) (P n o))) N) LEmpty
{-
go19 a b c d e f g h i j k l m n o p q r s           = BigG (GG (B3 a b c) (B2 r s)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B3 (P l m) (P n o) (P p q))) N) LEmpty
go20 a b c d e f g h i j k l m n o p q r s t         = BigG (GG (B3 a b c) (B3 r s t)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B3 (P l m) (P n o) (P p q))) N) LEmpty
go21 a b c d e f g h i j k l m n o p q r s t u       = BigG (GG (B3 a b c) (B2 t u)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B4 (P l m) (P n o) (P p q) (P r s))) N) LEmpty
go22 a b c d e f g h i j k l m n o p q r s t u v     = BigG (GG (B3 a b c) (B3 t u v)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B4 (P l m) (P n o) (P p q) (P r s))) N) LEmpty
-}

implant :: Yellows q r i j k l -> Level F F T r j k -> Deque q i l
implant N LEmpty = Deque $ LEmpty
implant N (TinyL b) = Deque $ TinyL b
implant N (BigG b y z) = Deque $ BigG b y z
implant (Y1 b@B1{}) _ = Deque $ TinyL b -- in agda we could properly eliminate the impossible cases here :( however the thristing ensures we can't throw anything away.
implant (Y1 b@B4{}) _ = Deque $ TinyH b
implant (Y y ys) z = Deque $ BigY y ys z
{-- INLINE implant #-}

empty :: Deque q i i
empty = Deque LEmpty

infixr 5 :|
data View l r a c where
  Empty :: View l r a a
  (:|) :: l b c -> r a b -> View l r a c

class Uncons t where
  uncons :: t r a b -> View r (t r) a b

class Unsnoc t where
  unsnoc :: t r a b -> View (t r) r a b

infixr 5 <|
class Cons t where
  (<|) :: r b c -> t r a b -> t r a c

infixl 5 |>
class Snoc t where
  (|>) :: t r b c -> r a b -> t r a c

instance Cons Deque where
  a <| (Deque LEmpty)                                    = Deque $ TinyL (B1 a)
  a <| (Deque (TinyL (B Zero _ _ _ _ _)))                              = Deque $ TinyL (B1 a)
  a <| (Deque (TinyL (B One b _ _ _ _)))                            = Deque $ TinyL (B2 a b)
  a <| (Deque (TinyL (B Two b c _ _ _)))                          = Deque $ TinyL (B3 a b c)
  a <| (Deque (TinyL (B Three b c d _ _)))                        = Deque $ TinyH (B4 a b c d)
  a <| (Deque (TinyH (B Four b c d e _)))                      = fixup N (TinyH (B5 a b c d e))
  a <| (Deque (BigY (YX (B One b _ _ _ _) (B One i _ _ _ _)) y z))             = Deque $ BigY (GY (B2 a b) (B1 i)) y z
  a <| (Deque (BigY (YX (B One b _ _ _ _) (B Two i j _ _ _)) y z))           = Deque $ BigG (GG (B2 a b) (B2 i j)) y z
  a <| (Deque (BigY (YX (B One b _ _ _ _) (B Three i j k _ _)) y z))         = Deque $ BigG (GG (B2 a b) (B3 i j k)) y z
  a <| (Deque (BigY (YX (B One b _ _ _ _) (B Four i j k l _)) y z))       = Deque $ BigY (GY (B2 a b) (B4 i j k l)) y z
  a <| (Deque (BigY (GY (B Two b c _ _ _) x) y z))                = Deque $ BigY (GY (B3 a b c) x) y z
  a <| (Deque (BigG (GG (B Two b c _ _ _) x) y z))                = Deque $ BigG (GG (B3 a b c) x) y z
  a <| (Deque (BigY (GY (B Three b c d _ _) x) y z))              = Deque $ BigY (YX (B4 a b c d) x) y z
  a <| (Deque (BigG (GG (B Three b c d _ _) x) y LEmpty))         = Deque $ BigY (YX (B4 a b c d) x) y LEmpty
  a <| (Deque (BigG (GG (B Three b c d _ _) x) y z@(TinyH (B Five _ _ _ _ _)))) = Deque $ BigY (YX (B4 a b c d) x) y (fixup' z)
  a <| (Deque (BigG (GG (B Three b c d _ _) x) y z@(TinyL{})))    = Deque $ BigY (YX (B4 a b c d) x) y z
  a <| (Deque (BigG (GG (B Three b c d _ _) x) y z@(BigR{})))     = Deque $ BigY (YX (B4 a b c d) x) y (fixup' z)
  a <| (Deque (BigG (GG (B Three b c d _ _) x) y z@(BigG{})))     = Deque $ BigY (YX (B4 a b c d) x) y z
  a <| (Deque (BigY (YX (B Four b c d e _) x) y z))            = fixup N (BigR (RX (B5 a b c d e) x) y z)

instance Unsnoc Deque where
  unsnoc (Deque LEmpty)                                  = Empty
  unsnoc (Deque (TinyL (B Zero _ _ _ _ _)))                            = Empty
  unsnoc (Deque (TinyL (B One b _ _ _ _)))                          = Deque LEmpty :| b
  unsnoc (Deque (TinyL (B Two b c _ _ _)))                        = Deque (TinyL (B1 b)) :| c
  unsnoc (Deque (TinyL (B Three b c d _ _)))                      = Deque (TinyL (B2 b c)) :| d
  unsnoc (Deque (TinyH (B Four b c d e _)))                    = Deque (TinyL (B3 b c d)) :| e
  unsnoc (Deque (BigY (YX b (B One i _ _ _ _)) y z))                = fixup N (BigR (XR b (B0)) y z) :| i
  unsnoc (Deque (BigY (YX b (B Two i j _ _ _)) y z))              = Deque (BigY (YX b (B1 i)) y z) :| j
  unsnoc (Deque (BigY (YX b (B Three i j k _ _)) y z))            = Deque (BigY (YX b (B2 i j)) y z) :| k
  unsnoc (Deque (BigY (YX b (B Four i j k l _)) y z))          = Deque (BigY (YX b (B3 i j k)) y z) :| l
  unsnoc (Deque (BigY (GY b (B One i _ _ _ _)) y z))                = fixup N (BigR (XR b B0) y z) :| i
  unsnoc (Deque (BigY (GY b (B Four i j k l _)) y z))          = Deque (BigG (GG b (B3 i j k)) y z) :| l
  unsnoc (Deque (BigG (GG b (B Two i j _ _ _)) y LEmpty))         = Deque (BigY (GY b (B1 i)) y LEmpty) :| j
  unsnoc (Deque (BigG (GG b (B Two i j _ _ _)) y z@(TinyH B5{}))) = Deque (BigY (GY b (B1 i)) y (fixup' z)) :| j
  unsnoc (Deque (BigG (GG b (B Two i j _ _ _)) y z@(TinyL{})))    = Deque (BigY (GY b (B1 i)) y z) :| j
  unsnoc (Deque (BigG (GG b (B Two i j _ _ _)) y z@(BigR{})))     = Deque (BigY (GY b (B1 i)) y (fixup' z)) :| j
  unsnoc (Deque (BigG (GG b (B Two i j _ _ _)) y z@(BigG{})))     = Deque (BigY (GY b (B1 i)) y z) :| j
  unsnoc (Deque (BigG (GG b (B Three i j k _ _)) y z))            = Deque (BigG (GG b (B2 i j)) y z) :| k

instance Uncons Deque where
  uncons (Deque LEmpty)                                    = Empty
  uncons (Deque (TinyL (B Zero _ _ _ _ _)))                              = Empty
  uncons (Deque (TinyL (B One b _ _ _ _)))                            = b :| Deque LEmpty
  uncons (Deque (TinyL (B Two b c _ _ _)))                          = b :| Deque (TinyL (B1 c))
  uncons (Deque (TinyL (B Three b c d _ _)))                        = b :| Deque (TinyL (B2 c d))
  uncons (Deque (TinyH (B Four b c d e _)))                      = b :| Deque (TinyL (B3 c d e))
  uncons (Deque (BigY (YX (B One b _ _ _ _) i) y z))                  = b :| fixup N (BigR (RX B0 i) y z)
  uncons (Deque (BigY (GY (B Two b c _ _ _) (B One i _ _ _ _)) y z))           = b :| Deque (BigY (YX (B1 c) (B1 i)) y z)
  uncons (Deque (BigY (GY (B Two b c _ _ _) (B Four i j k l _)) y z))     = b :| Deque (BigY (YX (B1 c) (B4 i j k l)) y z)
  uncons (Deque (BigG (GG (B Two b c _ _ _) i) y LEmpty))           = b :| Deque (BigY (YX (B1 c) i) y LEmpty)
  uncons (Deque (BigG (GG (B Two b c _ _ _) i) y z@(TinyH (B Five _ _ _ _ _))))   = b :| Deque (BigY (YX (B1 c) i) y (fixup' z))
  uncons (Deque (BigG (GG (B Two b c _ _ _) i) y z@(TinyL{})))      = b :| Deque (BigY (YX (B1 c) i) y z)
  uncons (Deque (BigG (GG (B Two b c _ _ _) i) y z@(BigR{})))       = b :| Deque (BigY (YX (B1 c) i) y (fixup' z))
  uncons (Deque (BigG (GG (B Two b c _ _ _) i) y z@(BigG{})))       = b :| Deque (BigY (YX (B1 c) i) y z)
  uncons (Deque (BigY (GY (B Three b c d _ _) i) y z))              = b :| Deque (BigY (GY (B2 c d) i) y z)
  uncons (Deque (BigG (GG (B Three b c d _ _) i) y z))              = b :| Deque (BigG (GG (B2 c d) i) y z)
  uncons (Deque (BigY (YX (B Four b c d e _) (B One i _ _ _ _)) y z))       = b :| Deque (BigY (GY (B3 c d e) (B1 i)) y z)
  uncons (Deque (BigY (YX (B Four b c d e _) (B Two i j _ _ _)) y z))     = b :| Deque (BigG (GG (B3 c d e) (B2 i j)) y z)
  uncons (Deque (BigY (YX (B Four b c d e _) (B Three i j k _ _)) y z))   = b :| Deque (BigG (GG (B3 c d e) (B3 i j k)) y z)
  uncons (Deque (BigY (YX (B Four b c d e _) (B Four i j k l _)) y z)) = b :| Deque (BigY (GY (B3 c d e) (B4 i j k l)) y z)

instance Snoc Deque where
  (Deque LEmpty)                                    |> a = Deque $ TinyL (B1 a)
  (Deque (TinyL (B Zero _ _ _ _ _)))                              |> a = Deque $ TinyL (B1 a)
  (Deque (TinyL (B One b _ _ _ _)))                            |> a = Deque $ TinyL (B2 b a)
  (Deque (TinyL (B Two b c _ _ _)))                          |> a = Deque $ TinyL (B3 b c a)
  (Deque (TinyL (B Three b c d _ _)))                        |> a = Deque $ TinyH (B4 b c d a)
  (Deque (TinyH (B Four b c d e _)))                      |> a = fixup N (TinyH (B5 b c d e a))
  (Deque (BigY (YX b (B One i _ _ _ _)) y z))                  |> a = Deque $ BigY (YX b (B2 i a)) y z
  (Deque (BigY (YX b (B Two i j _ _ _)) y z))                |> a = Deque $ BigY (YX b (B3 i j a)) y z
  (Deque (BigY (YX b (B Three i j k _ _)) y z))              |> a = Deque $ BigY (YX b (B4 i j k a)) y z
  (Deque (BigY (YX b (B Four i j k l _)) y z))            |> a = fixup N (BigR (XR b (B5 i j k l a)) y z)
  (Deque (BigY (GY b (B One i _ _ _ _)) y z))                  |> a = Deque $ BigG (GG b (B2 i a)) y z
  (Deque (BigY (GY b (B Four i j k l _)) y z))            |> a = fixup N (BigR (XR b (B5 i j k l a)) y z)
  (Deque (BigG (GG b (B Two i j _ _ _)) y z))                |> a = Deque $ BigG (GG b (B3 i j a)) y z
  (Deque (BigG (GG b (B Three i j k _ _)) y z@LEmpty))       |> a = Deque $ BigY (GY b (B4 i j k a)) y z
  (Deque (BigG (GG b (B Three i j k _ _)) y z@(TinyH (B Five _ _ _ _ _)))) |> a = Deque $ BigY (GY b (B4 i j k a)) y (fixup' z)
  (Deque (BigG (GG b (B Three i j k _ _)) y z@TinyL{}))      |> a = Deque $ BigY (GY b (B4 i j k a)) y z
  (Deque (BigG (GG b (B Three i j k _ _)) y z@BigR{}))       |> a = Deque $ BigY (GY b (B4 i j k a)) y (fixup' z)
  (Deque (BigG (GG b (B Three i j k _ _)) y z@BigG{}))       |> a = Deque $ BigY (GY b (B4 i j k a)) y z
