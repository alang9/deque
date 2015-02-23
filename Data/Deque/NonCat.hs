{-- LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -Wall #-}
module Data.Deque.NonCat where

import Data.Type.Bool

data Nat = Z | S Nat deriving (Read, Show, Eq, Ord)
data Color = Red | Yellow | Green deriving (Read, Show, Eq, Ord)
data Trend = Lo | Hi deriving (Read, Show, Eq, Ord)

type T = True
type F = False

data Buffer u v w x y z q i j where
  B0 :: Buffer T F F F F F q i i
  B1 :: !(q i j) -> Buffer F T F F F F q i j
  B2 :: !(q j k) -> !(q i j) -> Buffer F F T F F F q i k
  B3 :: !(q k l) -> !(q j k) -> !(q i j) -> Buffer F F F T F F q i l
  B4 :: !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer F F F F T F q i m
  B5 :: !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer F F F F F T q i n

instance Show (Buffer u v w x y z q i j) where
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

pushB :: q j k -> Buffer u v w x y F q i j -> Buffer F u v w x y q i k
pushB a B0 = B1 a
pushB a (B1 b) = B2 a b
pushB a (B2 b c) = B3 a b c
pushB a (B3 b c d) = B4 a b c d
pushB a (B4 b c d e) = B5 a b c d e

popB :: Buffer F v w x y z q i j -> HPair q (Buffer v w x y z F q) i j
popB (B1 a) = a `H` B0
popB (B2 a b) = a `H` B1 b
popB (B3 a b c) = a `H` B2 b c
popB (B4 a b c d) = a `H` B3 b c d
popB (B5 a b c d e) = a `H` B4 b c d e

pushB2 :: Pair q j k -> Buffer u v w x F F q i j -> Buffer F F u v w x q i k
pushB2 (P a b) cs = pushB a (pushB b cs)

popB2 :: Buffer F F w x y z q i j -> HPair (Pair q) (Buffer w x y z F F q) i j
popB2 as =
  case popB as of
    a `H` bs -> case popB bs of
      b `H` cs -> P a b `H` cs

injectB :: Buffer u v w x y F q j k -> q i j -> Buffer F u v w x y q i k
injectB B0 a = B1 a
injectB (B1 a) b = B2 a b
injectB (B2 a b) c = B3 a b c
injectB (B3 a b c) d = B4 a b c d
injectB (B4 a b c d) e = B5 a b c d e

ejectB :: Buffer F v w x y z q i j -> HPair (Buffer v w x y z F q) q i j
ejectB (B1 a) = B0 `H` a
ejectB (B2 a b) = B1 a `H` b
ejectB (B3 a b c) = B2 a b `H` c
ejectB (B4 a b c d) = B3 a b c `H` d
ejectB (B5 a b c d e) = B4 a b c d `H` e

injectB2 :: Buffer u v w x F F q j k -> Pair q i j -> Buffer F F u v w x q i k
injectB2 as (P b c) = injectB (injectB as b) c

ejectB2 :: Buffer F F w x y z q i j -> HPair (Buffer w x y z F F q) (Pair q) i j
ejectB2 cs = case ejectB cs of
  bs `H` c -> case ejectB bs of
    as `H` b -> as `H` P b c

data OverUnder u v w x y z q i j where
  Under :: Buffer u v F F F F q i j -> OverUnder u v w x y z q i j
  Okay :: Buffer F F w x F F q i j -> OverUnder u v w x y z q i j
  Over :: Buffer F F F F y z q i j -> OverUnder u v w x y z q i j

overUnder :: Buffer u v w x y z q i j -> OverUnder u v w x y z q i j
overUnder B0 = Under B0
overUnder (B1 a) = Under (B1 a)
overUnder (B2 a b) = Okay (B2 a b)
overUnder (B3 a b c) = Okay (B3 a b c)
overUnder (B4 a b c d) = Over (B4 a b c d)
overUnder (B5 a b c d e) = Over (B5 a b c d e)

data Nope i j where

data Fringe r y g q i j k l where
  RX :: !(Buffer s F F F F t q k l) -> !(Buffer u v w x y z q i j) -> Fringe T F F q i j k l
  XR :: !(Buffer F u v w x F q k l) -> !(Buffer y F F F F z q i j) -> Fringe T F F q i j k l
  YX :: !(Buffer F u F F v F q k l) -> !(Buffer F w x y z F q i j) -> Fringe F T F q i j k l
  GY :: !(Buffer F F w x F F q k l) -> !(Buffer F y F F z F q i j) -> Fringe F T F q i j k l
  GG :: !(Buffer F F w x F F q k l) -> !(Buffer F F y z F F q i j) -> Fringe F F T q i j k l

deriving instance Show (Fringe r y g q i j k l)

data Yellows q r i j k l where
  N :: Yellows q q i i l l
  Y :: !(Fringe F T F q i m n l) -> !(Yellows (Pair q) r m j k n) -> Yellows q r i j k l
  Y1 :: !(Buffer F x F F y F q i j) -> Yellows q Nope i j j j

deriving instance Show (Yellows q r i j k l)

data Level r y g q i j where
  Empty :: Level F F c q i i
  TinyH :: !(Buffer F F F g y r q i j) -> Level r y g q i j
  TinyL :: !(Buffer r y g F F F q i j) -> Level r y g q i j
  BigG :: !(Fringe F F T q i j m n) -> !(Yellows (Pair q) r j k l m) -> !(Level c1 F c2 r k l) -> Level F F T q i n
  BigY :: !(Fringe F T F q i j m n) -> !(Yellows (Pair q) r j k l m) -> !(Level c1 F c2 r k l) -> Level c1 T c2 q i n
  BigR :: !(Fringe T F F q i j m n) -> !(Yellows (Pair q) r j k l m) -> !(Level F F c r k l) -> Level T F F q i n

deriving instance Show (Level r y g q i j)

data Deque q i j where
  Deque :: !(Level F y g q i j) -> Deque q i j

deriving instance Show (Deque q i j)

{-
type family Col u v w x y z a b c d e f where
  Col u F F F F z a b c d e f = Red
  Col F u v w x F a F F F F f = Red
  Col F u F F v F F b c d e F = Yellow
  Col F F w x F F F b F F e F = Yellow
  Col F F w x F F F F c d F F = Green-}

toFringe :: (r ~ (u || z || a || f), ye ~ (Not r && (v || y || b || e)), g ~ (Not r && Not ye)) => Buffer u v w x y z q k l -> Buffer a b c d e f q i j -> Fringe r ye g q i j k l
toFringe a@B0{} b@B0{} = RX a b
toFringe a@B0{} b@B1{} = RX a b
toFringe a@B0{} b@B2{} = RX a b
toFringe a@B0{} b@B3{} = RX a b
toFringe a@B0{} b@B4{} = RX a b
toFringe a@B0{} b@B5{} = RX a b
toFringe a@B5{} b@B0{} = RX a b
toFringe a@B5{} b@B1{} = RX a b
toFringe a@B5{} b@B2{} = RX a b
toFringe a@B5{} b@B3{} = RX a b
toFringe a@B5{} b@B4{} = RX a b
toFringe a@B5{} b@B5{} = RX a b
toFringe a@B1{} b@B0{} = XR a b
toFringe a@B2{} b@B0{} = XR a b
toFringe a@B3{} b@B0{} = XR a b
toFringe a@B4{} b@B0{} = XR a b
toFringe a@B1{} b@B5{} = XR a b
toFringe a@B2{} b@B5{} = XR a b
toFringe a@B3{} b@B5{} = XR a b
toFringe a@B4{} b@B5{} = XR a b
toFringe a@B1{} b@B1{} = YX a b
toFringe a@B1{} b@B2{} = YX a b
toFringe a@B1{} b@B3{} = YX a b
toFringe a@B1{} b@B4{} = YX a b
toFringe a@B4{} b@B1{} = YX a b
toFringe a@B4{} b@B2{} = YX a b
toFringe a@B4{} b@B3{} = YX a b
toFringe a@B4{} b@B4{} = YX a b
toFringe a@B2{} b@B1{} = GY a b
toFringe a@B2{} b@B4{} = GY a b
toFringe a@B3{} b@B1{} = GY a b
toFringe a@B3{} b@B4{} = GY a b
toFringe a@B2{} b@B2{} = GG a b
toFringe a@B2{} b@B2{} = GG a b
toFringe a@B3{} b@B3{} = GG a b
toFringe a@B3{} b@B3{} = GG a b
{-- INLINE toFringe #-}

combine :: ((r && r') ~ F) => Fringe r y g q i j m n -> Level r' y' g' (Pair q) j m -> Level (r || (y && r')) y (g || (y && g')) q i n
combine f@(RX _ _) Empty = BigR f N Empty
combine f@(XR _ _) Empty = BigR f N Empty
combine f@(YX _ _) Empty = BigY f N Empty
combine f@(GY _ _) Empty = BigY f N Empty
combine f@(GG _ _) Empty = BigG f N Empty
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
combine f@(RX _ _) (TinyL b@B1{}) = BigR f (Y1 b) Empty
combine f@(RX _ _) (TinyH b@B4{}) = BigR f (Y1 b) Empty
combine f@(RX _ _) g@(TinyH B3{}) = BigR f N g
combine f@(RX _ _) g@(TinyL B2{}) = BigR f N g
combine f@(XR _ _) (TinyL b@B1{}) = BigR f (Y1 b) Empty
combine f@(XR _ _) (TinyH b@B4{}) = BigR f (Y1 b) Empty
combine f@(XR _ _) g@(TinyH B3{}) = BigR f N g
combine f@(XR _ _) g@(TinyL B2{}) = BigR f N g
combine f@(YX _ _) ls@(TinyL B0{}) = BigY f N ls
combine f@(YX _ _) ls@(TinyH B5{}) = BigY f N ls
combine f@(YX _ _) ls@(TinyL B2{}) = BigY f N ls
combine f@(YX _ _) ls@(TinyH B3{}) = BigY f N ls
combine f@(YX _ _) (TinyL b@B1{}) = BigY f (Y1 b) Empty
combine f@(YX _ _) (TinyH b@B4{}) = BigY f (Y1 b) Empty
combine f@(GY _ _) ls@(TinyL B0{}) = BigY f N ls
combine f@(GY _ _) ls@(TinyH B5{}) = BigY f N ls
combine f@(GY _ _) ls@(TinyL B2{}) = BigY f N ls
combine f@(GY _ _) ls@(TinyH B3{}) = BigY f N ls
combine f@(GY _ _) (TinyL b@B1{}) = BigY f (Y1 b) Empty
combine f@(GY _ _) (TinyH b@B4{}) = BigY f (Y1 b) Empty
combine f@(GG _ _) ls@(TinyL B0{}) = BigG f N ls
combine f@(GG _ _) ls@(TinyH B5{}) = BigG f N ls
combine f@(GG _ _) ls@(TinyL B2{}) = BigG f N ls
combine f@(GG _ _) ls@(TinyH B3{}) = BigG f N ls
combine f@(GG _ _) (TinyL b@B1{}) = BigG f (Y1 b) Empty
combine f@(GG _ _) (TinyH b@B4{}) = BigG f (Y1 b) Empty
combine f@(RX _ _) ls@(BigG _ _ _) = BigR f N ls
combine f@(XR _ _) ls@(BigG _ _ _) = BigR f N ls
combine f@(YX _ _) ls@(BigG _ _ _) = BigY f N ls
combine f@(GY _ _) ls@(BigG _ _ _) = BigY f N ls
combine f@(GG _ _) ls@(BigG _ _ _) = BigG f N ls
combine f@(RX _ _) ls@(BigG _ _ _) = BigR f N ls
combine f@(XR _ _) ls@(BigG _ _ _) = BigR f N ls
combine f@(YX _ _) ls@(BigG _ _ _) = BigY f N ls
combine f@(GY _ _) ls@(BigG _ _ _) = BigY f N ls
combine f@(GG _ _) ls@(BigG _ _ _) = BigG f N ls
{-- INLINE combine #-}

data LCons r y g q i n where
  LR :: !(Fringe r y g q i j m n) -> !(Level T y' g' (Pair q) j m) -> LCons r y g q i n
  LGY :: !(Fringe r y g q i j m n) -> !(Level F y' g' (Pair q) j m) -> LCons r y g q i n
  LEmpty :: LCons r y g q i n

{-
data FPair r ye g q i j k l where
  FP :: (r ~ (u || z || a || f), ye ~ (Not r && (v || y || b || e)), g ~ (Not r && Not y)) => !(Buffer a b c d e f q k l) -> !(Buffer u v w x y z q i j) -> FPair r ye g q i j k l

splitFringe :: Fringe r y g q i j k l -> FPair r y g q i j k l
splitFringe = undefined
-}

toTiny :: (r ~ (a || f), ye ~ (Not r && (b || e)), g ~ (Not r && Not ye)) => Buffer a b c d e f q i j -> Level r ye g q i j
toTiny b@B0{} = TinyL b
toTiny b@B1{} = TinyL b
toTiny b@B2{} = TinyL b
toTiny b@B3{} = TinyH b
toTiny b@B4{} = TinyH b
toTiny b@B5{} = TinyH b
{-# INLINE toTiny #-}

popL :: Level r y g q i j -> LCons (r && Not y) y (g && Not y) q i j
popL Empty = LEmpty
popL (TinyH _) = LEmpty
popL (TinyL _) = LEmpty
popL (BigG f N ls@Empty) = LGY f ls
popL (BigG f N ls@(TinyH B5{})) = LR f ls
popL (BigG f N ls@(TinyL B0{})) = LR f ls
popL (BigG f N ls@(TinyH B3{})) = LGY f ls
popL (BigG f N ls@(TinyL B2{})) = LGY f ls
popL (BigG f N ls@(BigR _ _ _)) = LR f ls
popL (BigG f N ls@(BigG _ _ _)) = LGY f ls
popL (BigG f (Y1 b) Empty) = LGY f (toTiny b)
popL (BigG f (Y y ys) ls@Empty) = LGY f (BigY y ys ls)
popL (BigG f (Y y ys) ls@(TinyH B5{})) = LR f (BigY y ys ls)
popL (BigG f (Y y ys) ls@(TinyL B0{})) = LR f (BigY y ys ls)
popL (BigG f (Y y ys) ls@(TinyH B3{})) = LGY f (BigY y ys ls)
popL (BigG f (Y y ys) ls@(TinyL B2{})) = LGY f (BigY y ys ls)
popL (BigG f (Y y ys) ls@(BigR _ _ _)) = LR f (BigY y ys ls)
popL (BigG f (Y y ys) ls@(BigG _ _ _)) = LGY f (BigY y ys ls)
popL (BigY f N ls@Empty) = LGY f ls
popL (BigY f N ls@(TinyH B5{})) = LR f ls
popL (BigY f N ls@(TinyL B0{})) = LR f ls
popL (BigY f N ls@(TinyH B3{})) = LGY f ls
popL (BigY f N ls@(TinyL B2{})) = LGY f ls
popL (BigY f N ls@(BigR _ _ _)) = LR f ls
popL (BigY f N ls@(BigG _ _ _)) = LGY f ls
popL (BigY f (Y1 b) Empty) = LGY f (toTiny b)
popL (BigY f (Y y ys) ls@Empty) = LGY f (BigY y ys ls)
popL (BigY f (Y y ys) ls@(TinyH B5{})) = LR f (BigY y ys ls)
popL (BigY f (Y y ys) ls@(TinyL B0{})) = LR f (BigY y ys ls)
popL (BigY f (Y y ys) ls@(TinyH B3{})) = LGY f (BigY y ys ls)
popL (BigY f (Y y ys) ls@(TinyL B2{})) = LGY f (BigY y ys ls)
popL (BigY f (Y y ys) ls@(BigR _ _ _)) = LR f (BigY y ys ls)
popL (BigY f (Y y ys) ls@(BigG _ _ _)) = LGY f (BigY y ys ls)
popL (BigR f N ls@Empty) = LGY f ls
popL (BigR f N ls@(TinyH B3{})) = LGY f ls
popL (BigR f N ls@(TinyL B2{})) = LGY f ls
popL (BigR f N ls@(BigG _ _ _)) = LGY f ls
popL (BigR f (Y1 b) Empty) = LGY f (toTiny b)
popL (BigR f (Y y ys) ls@Empty) = LGY f (BigY y ys ls)
popL (BigR f (Y y ys) ls@(TinyH B3{})) = LGY f (BigY y ys ls)
popL (BigR f (Y y ys) ls@(TinyL B2{})) = LGY f (BigY y ys ls)
popL (BigR f (Y y ys) ls@(BigG _ _ _)) = LGY f (BigY y ys ls)
{-# INLINE popL #-}

moveUpL :: Buffer u v w x F F q j k -> Buffer F b c d e f (Pair q) i j -> HPair (Buffer F F u v w x q) (Buffer b c d e f F (Pair q)) i k
moveUpL b1 b2 = case popB b2 of H p b2' -> injectB2 b1 p `H` b2'
{-# INLINE moveUpL #-}

moveDownL :: Buffer F F w x y z q j k -> Buffer a b c d e F (Pair q) i j -> HPair (Buffer w x y z F F q) (Buffer F a b c d e (Pair q)) i k
moveDownL b1 b2 = case ejectB2 b1 of H b1' p -> b1' `H` pushB p b2
{-# INLINE moveDownL #-}

moveDownR :: Buffer u v w x y F (Pair q) j k -> Buffer F F c d e f q i j -> HPair (Buffer F u v w x y (Pair q)) (Buffer c d e f F F q) i k
moveDownR b1 b2 = case popB2 b2 of H p b2' -> injectB b1 p `H` b2'
{-# INLINE moveDownR #-}

moveUpR :: Buffer F v w x y z (Pair q) j k -> Buffer a b c d F F q i j -> HPair (Buffer v w x y z F (Pair q)) (Buffer F F a b c d q) i k
moveUpR b1 b2 = case ejectB b1 of H b1' p -> b1' `H` pushB2 p b2
{-# INLINE moveUpR #-}

fixup :: Yellows q r i j k l -> Level T F F r j k -> Deque q i l
fixup y z = implant y (fixup' z)
{-# INLINE fixup #-}

fixup' :: Level T F F q i j -> Level F F T q i j
fixup' (popL -> LGY f1 (popL -> LGY f2 ls)) = case (f1, f2) of
  (RX b1 b2, YX b3 b4) ->  case (overUnder b1, overUnder b2) of
    (Under b1' , Under b2') -> let l = moveUpL b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Under b2') -> let l = H b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Under b2') -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Okay b2')  -> let l = moveUpL b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Okay b2')  -> let l = H b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Okay b2')  -> let l = moveDownL b1' b3 in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Over b2')  -> let l = moveUpL b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Over b2')  -> let l = H b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Over b2')  -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
  (RX b1 b2, GY b3 b4) ->  case (overUnder b1, overUnder b2) of
    (Under b1' , Under b2') -> let l = moveUpL b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Under b2') -> let l = H b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Under b2') -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Okay b2')  -> let l = moveUpL b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Okay b2')  -> let l = H b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Okay b2')  -> let l = moveDownL b1' b3 in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Over b2')  -> let l = moveUpL b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Over b2')  -> let l = H b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Over b2')  -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
  (RX b1 b2, GG b3 b4) ->  case (overUnder b1, overUnder b2) of
    (Under b1' , Under b2') -> let l = moveUpL b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Under b2') -> let l = H b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Under b2') -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Okay b2')  -> let l = moveUpL b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Okay b2')  -> let l = H b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Okay b2')  -> let l = moveDownL b1' b3 in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Over b2')  -> let l = moveUpL b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Over b2')  -> let l = H b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Over b2')  -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
  (XR b1 b2, YX b3 b4) ->  case (overUnder b1, overUnder b2) of
    (Under b1' , Under b2') -> let l = moveUpL b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Under b2') -> let l = H b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Under b2') -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Okay b2')  -> let l = moveUpL b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Okay b2')  -> let l = H b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Okay b2')  -> let l = moveDownL b1' b3 in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Over b2')  -> let l = moveUpL b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Over b2')  -> let l = H b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Over b2')  -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
  (XR b1 b2, GY b3 b4) ->  case (overUnder b1, overUnder b2) of
    (Under b1' , Under b2') -> let l = moveUpL b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Under b2') -> let l = H b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Under b2') -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Okay b2')  -> let l = moveUpL b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Okay b2')  -> let l = H b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Okay b2')  -> let l = moveDownL b1' b3 in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Over b2')  -> let l = moveUpL b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Over b2')  -> let l = H b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Over b2')  -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
  (XR b1 b2, GG b3 b4) ->  case (overUnder b1, overUnder b2) of
    (Under b1' , Under b2') -> let l = moveUpL b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Under b2') -> let l = H b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Under b2') -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Okay b2')  -> let l = moveUpL b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Okay b2')  -> let l = H b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Okay b2')  -> let l = moveDownL b1' b3 in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Over b2')  -> let l = moveUpL b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Over b2')  -> let l = H b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Over b2')  -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
fixup' (popL -> LGY f1 (popL -> LR f2 ls)) = case (f1, f2) of
  (RX b1 b2, GG b3 b4) ->  case (overUnder b1, overUnder b2) of
    (Under b1' , Under b2') -> let l = moveUpL b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Under b2') -> let l = H b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Under b2') -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Okay b2')  -> let l = moveUpL b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Okay b2')  -> let l = H b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Okay b2')  -> let l = moveDownL b1' b3 in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Over b2')  -> let l = moveUpL b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Over b2')  -> let l = H b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Over b2')  -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
  (XR b1 b2, GG b3 b4) ->  case (overUnder b1, overUnder b2) of
    (Under b1' , Under b2') -> let l = moveUpL b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Under b2') -> let l = H b1' b3   in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Under b2') -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Okay b2')  -> let l = moveUpL b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Okay b2')  -> let l = H b1' b3   in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Okay b2')  -> let l = moveDownL b1' b3 in let r = H b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Under b1' , Over b2')  -> let l = moveUpL b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Okay b1'  , Over b2')  -> let l = H b1' b3   in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
    (Over b1'  , Over b2')  -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combine (toFringe c1 c4) $ combine (toFringe c2 c3) ls
fixup' (TinyL B0) = Empty -- probably can't happen, but it's handled
fixup' (TinyH (B5 a b c d e)) = BigG (GG (B2 a b) (B3 c d e)) N Empty
fixup' (BigR (RX B0 (B0))                       N Empty)                                = Empty
--fixup' (BigR (RX B0 (B1 n))                     N Empty)                                = go1 n
fixup' (BigR (RX B0 (B2 n o))                   N Empty)                                = go2 n o
fixup' (BigR (RX B0 (B3 n o p))                 N Empty)                                = go3 n o p
fixup' (BigR (RX B0 (B4 n o p q))               N Empty)                                = go4 n o p q
fixup' (BigR (RX B0 (B5 n o p q r))             N Empty)                                = go5 n o p q r
fixup' (BigR (RX (B5 a b c d e) (B0))           N Empty)                                = go5 a b c d e
fixup' (BigR (RX (B5 a b c d e) (B1 n))         N Empty)                                = go6 a b c d e n
fixup' (BigR (RX (B5 a b c d e) (B2 n o))       N Empty)                                = go7 a b c d e n o
fixup' (BigR (RX (B5 a b c d e) (B3 n o p))     N Empty)                                = go8 a b c d e n o p
fixup' (BigR (RX (B5 a b c d e) (B4 n o p q))   N Empty)                                = go9 a b c d e n o p q
fixup' (BigR (RX (B5 a b c d e) (B5 n o p q r)) N Empty)                                = go10 a b c d e n o p q r
--fixup' (BigR (XR (B1 a) (B0))                   N Empty)                                = go1 a
fixup' (BigR (XR (B1 a) (B5 n o p q r))         N Empty)                                = go6 a n o p q r
fixup' (BigR (XR (B2 a b) (B0))                 N Empty)                                = go2 a b
fixup' (BigR (XR (B2 a b) (B5 n o p q r))       N Empty)                                = go7 a b n o p q r
fixup' (BigR (XR (B3 a b c) (B0))               N Empty)                                = go3 a b c
fixup' (BigR (XR (B3 a b c) (B5 n o p q r))     N Empty)                                = go8 a b c n o p q r
fixup' (BigR (XR (B4 a b c d) (B0))             N Empty)                                = go4 a b c d
fixup' (BigR (XR (B4 a b c d) (B5 n o p q r))   N Empty)                                = go9 a b c d n o p q r
--fixup' (BigR (RX B0 (B0))                       (Y1 (B1 s)) Empty)                      = go1 s
fixup' (BigR (RX B0 (B1 n))                     (Y1 (B1 (P s t))) Empty)                      = go3 s t n
fixup' (BigR (RX B0 (B2 n o))                   (Y1 (B1 (P s t))) Empty)                      = go4 s t n o
fixup' (BigR (RX B0 (B3 n o p))                 (Y1 (B1 (P s t))) Empty)                      = go5 s t n o p
fixup' (BigR (RX B0 (B4 n o p q))               (Y1 (B1 (P s t))) Empty)                      = go6 s t n o p q
fixup' (BigR (RX B0 (B5 n o p q r))             (Y1 (B1 (P s t))) Empty)                      = go7 s t n o p q r
fixup' (BigR (RX (B5 a b c d e) (B0))           (Y1 (B1 (P s t))) Empty)                      = go7 a b c d e s t
fixup' (BigR (RX (B5 a b c d e) (B1 n))         (Y1 (B1 (P s t))) Empty)                      = go8 a b c d e s t n
fixup' (BigR (RX (B5 a b c d e) (B2 n o))       (Y1 (B1 (P s t))) Empty)                      = go9 a b c d e s t n o
fixup' (BigR (RX (B5 a b c d e) (B3 n o p))     (Y1 (B1 (P s t))) Empty)                      = go10 a b c d e s t n o p
fixup' (BigR (RX (B5 a b c d e) (B4 n o p q))   (Y1 (B1 (P s t))) Empty)                      = go11 a b c d e s t n o p q
fixup' (BigR (RX (B5 a b c d e) (B5 n o p q r)) (Y1 (B1 (P s t))) Empty)                      = go12 a b c d e s t n o p q r
fixup' (BigR (XR (B1 a) (B0))                   (Y1 (B1 (P s t))) Empty)                      = go3 a s t
fixup' (BigR (XR (B1 a) (B5 n o p q r))         (Y1 (B1 (P s t))) Empty)                      = go8 a s t n o p q r
fixup' (BigR (XR (B2 a b) (B0))                 (Y1 (B1 (P s t))) Empty)                      = go4 a b s t
fixup' (BigR (XR (B2 a b) (B5 n o p q r))       (Y1 (B1 (P s t))) Empty)                      = go9 a b s t n o p q r
fixup' (BigR (XR (B3 a b c) (B0))               (Y1 (B1 (P s t))) Empty)                      = go5 a b c s t
fixup' (BigR (XR (B3 a b c) (B5 n o p q r))     (Y1 (B1 (P s t))) Empty)                      = go10 a b c s t n o p q r
fixup' (BigR (XR (B4 a b c d) (B0))             (Y1 (B1 (P s t))) Empty)                      = go6 a b c d s t
fixup' (BigR (XR (B4 a b c d) (B5 n o p q r))   (Y1 (B1 (P s t))) Empty)                      = go11 a b c d s t n o p q r
fixup' (BigR (RX B0 (B0))                       (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go8 s t u v w x y z
fixup' (BigR (RX B0 (B1 n))                     (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go9 s t u v w x y z n
fixup' (BigR (RX B0 (B2 n o))                   (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go10 s t u v w x y z n o
fixup' (BigR (RX B0 (B3 n o p))                 (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go11 s t u v w x y z n o p
fixup' (BigR (RX B0 (B4 n o p q))               (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go12 s t u v w x y z n o p q
fixup' (BigR (RX B0 (B5 n o p q r))             (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go13 s t u v w x y z n o p q r
fixup' (BigR (RX (B5 a b c d e) (B0))           (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go13 a b c d e s t u v w x y z
fixup' (BigR (RX (B5 a b c d e) (B1 n))         (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go14 a b c d e s t u v w x y z n
fixup' (BigR (RX (B5 a b c d e) (B2 n o))       (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go15 a b c d e s t u v w x y z n o
fixup' (BigR (RX (B5 a b c d e) (B3 n o p))     (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go16 a b c d e s t u v w x y z n o p
fixup' (BigR (RX (B5 a b c d e) (B4 n o p q))   (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go17 a b c d e s t u v w x y z n o p q
fixup' (BigR (RX (B5 a b c d e) (B5 n o p q r)) (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go18 a b c d e s t u v w x y z n o p q r
fixup' (BigR (XR (B1 a) (B0))                   (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go9 a s t u v w x y z
fixup' (BigR (XR (B1 a) (B5 n o p q r))         (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go14 a s t u v w x y z n o p q r
fixup' (BigR (XR (B2 a b) (B0))                 (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go10 a b s t u v w x y z
fixup' (BigR (XR (B2 a b) (B5 n o p q r))       (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go15 a b s t u v w x y z n o p q r
fixup' (BigR (XR (B3 a b c) (B0))               (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go11 a b c s t u v w x y z
fixup' (BigR (XR (B3 a b c) (B5 n o p q r))     (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go16 a b c s t u v w x y z n o p q r
fixup' (BigR (XR (B4 a b c d) (B0))             (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go12 a b c d s t u v w x y z
fixup' (BigR (XR (B4 a b c d) (B5 n o p q r))   (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) Empty)                = go17 a b c d s t u v w x y z n o p q r
fixup' (BigR (RX B0 (B0))                       N (TinyL (B2 (P s t) (P u v))))         = go4 s t u v
fixup' (BigR (RX B0 (B1 n))                     N (TinyL (B2 (P s t) (P u v))))         = go5 s t u v n
fixup' (BigR (RX B0 (B2 n o))                   N (TinyL (B2 (P s t) (P u v))))         = go6 s t u v n o
fixup' (BigR (RX B0 (B3 n o p))                 N (TinyL (B2 (P s t) (P u v))))         = go7 s t u v n o p
fixup' (BigR (RX B0 (B4 n o p q))               N (TinyL (B2 (P s t) (P u v))))         = go8 s t u v n o p q
fixup' (BigR (RX B0 (B5 n o p q r))             N (TinyL (B2 (P s t) (P u v))))         = go9 s t u v n o p q r
fixup' (BigR (RX (B5 a b c d e) (B0))           N (TinyL (B2 (P s t) (P u v))))         = go9 a b c d e s t u v
fixup' (BigR (RX (B5 a b c d e) (B1 n))         N (TinyL (B2 (P s t) (P u v))))         = go10 a b c d e s t u v n
fixup' (BigR (RX (B5 a b c d e) (B2 n o))       N (TinyL (B2 (P s t) (P u v))))         = go11 a b c d e s t u v n o
fixup' (BigR (RX (B5 a b c d e) (B3 n o p))     N (TinyL (B2 (P s t) (P u v))))         = go12 a b c d e s t u v n o p
fixup' (BigR (RX (B5 a b c d e) (B4 n o p q))   N (TinyL (B2 (P s t) (P u v))))         = go13 a b c d e s t u v n o p q
fixup' (BigR (RX (B5 a b c d e) (B5 n o p q r)) N (TinyL (B2 (P s t) (P u v))))         = go14 a b c d e s t u v n o p q r
fixup' (BigR (XR (B1 a) (B0))                   N (TinyL (B2 (P s t) (P u v))))         = go5 a s t u v
fixup' (BigR (XR (B1 a) (B5 n o p q r))         N (TinyL (B2 (P s t) (P u v))))         = go10 a s t u v n o p q r
fixup' (BigR (XR (B2 a b) (B0))                 N (TinyL (B2 (P s t) (P u v))))         = go6 a b s t u v
fixup' (BigR (XR (B2 a b) (B5 n o p q r))       N (TinyL (B2 (P s t) (P u v))))         = go11 a b s t u v n o p q r
fixup' (BigR (XR (B3 a b c) (B0))               N (TinyL (B2 (P s t) (P u v))))         = go7 a b c s t u v
fixup' (BigR (XR (B3 a b c) (B5 n o p q r))     N (TinyL (B2 (P s t) (P u v))))         = go12 a b c s t u v n o p q r
fixup' (BigR (XR (B4 a b c d) (B0))             N (TinyL (B2 (P s t) (P u v))))         = go8 a b c d s t u v
fixup' (BigR (XR (B4 a b c d) (B5 n o p q r))   N (TinyL (B2 (P s t) (P u v))))         = go13 a b c d s t u v n o p q r
fixup' (BigR (RX B0 (B0))                       N (TinyH (B3 (P s t) (P u v) (P w x)))) = go6 s t u v w x
fixup' (BigR (RX B0 (B1 n))                     N (TinyH (B3 (P s t) (P u v) (P w x)))) = go7 s t u v w x n
fixup' (BigR (RX B0 (B2 n o))                   N (TinyH (B3 (P s t) (P u v) (P w x)))) = go8 s t u v w x n o
fixup' (BigR (RX B0 (B3 n o p))                 N (TinyH (B3 (P s t) (P u v) (P w x)))) = go9 s t u v w x n o p
fixup' (BigR (RX B0 (B4 n o p q))               N (TinyH (B3 (P s t) (P u v) (P w x)))) = go10 s t u v w x n o p q
fixup' (BigR (RX B0 (B5 n o p q r))             N (TinyH (B3 (P s t) (P u v) (P w x)))) = go11 s t u v w x n o p q r
fixup' (BigR (RX (B5 a b c d e) (B0))           N (TinyH (B3 (P s t) (P u v) (P w x)))) = go11 a b c d e s t u v w x
fixup' (BigR (RX (B5 a b c d e) (B1 n))         N (TinyH (B3 (P s t) (P u v) (P w x)))) = go12 a b c d e s t u v w x n
fixup' (BigR (RX (B5 a b c d e) (B2 n o))       N (TinyH (B3 (P s t) (P u v) (P w x)))) = go13 a b c d e s t u v w x n o
fixup' (BigR (RX (B5 a b c d e) (B3 n o p))     N (TinyH (B3 (P s t) (P u v) (P w x)))) = go14 a b c d e s t u v w x n o p
fixup' (BigR (RX (B5 a b c d e) (B4 n o p q))   N (TinyH (B3 (P s t) (P u v) (P w x)))) = go15 a b c d e s t u v w x n o p q
fixup' (BigR (RX (B5 a b c d e) (B5 n o p q r)) N (TinyH (B3 (P s t) (P u v) (P w x)))) = go16 a b c d e s t u v w x n o p q r
fixup' (BigR (XR (B1 a) (B0))                   N (TinyH (B3 (P s t) (P u v) (P w x)))) = go7 a s t u v w x
fixup' (BigR (XR (B1 a) (B5 n o p q r))         N (TinyH (B3 (P s t) (P u v) (P w x)))) = go12 a s t u v w x n o p q r
fixup' (BigR (XR (B2 a b) (B0))                 N (TinyH (B3 (P s t) (P u v) (P w x)))) = go8 a b s t u v w x
fixup' (BigR (XR (B2 a b) (B5 n o p q r))       N (TinyH (B3 (P s t) (P u v) (P w x)))) = go13 a b s t u v w x n o p q r
fixup' (BigR (XR (B3 a b c) (B0))               N (TinyH (B3 (P s t) (P u v) (P w x)))) = go9 a b c s t u v w x
fixup' (BigR (XR (B3 a b c) (B5 n o p q r))     N (TinyH (B3 (P s t) (P u v) (P w x)))) = go14 a b c s t u v w x n o p q r
fixup' (BigR (XR (B4 a b c d) (B0))             N (TinyH (B3 (P s t) (P u v) (P w x)))) = go10 a b c d s t u v w x
fixup' (BigR (XR (B4 a b c d) (B5 n o p q r))   N (TinyH (B3 (P s t) (P u v) (P w x)))) = go15 a b c d s t u v w x n o p q r
{-# INLINE fixup' #-}

go2 a b                                              = TinyL (B2 a b)
go3 a b c                                            = TinyH (B3 a b c)
go4 a b c d                                          = BigG (GG (B2 a b) (B2 c d)) N Empty
go5 a b c d e                                        = BigG (GG (B2 a b) (B3 c d e)) N Empty
go6 a b c d e f                                      = BigG (GG (B3 a b c) (B3 d e f)) N Empty
go7 a b c d e f g                                    = BigG (GG (B3 a b c) (B2 f g)) (Y1 (B1 (P d e))) Empty
go8 a b c d e f g h                                  = BigG (GG (B3 a b c) (B3 f g h)) (Y1 (B1 (P d e))) Empty
go9 a b c d e f g h i                                = BigG (GG (B3 a b c) (B2 h i)) (Y (YX (B1 (P d e)) (B1 (P f g))) N) Empty
go10 a b c d e f g h i j                             = BigG (GG (B3 a b c) (B3 h i j)) (Y (YX (B1 (P d e)) (B1 (P f g))) N) Empty
go11 a b c d e f g h i j k                           = BigG (GG (B3 a b c) (B2 j k)) (Y (YX (B1 (P d e)) (B2 (P f g) (P h i))) N) Empty
go12 a b c d e f g h i j k l                         = BigG (GG (B3 a b c) (B3 j k l)) (Y (YX (B1 (P d e)) (B2 (P f g) (P h i))) N) Empty
go13 a b c d e f g h i j k l m                       = BigG (GG (B3 a b c) (B2 l m)) (Y (YX (B1 (P d e)) (B3 (P f g) (P h i) (P j k))) N) Empty
go14 a b c d e f g h i j k l m n                     = BigG (GG (B3 a b c) (B3 l m n)) (Y (YX (B1 (P d e)) (B3 (P f g) (P h i) (P j k))) N) Empty
go15 a b c d e f g h i j k l m n o                   = BigG (GG (B3 a b c) (B2 n o)) (Y (YX (B1 (P d e)) (B4 (P f g) (P h i) (P j k) (P l m))) N) Empty
go16 a b c d e f g h i j k l m n o p                 = BigG (GG (B3 a b c) (B3 n o p)) (Y (YX (B1 (P d e)) (B4 (P f g) (P h i) (P j k) (P l m))) N) Empty
go17 a b c d e f g h i j k l m n o p q               = BigG (GG (B3 a b c) (B2 p q)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B2 (P l m) (P n o))) N) Empty
go18 a b c d e f g h i j k l m n o p q r             = BigG (GG (B3 a b c) (B3 p q r)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B2 (P l m) (P n o))) N) Empty
go19 a b c d e f g h i j k l m n o p q r s           = BigG (GG (B3 a b c) (B2 r s)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B3 (P l m) (P n o) (P p q))) N) Empty
go20 a b c d e f g h i j k l m n o p q r s t         = BigG (GG (B3 a b c) (B3 r s t)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B3 (P l m) (P n o) (P p q))) N) Empty
go21 a b c d e f g h i j k l m n o p q r s t u       = BigG (GG (B3 a b c) (B2 t u)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B4 (P l m) (P n o) (P p q) (P s t))) N) Empty
go22 a b c d e f g h i j k l m n o p q r s t u v     = BigG (GG (B3 a b c) (B3 t u v)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B4 (P l m) (P n o) (P p q) (P s t))) N) Empty

implant :: Yellows q r i j k l -> Level F F T r j k -> Deque q i l
implant N Empty = Deque $ Empty
implant N (TinyL b) = Deque $ TinyL b
implant N (TinyH b) = Deque $ TinyH b
implant N (BigG b y z) = Deque $ BigG b y z
implant (Y1 b@B1{}) _ = Deque $ TinyL b -- in agda we could properly eliminate the impossible cases here :( however the thristing ensures we can't throw anything away.
implant (Y1 b@B4{}) _ = Deque $ TinyH b
implant (Y y ys) z = Deque $ BigY y ys z
{-# INLINE implant #-}

push :: q j k -> Deque q i j -> Deque q i k
push a (Deque Empty) = Deque $ TinyL (B1 a)
push a (Deque (TinyL (B1 b))) = Deque $ TinyL (B2 a b)
push a (Deque (TinyL (B2 b c))) = Deque $ TinyH (B3 a b c)
push a (Deque (TinyH (B3 b c d))) = Deque $ TinyH (B4 a b c d)
push a (Deque (TinyH (B4 b c d e))) = fixup N (TinyH (B5 a b c d e))
push a (Deque (BigY (YX (B1 b) (B1 i)) y z)) = Deque $ BigY (GY (B2 a b) (B1 i)) y z
push a (Deque (BigY (YX (B1 b) (B2 i j)) y z)) = Deque $ BigG (GG (B2 a b) (B2 i j)) y z
push a (Deque (BigY (YX (B1 b) (B3 i j k)) y z)) = Deque $ BigG (GG (B2 a b) (B3 i j k)) y z
push a (Deque (BigY (YX (B1 b) (B4 i j k l)) y z)) = Deque $ BigY (GY (B2 a b) (B4 i j k l)) y z
push a (Deque (BigY (GY (B2 b c) x) y z)) = Deque $ BigY (GY (B3 a b c) x) y z
push a (Deque (BigG (GG (B2 b c) x) y z)) = Deque $ BigG (GG (B3 a b c) x) y z
push a (Deque (BigY (GY (B3 b c d) x) y z)) = Deque $ BigY (YX (B4 a b c d) x) y z
push a (Deque (BigG (GG (B3 b c d) x) y Empty)) = Deque $ BigY (YX (B4 a b c d) x) y Empty
push a (Deque (BigG (GG (B3 b c d) x) y z@(TinyL B0))) = Deque $ BigY (YX (B4 a b c d) x) y (fixup' z)
push a (Deque (BigG (GG (B3 b c d) x) y z@(TinyH B5{}))) = Deque $ BigY (YX (B4 a b c d) x) y (fixup' z)
push a (Deque (BigG (GG (B3 b c d) x) y z@(TinyL B2{}))) = Deque $ BigY (YX (B4 a b c d) x) y z
push a (Deque (BigG (GG (B3 b c d) x) y z@(TinyH B3{}))) = Deque $ BigY (YX (B4 a b c d) x) y z
push a (Deque (BigG (GG (B3 b c d) x) y z@(BigR{}))) = Deque $ BigY (YX (B4 a b c d) x) y (fixup' z)
push a (Deque (BigG (GG (B3 b c d) x) y z@(BigG{}))) = Deque $ BigY (YX (B4 a b c d) x) y z
push a (Deque (BigY (YX (B4 b c d e) x) y z)) = fixup N (BigR (RX (B5 a b c d e) x) y z)
{-# INLINE push #-}

empty = Deque Empty

data Foo a b where
  F :: Int -> Foo () ()

deriving instance Show (Foo a b)
