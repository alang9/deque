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
import qualified Data.Sequence as Seq

data Nat = Z | S Nat deriving (Read, Show, Eq, Ord)
data Color = Red | Yellow | Green deriving (Read, Show, Eq, Ord)
data Trend = Lo | Hi deriving (Read, Show, Eq, Ord)

type T = True
type F = False

data Buffer q i j where
  B0 :: Buffer q i i
  B1 :: !(q i j) -> Buffer q i j
  B2 :: !(q j k) -> !(q i j) -> Buffer q i k
  B3 :: !(q k l) -> !(q j k) -> !(q i j) -> Buffer q i l
  B4 :: !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer q i m
  B5 :: !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer q i n

instance Show (Buffer q i j) where
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

pushB :: q j k -> Buffer q i j -> Buffer q i k
pushB a B0 = B1 a
pushB a (B1 b) = B2 a b
pushB a (B2 b c) = B3 a b c
pushB a (B3 b c d) = B4 a b c d
pushB a (B4 b c d e) = B5 a b c d e
{-- INLINE pushB #-}

popB :: Buffer q i j -> HPair q (Buffer q) i j
popB (B1 a) = a `H` B0
popB (B2 a b) = a `H` B1 b
popB (B3 a b c) = a `H` B2 b c
popB (B4 a b c d) = a `H` B3 b c d
popB (B5 a b c d e) = a `H` B4 b c d e
{-- INLINE popB #-}

pushB2 :: Pair q j k -> Buffer q i j -> Buffer q i k
pushB2 (P a b) cs = pushB a (pushB b cs)
{-- INLINE pushB2 #-}

popB2 :: Buffer q i j -> HPair (Pair q) (Buffer q) i j
popB2 as =
  case popB as of
    a `H` bs -> case popB bs of
      b `H` cs -> P a b `H` cs
{-- INLINE popB2 #-}

injectB :: Buffer q j k -> q i j -> Buffer q i k
injectB B0 a = B1 a
injectB (B1 a) b = B2 a b
injectB (B2 a b) c = B3 a b c
injectB (B3 a b c) d = B4 a b c d
injectB (B4 a b c d) e = B5 a b c d e
{-- INLINE injectB #-}

ejectB :: Buffer q i j -> HPair (Buffer q) q i j
ejectB (B1 a) = B0 `H` a
ejectB (B2 a b) = B1 a `H` b
ejectB (B3 a b c) = B2 a b `H` c
ejectB (B4 a b c d) = B3 a b c `H` d
ejectB (B5 a b c d e) = B4 a b c d `H` e
{-- INLINE ejectB #-}

injectB2 :: Buffer q j k -> Pair q i j -> Buffer q i k
injectB2 as (P b c) = injectB (injectB as b) c
{-- INLINE injectB2 #-}

ejectB2 :: Buffer q i j -> HPair (Buffer q) (Pair q) i j
ejectB2 cs = case ejectB cs of
  bs `H` c -> case ejectB bs of
    as `H` b -> as `H` P b c
{-- INLINE ejectB2 #-}

data OverUnder q i j where
  Under :: Buffer q i j -> OverUnder q i j
  Okay :: Buffer q i j -> OverUnder q i j
  Over :: Buffer q i j -> OverUnder q i j

overUnder :: Buffer q i j -> OverUnder q i j
overUnder B0 = Under B0
overUnder (B1 a) = Under (B1 a)
overUnder (B2 a b) = Okay (B2 a b)
overUnder (B3 a b c) = Okay (B3 a b c)
overUnder (B4 a b c d) = Over (B4 a b c d)
overUnder (B5 a b c d e) = Over (B5 a b c d e)
{-- INLINE overUnder #-}

data Nope i j where

data Fringe q i j k l where
  RX :: !(Buffer q k l) -> !(Buffer q i j) -> Fringe q i j k l
  XR :: !(Buffer q k l) -> !(Buffer q i j) -> Fringe q i j k l
  YX :: !(Buffer q k l) -> !(Buffer q i j) -> Fringe q i j k l
  GY :: !(Buffer q k l) -> !(Buffer q i j) -> Fringe q i j k l
  GG :: !(Buffer q k l) -> !(Buffer q i j) -> Fringe q i j k l

deriving instance Show (Fringe q i j k l)

data Yellows q r i j k l where
  N :: Yellows q q i i l l
  Y :: !(Fringe q i m n l) -> !(Yellows (Pair q) r m j k n) -> Yellows q r i j k l
  Y1 :: !(Buffer q i j) -> Yellows q Nope i j j j

deriving instance Show (Yellows q r i j k l)

data Level q i j where
  LEmpty :: Level q i i
  TinyH :: !(Buffer q i j) -> Level q i j
  TinyL :: !(Buffer q i j) -> Level q i j
  BigG :: !(Fringe q i j m n) -> !(Yellows (Pair q) r j k l m) -> !(Level r k l) -> Level q i n
  BigY :: !(Fringe q i j m n) -> !(Yellows (Pair q) r j k l m) -> !(Level r k l) -> Level q i n
  BigR :: !(Fringe q i j m n) -> !(Yellows (Pair q) r j k l m) -> !(Level r k l) -> Level q i n

deriving instance Show (Level q i j)

data Deque q i j where
  Deque :: !(Level q i j) -> Deque q i j

deriving instance Show (Deque q i j)

toFringe :: Buffer q k l -> Buffer q i j -> Fringe q i j k l
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
toFringe a@B2{} b@B3{} = GG a b
toFringe a@B3{} b@B2{} = GG a b
toFringe a@B3{} b@B3{} = GG a b
{-- INLINE toFringe #-}

combine :: Fringe q i j m n -> Level (Pair q) j m -> Level q i n
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

combineGG :: Fringe q i j m n -> Level (Pair q) j m -> Level q i n
combineGG f LEmpty = BigG f N LEmpty
combineGG f (BigY y ys ls) = BigG f (Y y ys) ls
combineGG f ls@(BigG _ _ _) = BigG f N ls
combineGG f ls@(BigR _ _ _) = BigG f N ls
combineGG f ls@(TinyH B5{}) = BigG f N ls
combineGG f ls@TinyL{} = BigG f N ls
combineGG f (TinyH b@B4{}) = BigG f (Y1 b) LEmpty
{-- INLINE combineGG #-}

data LCons q i n where
  LR :: !(Fringe q i j m n) -> !(Level (Pair q) j m) -> LCons q i n
  LGY :: !(Fringe q i j m n) -> !(Level (Pair q) j m) -> LCons q i n
  LLEmpty :: LCons q i n

toTiny :: Buffer q i j -> Level q i j
toTiny b@B0{} = TinyL b
toTiny b@B1{} = TinyL b
toTiny b@B2{} = TinyL b
toTiny b@B3{} = TinyL b
toTiny b@B4{} = TinyH b
toTiny b@B5{} = TinyH b
{-- INLINE toTiny #-}

popL :: Level q i j -> LCons q i j
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

moveUpL :: Buffer q j k -> Buffer (Pair q) i j -> HPair (Buffer q) (Buffer (Pair q)) i k
moveUpL b1 b2 = case popB b2 of H p b2' -> injectB2 b1 p `H` b2'
{-- INLINE moveUpL #-}

moveDownL :: Buffer q j k -> Buffer (Pair q) i j -> HPair (Buffer q) (Buffer (Pair q)) i k
moveDownL b1 b2 = case ejectB2 b1 of H b1' p -> b1' `H` pushB p b2
{-- INLINE moveDownL #-}

moveDownR :: Buffer (Pair q) j k -> Buffer q i j -> HPair (Buffer (Pair q)) (Buffer q) i k
moveDownR b1 b2 = case popB2 b2 of H p b2' -> injectB b1 p `H` b2'
{-- INLINE moveDownR #-}

moveUpR :: Buffer (Pair q) j k -> Buffer q i j -> HPair (Buffer (Pair q)) (Buffer q) i k
moveUpR b1 b2 = case ejectB b1 of H b1' p -> b1' `H` pushB2 p b2
{-- INLINE moveUpR #-}

fixup :: Yellows q r i j k l -> Level r j k -> Deque q i l
fixup y z = implant y (fixup' z)
{-- INLINE fixup #-}

fixup' :: Level q i j -> Level q i j
fixup' (popL -> LGY f1 (popL -> LGY f2 ls)) = case (f1, f2) of
  (RX b1 b2, YX b3 b4) -> case b1 of
    B0{} -> case overUnder b2 of
      Under b2' -> let l = moveUpL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveUpL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveUpL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    B5{} -> case overUnder b2 of
      Under b2' -> let l = moveDownL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveDownL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveDownL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
  (RX b1 b2, GY b3 b4) -> case b1 of
    B0{} -> case overUnder b2 of
      Under b2' -> let l = moveUpL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveUpL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveUpL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    B5{} -> case overUnder b2 of
      Under b2' -> let l = moveDownL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveDownL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveDownL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
  (RX b1 b2, GG b3 b4) -> case b1 of
    B0{} -> case overUnder b2 of
      Under b2' -> let l = moveUpL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveUpL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveUpL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    B5{} -> case overUnder b2 of
      Under b2' -> let l = moveDownL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveDownL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveDownL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
  (XR b1 b2, YX b3 b4) -> case overUnder b1 of
    Under b1' -> case b2 of
      B0{} -> let l = moveUpL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      B5{} -> let l = moveUpL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    Okay b1' -> case b2 of
      B0{} -> let r = moveUpR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
      B5{} -> let r = moveDownR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
    Over b1' -> case b2 of
      B0{} -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      B5{} -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
  (XR b1 b2, GY b3 b4) -> case overUnder b1 of
    Under b1' -> case b2 of
      B0{} -> let l = moveUpL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      B5{} -> let l = moveUpL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    Okay b1' -> case b2 of
      B0{} -> let r = moveUpR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
      B5{} -> let r = moveDownR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
    Over b1' -> case b2 of
      B0{} -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      B5{} -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
  (XR b1 b2, GG b3 b4) -> case overUnder b1 of
    Under b1' -> case b2 of
      B0{} -> let l = moveUpL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      B5{} -> let l = moveUpL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    Okay b1' -> case b2 of
      B0{} -> let r = moveUpR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
      B5{} -> let r = moveDownR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
    Over b1' -> case b2 of
      B0{} -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      B5{} -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
fixup' (popL -> LGY f1 (popL -> LR f2 ls)) = case (f1, f2) of
  (RX b1 b2, GG b3 b4) -> case b1 of
    B0{} -> case overUnder b2 of
      Under b2' -> let l = moveUpL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveUpL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveUpL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    B5{} -> case overUnder b2 of
      Under b2' -> let l = moveDownL b1 b3 in let r = moveUpR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      Okay b2'  -> let l = moveDownL b1 b3 in case l of H c1 c2 -> combineGG (GG c1 b2') $ combine (toFringe c2 b4) ls
      Over b2'  -> let l = moveDownL b1 b3 in let r = moveDownR b4 b2' in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
  (XR b1 b2, GG b3 b4) -> case overUnder b1 of
    Under b1' -> case b2 of
      B0{} -> let l = moveUpL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      B5{} -> let l = moveUpL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
    Okay b1' -> case b2 of
      B0{} -> let r = moveUpR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
      B5{} -> let r = moveDownR b4 b2 in case r of H c3 c4 -> combineGG (GG b1' c4) $ combine (toFringe b3 c3) ls
    Over b1' -> case b2 of
      B0{} -> let l = moveDownL b1' b3 in let r = moveUpR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
      B5{} -> let l = moveDownL b1' b3 in let r = moveDownR b4 b2 in case (l, r) of (H c1 c2, H c3 c4) -> combineGG (GG c1 c4) $ combine (toFringe c2 c3) ls
fixup' a = fixup2' a
{-- INLINE fixup' #-}

fixup2' :: Level q i j -> Level q i j
fixup2' (TinyH (B5 a b c d e))                                                                     = go5 a b c d e
fixup2' (BigR (RX B0 (B0))                       N LEmpty)                                         = LEmpty
fixup2' (BigR (RX B0 (B1 n))                     N LEmpty)                                         = go1 n
fixup2' (BigR (RX B0 (B2 n o))                   N LEmpty)                                         = go2 n o
fixup2' (BigR (RX B0 (B3 n o p))                 N LEmpty)                                         = go3 n o p
fixup2' (BigR (RX B0 (B4 n o p q))               N LEmpty)                                         = go4 n o p q
fixup2' (BigR (RX B0 (B5 n o p q r))             N LEmpty)                                         = go5 n o p q r
fixup2' (BigR (RX (B5 a b c d e) (B0))           N LEmpty)                                         = go5 a b c d e
fixup2' (BigR (RX (B5 a b c d e) (B1 n))         N LEmpty)                                         = go6 a b c d e n
fixup2' (BigR (RX (B5 a b c d e) (B2 n o))       N LEmpty)                                         = go7 a b c d e n o
fixup2' (BigR (RX (B5 a b c d e) (B3 n o p))     N LEmpty)                                         = go8 a b c d e n o p
fixup2' (BigR (RX (B5 a b c d e) (B4 n o p q))   N LEmpty)                                         = go9 a b c d e n o p q
fixup2' (BigR (RX (B5 a b c d e) (B5 n o p q r)) N LEmpty)                                         = go10 a b c d e n o p q r
fixup2' (BigR (XR (B1 a) (B0))                   N LEmpty)                                         = go1 a
fixup2' (BigR (XR (B1 a) (B5 n o p q r))         N LEmpty)                                         = go6 a n o p q r
fixup2' (BigR (XR (B2 a b) (B0))                 N LEmpty)                                         = go2 a b
fixup2' (BigR (XR (B2 a b) (B5 n o p q r))       N LEmpty)                                         = go7 a b n o p q r
fixup2' (BigR (XR (B3 a b c) (B0))               N LEmpty)                                         = go3 a b c
fixup2' (BigR (XR (B3 a b c) (B5 n o p q r))     N LEmpty)                                         = go8 a b c n o p q r
fixup2' (BigR (XR (B4 a b c d) (B0))             N LEmpty)                                         = go4 a b c d
fixup2' (BigR (XR (B4 a b c d) (B5 n o p q r))   N LEmpty)                                         = go9 a b c d n o p q r
fixup2' (BigR (RX B0 (B0))                       (Y1 (B1 (P s t))) LEmpty)                         = go2 s t
fixup2' (BigR (RX B0 (B1 n))                     (Y1 (B1 (P s t))) LEmpty)                         = go3 s t n
fixup2' (BigR (RX B0 (B2 n o))                   (Y1 (B1 (P s t))) LEmpty)                         = go4 s t n o
fixup2' (BigR (RX B0 (B3 n o p))                 (Y1 (B1 (P s t))) LEmpty)                         = go5 s t n o p
fixup2' (BigR (RX B0 (B4 n o p q))               (Y1 (B1 (P s t))) LEmpty)                         = go6 s t n o p q
fixup2' (BigR (RX B0 (B5 n o p q r))             (Y1 (B1 (P s t))) LEmpty)                         = go7 s t n o p q r
fixup2' (BigR (RX (B5 a b c d e) (B0))           (Y1 (B1 (P s t))) LEmpty)                         = go7 a b c d e s t
fixup2' (BigR (RX (B5 a b c d e) (B1 n))         (Y1 (B1 (P s t))) LEmpty)                         = go8 a b c d e s t n
fixup2' (BigR (RX (B5 a b c d e) (B2 n o))       (Y1 (B1 (P s t))) LEmpty)                         = go9 a b c d e s t n o
fixup2' (BigR (RX (B5 a b c d e) (B3 n o p))     (Y1 (B1 (P s t))) LEmpty)                         = go10 a b c d e s t n o p
fixup2' (BigR (RX (B5 a b c d e) (B4 n o p q))   (Y1 (B1 (P s t))) LEmpty)                         = go11 a b c d e s t n o p q
fixup2' (BigR (RX (B5 a b c d e) (B5 n o p q r)) (Y1 (B1 (P s t))) LEmpty)                         = go12 a b c d e s t n o p q r
fixup2' (BigR (XR (B1 a) (B0))                   (Y1 (B1 (P s t))) LEmpty)                         = go3 a s t
fixup2' (BigR (XR (B1 a) (B5 n o p q r))         (Y1 (B1 (P s t))) LEmpty)                         = go8 a s t n o p q r
fixup2' (BigR (XR (B2 a b) (B0))                 (Y1 (B1 (P s t))) LEmpty)                         = go4 a b s t
fixup2' (BigR (XR (B2 a b) (B5 n o p q r))       (Y1 (B1 (P s t))) LEmpty)                         = go9 a b s t n o p q r
fixup2' (BigR (XR (B3 a b c) (B0))               (Y1 (B1 (P s t))) LEmpty)                         = go5 a b c s t
fixup2' (BigR (XR (B3 a b c) (B5 n o p q r))     (Y1 (B1 (P s t))) LEmpty)                         = go10 a b c s t n o p q r
fixup2' (BigR (XR (B4 a b c d) (B0))             (Y1 (B1 (P s t))) LEmpty)                         = go6 a b c d s t
fixup2' (BigR (XR (B4 a b c d) (B5 n o p q r))   (Y1 (B1 (P s t))) LEmpty)                         = go11 a b c d s t n o p q r
fixup2' (BigR (RX B0 (B0))                       (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go8 s t u v w x y z
fixup2' (BigR (RX B0 (B1 n))                     (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go9 s t u v w x y z n
fixup2' (BigR (RX B0 (B2 n o))                   (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go10 s t u v w x y z n o
fixup2' (BigR (RX B0 (B3 n o p))                 (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go11 s t u v w x y z n o p
fixup2' (BigR (RX B0 (B4 n o p q))               (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go12 s t u v w x y z n o p q
fixup2' (BigR (RX B0 (B5 n o p q r))             (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go13 s t u v w x y z n o p q r
fixup2' (BigR (RX (B5 a b c d e) (B0))           (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go13 a b c d e s t u v w x y z
fixup2' (BigR (RX (B5 a b c d e) (B1 n))         (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go14 a b c d e s t u v w x y z n
fixup2' (BigR (RX (B5 a b c d e) (B2 n o))       (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go15 a b c d e s t u v w x y z n o
fixup2' (BigR (RX (B5 a b c d e) (B3 n o p))     (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go16 a b c d e s t u v w x y z n o p
fixup2' (BigR (RX (B5 a b c d e) (B4 n o p q))   (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go17 a b c d e s t u v w x y z n o p q
fixup2' (BigR (RX (B5 a b c d e) (B5 n o p q r)) (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go18 a b c d e s t u v w x y z n o p q r
fixup2' (BigR (XR (B1 a) (B0))                   (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go9 a s t u v w x y z
fixup2' (BigR (XR (B1 a) (B5 n o p q r))         (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go14 a s t u v w x y z n o p q r
fixup2' (BigR (XR (B2 a b) (B0))                 (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go10 a b s t u v w x y z
fixup2' (BigR (XR (B2 a b) (B5 n o p q r))       (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go15 a b s t u v w x y z n o p q r
fixup2' (BigR (XR (B3 a b c) (B0))               (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go11 a b c s t u v w x y z
fixup2' (BigR (XR (B3 a b c) (B5 n o p q r))     (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go16 a b c s t u v w x y z n o p q r
fixup2' (BigR (XR (B4 a b c d) (B0))             (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go12 a b c d s t u v w x y z
fixup2' (BigR (XR (B4 a b c d) (B5 n o p q r))   (Y1 (B4 (P s t) (P u v) (P w x) (P y z))) LEmpty) = go17 a b c d s t u v w x y z n o p q r
fixup2' (BigR (RX B0 (B0))                       N (TinyL B0))                           = LEmpty
fixup2' (BigR (RX B0 (B1 n))                     N (TinyL B0))                           = go1 n
fixup2' (BigR (RX B0 (B2 n o))                   N (TinyL B0))                           = go2 n o
fixup2' (BigR (RX B0 (B3 n o p))                 N (TinyL B0))                           = go3 n o p
fixup2' (BigR (RX B0 (B4 n o p q))               N (TinyL B0))                           = go4 n o p q
fixup2' (BigR (RX B0 (B5 n o p q r))             N (TinyL B0))                           = go5 n o p q r
fixup2' (BigR (RX (B5 a b c d e) (B0))           N (TinyL B0))                           = go5 a b c d e
fixup2' (BigR (RX (B5 a b c d e) (B1 n))         N (TinyL B0))                           = go6 a b c d e n
fixup2' (BigR (RX (B5 a b c d e) (B2 n o))       N (TinyL B0))                           = go7 a b c d e n o
fixup2' (BigR (RX (B5 a b c d e) (B3 n o p))     N (TinyL B0))                           = go8 a b c d e n o p
fixup2' (BigR (RX (B5 a b c d e) (B4 n o p q))   N (TinyL B0))                           = go9 a b c d e n o p q
fixup2' (BigR (RX (B5 a b c d e) (B5 n o p q r)) N (TinyL B0))                           = go10 a b c d e n o p q r
fixup2' (BigR (XR (B1 a) (B0))                   N (TinyL B0))                           = go1 a
fixup2' (BigR (XR (B1 a) (B5 n o p q r))         N (TinyL B0))                           = go6 a n o p q r
fixup2' (BigR (XR (B2 a b) (B0))                 N (TinyL B0))                           = go2 a b
fixup2' (BigR (XR (B2 a b) (B5 n o p q r))       N (TinyL B0))                           = go7 a b n o p q r
fixup2' (BigR (XR (B3 a b c) (B0))               N (TinyL B0))                           = go3 a b c
fixup2' (BigR (XR (B3 a b c) (B5 n o p q r))     N (TinyL B0))                           = go8 a b c n o p q r
fixup2' (BigR (XR (B4 a b c d) (B0))             N (TinyL B0))                           = go4 a b c d
fixup2' (BigR (XR (B4 a b c d) (B5 n o p q r))   N (TinyL B0))                           = go9 a b c d n o p q r
fixup2' (BigR (RX B0 (B0))                       N (TinyL (B1 (P s t))))                           = go2 s t
fixup2' (BigR (RX B0 (B1 n))                     N (TinyL (B1 (P s t))))                           = go3 s t n
fixup2' (BigR (RX B0 (B2 n o))                   N (TinyL (B1 (P s t))))                           = go4 s t n o
fixup2' (BigR (RX B0 (B3 n o p))                 N (TinyL (B1 (P s t))))                           = go5 s t n o p
fixup2' (BigR (RX B0 (B4 n o p q))               N (TinyL (B1 (P s t))))                           = go6 s t n o p q
fixup2' (BigR (RX B0 (B5 n o p q r))             N (TinyL (B1 (P s t))))                           = go7 s t n o p q r
fixup2' (BigR (RX (B5 a b c d e) (B0))           N (TinyL (B1 (P s t))))                           = go7 a b c d e s t
fixup2' (BigR (RX (B5 a b c d e) (B1 n))         N (TinyL (B1 (P s t))))                           = go8 a b c d e s t n
fixup2' (BigR (RX (B5 a b c d e) (B2 n o))       N (TinyL (B1 (P s t))))                           = go9 a b c d e s t n o
fixup2' (BigR (RX (B5 a b c d e) (B3 n o p))     N (TinyL (B1 (P s t))))                           = go10 a b c d e s t n o p
fixup2' (BigR (RX (B5 a b c d e) (B4 n o p q))   N (TinyL (B1 (P s t))))                           = go11 a b c d e s t n o p q
fixup2' (BigR (RX (B5 a b c d e) (B5 n o p q r)) N (TinyL (B1 (P s t))))                           = go12 a b c d e s t n o p q r
fixup2' (BigR (XR (B1 a) (B0))                   N (TinyL (B1 (P s t))))                           = go3 a s t
fixup2' (BigR (XR (B1 a) (B5 n o p q r))         N (TinyL (B1 (P s t))))                           = go8 a s t n o p q r
fixup2' (BigR (XR (B2 a b) (B0))                 N (TinyL (B1 (P s t))))                           = go4 a b s t
fixup2' (BigR (XR (B2 a b) (B5 n o p q r))       N (TinyL (B1 (P s t))))                           = go9 a b s t n o p q r
fixup2' (BigR (XR (B3 a b c) (B0))               N (TinyL (B1 (P s t))))                           = go5 a b c s t
fixup2' (BigR (XR (B3 a b c) (B5 n o p q r))     N (TinyL (B1 (P s t))))                           = go10 a b c s t n o p q r
fixup2' (BigR (XR (B4 a b c d) (B0))             N (TinyL (B1 (P s t))))                           = go6 a b c d s t
fixup2' (BigR (XR (B4 a b c d) (B5 n o p q r))   N (TinyL (B1 (P s t))))                           = go11 a b c d s t n o p q r
fixup2' (BigR (RX B0 (B0))                       N (TinyL (B2 (P s t) (P u v))))                   = go4 s t u v
fixup2' (BigR (RX B0 (B1 n))                     N (TinyL (B2 (P s t) (P u v))))                   = go5 s t u v n
fixup2' (BigR (RX B0 (B2 n o))                   N (TinyL (B2 (P s t) (P u v))))                   = go6 s t u v n o
fixup2' (BigR (RX B0 (B3 n o p))                 N (TinyL (B2 (P s t) (P u v))))                   = go7 s t u v n o p
fixup2' (BigR (RX B0 (B4 n o p q))               N (TinyL (B2 (P s t) (P u v))))                   = go8 s t u v n o p q
fixup2' (BigR (RX B0 (B5 n o p q r))             N (TinyL (B2 (P s t) (P u v))))                   = go9 s t u v n o p q r
fixup2' (BigR (RX (B5 a b c d e) (B0))           N (TinyL (B2 (P s t) (P u v))))                   = go9 a b c d e s t u v
fixup2' (BigR (RX (B5 a b c d e) (B1 n))         N (TinyL (B2 (P s t) (P u v))))                   = go10 a b c d e s t u v n
fixup2' (BigR (RX (B5 a b c d e) (B2 n o))       N (TinyL (B2 (P s t) (P u v))))                   = go11 a b c d e s t u v n o
fixup2' (BigR (RX (B5 a b c d e) (B3 n o p))     N (TinyL (B2 (P s t) (P u v))))                   = go12 a b c d e s t u v n o p
fixup2' (BigR (RX (B5 a b c d e) (B4 n o p q))   N (TinyL (B2 (P s t) (P u v))))                   = go13 a b c d e s t u v n o p q
fixup2' (BigR (RX (B5 a b c d e) (B5 n o p q r)) N (TinyL (B2 (P s t) (P u v))))                   = go14 a b c d e s t u v n o p q r
fixup2' (BigR (XR (B1 a) (B0))                   N (TinyL (B2 (P s t) (P u v))))                   = go5 a s t u v
fixup2' (BigR (XR (B1 a) (B5 n o p q r))         N (TinyL (B2 (P s t) (P u v))))                   = go10 a s t u v n o p q r
fixup2' (BigR (XR (B2 a b) (B0))                 N (TinyL (B2 (P s t) (P u v))))                   = go6 a b s t u v
fixup2' (BigR (XR (B2 a b) (B5 n o p q r))       N (TinyL (B2 (P s t) (P u v))))                   = go11 a b s t u v n o p q r
fixup2' (BigR (XR (B3 a b c) (B0))               N (TinyL (B2 (P s t) (P u v))))                   = go7 a b c s t u v
fixup2' (BigR (XR (B3 a b c) (B5 n o p q r))     N (TinyL (B2 (P s t) (P u v))))                   = go12 a b c s t u v n o p q r
fixup2' (BigR (XR (B4 a b c d) (B0))             N (TinyL (B2 (P s t) (P u v))))                   = go8 a b c d s t u v
fixup2' (BigR (XR (B4 a b c d) (B5 n o p q r))   N (TinyL (B2 (P s t) (P u v))))                   = go13 a b c d s t u v n o p q r
fixup2' (BigR (RX B0 (B0))                       N (TinyL (B3 (P s t) (P u v) (P w x))))           = go6 s t u v w x
fixup2' (BigR (RX B0 (B1 n))                     N (TinyL (B3 (P s t) (P u v) (P w x))))           = go7 s t u v w x n
fixup2' (BigR (RX B0 (B2 n o))                   N (TinyL (B3 (P s t) (P u v) (P w x))))           = go8 s t u v w x n o
fixup2' (BigR (RX B0 (B3 n o p))                 N (TinyL (B3 (P s t) (P u v) (P w x))))           = go9 s t u v w x n o p
fixup2' (BigR (RX B0 (B4 n o p q))               N (TinyL (B3 (P s t) (P u v) (P w x))))           = go10 s t u v w x n o p q
fixup2' (BigR (RX B0 (B5 n o p q r))             N (TinyL (B3 (P s t) (P u v) (P w x))))           = go11 s t u v w x n o p q r
fixup2' (BigR (RX (B5 a b c d e) (B0))           N (TinyL (B3 (P s t) (P u v) (P w x))))           = go11 a b c d e s t u v w x
fixup2' (BigR (RX (B5 a b c d e) (B1 n))         N (TinyL (B3 (P s t) (P u v) (P w x))))           = go12 a b c d e s t u v w x n
fixup2' (BigR (RX (B5 a b c d e) (B2 n o))       N (TinyL (B3 (P s t) (P u v) (P w x))))           = go13 a b c d e s t u v w x n o
fixup2' (BigR (RX (B5 a b c d e) (B3 n o p))     N (TinyL (B3 (P s t) (P u v) (P w x))))           = go14 a b c d e s t u v w x n o p
fixup2' (BigR (RX (B5 a b c d e) (B4 n o p q))   N (TinyL (B3 (P s t) (P u v) (P w x))))           = go15 a b c d e s t u v w x n o p q
fixup2' (BigR (RX (B5 a b c d e) (B5 n o p q r)) N (TinyL (B3 (P s t) (P u v) (P w x))))           = go16 a b c d e s t u v w x n o p q r
fixup2' (BigR (XR (B1 a) (B0))                   N (TinyL (B3 (P s t) (P u v) (P w x))))           = go7 a s t u v w x
fixup2' (BigR (XR (B1 a) (B5 n o p q r))         N (TinyL (B3 (P s t) (P u v) (P w x))))           = go12 a s t u v w x n o p q r
fixup2' (BigR (XR (B2 a b) (B0))                 N (TinyL (B3 (P s t) (P u v) (P w x))))           = go8 a b s t u v w x
fixup2' (BigR (XR (B2 a b) (B5 n o p q r))       N (TinyL (B3 (P s t) (P u v) (P w x))))           = go13 a b s t u v w x n o p q r
fixup2' (BigR (XR (B3 a b c) (B0))               N (TinyL (B3 (P s t) (P u v) (P w x))))           = go9 a b c s t u v w x
fixup2' (BigR (XR (B3 a b c) (B5 n o p q r))     N (TinyL (B3 (P s t) (P u v) (P w x))))           = go14 a b c s t u v w x n o p q r
fixup2' (BigR (XR (B4 a b c d) (B0))             N (TinyL (B3 (P s t) (P u v) (P w x))))           = go10 a b c d s t u v w x
fixup2' (BigR (XR (B4 a b c d) (B5 n o p q r))   N (TinyL (B3 (P s t) (P u v) (P w x))))           = go15 a b c d s t u v w x n o p q r
{-# NOINLINE fixup2' #-}

go1 :: q a b -> Level q a b
go1 a = TinyL (B1 a)
go2 :: q b c -> q a b -> Level q a c
go2 a b                                              = TinyL (B2 a b)
go3 :: q c d -> q b c -> q a b -> Level q a d
go3 a b c                                            = TinyL (B3 a b c)
go4 :: q d e -> q c d -> q b c -> q a b -> Level q a e
go4 a b c d                                          = BigG (GG (B2 a b) (B2 c d)) N LEmpty
go5 :: q e f -> q d e -> q c d -> q b c -> q a b -> Level q a f
go5 a b c d e                                        = BigG (GG (B2 a b) (B3 c d e)) N LEmpty
go6 :: q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level q a g
go6 a b c d e f                                      = BigG (GG (B3 a b c) (B3 d e f)) N LEmpty
go7 :: q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level q a h
go7 a b c d e f g                                    = BigG (GG (B3 a b c) (B2 f g)) (Y1 (B1 (P d e))) LEmpty
go8 :: q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level q a i
go8 a b c d e f g h                                  = BigG (GG (B3 a b c) (B3 f g h)) (Y1 (B1 (P d e))) LEmpty
go9 :: q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level q a j
go9 a b c d e f g h i                                = BigG (GG (B3 a b c) (B2 h i)) (Y (YX (B1 (P d e)) (B1 (P f g))) N) LEmpty
go10 :: q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level q a k
go10 a b c d e f g h i j                             = BigG (GG (B3 a b c) (B3 h i j)) (Y (YX (B1 (P d e)) (B1 (P f g))) N) LEmpty
go11 :: q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level q a l
go11 a b c d e f g h i j k                           = BigG (GG (B3 a b c) (B2 j k)) (Y (YX (B1 (P d e)) (B2 (P f g) (P h i))) N) LEmpty
go12 :: q l m -> q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level q a m
go12 a b c d e f g h i j k l                         = BigG (GG (B3 a b c) (B3 j k l)) (Y (YX (B1 (P d e)) (B2 (P f g) (P h i))) N) LEmpty
go13 :: q m n -> q l m -> q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level q a n
go13 a b c d e f g h i j k l m                       = BigG (GG (B3 a b c) (B2 l m)) (Y (YX (B1 (P d e)) (B3 (P f g) (P h i) (P j k))) N) LEmpty
go14 :: q n o -> q m n -> q l m -> q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level q a o
go14 a b c d e f g h i j k l m n                     = BigG (GG (B3 a b c) (B3 l m n)) (Y (YX (B1 (P d e)) (B3 (P f g) (P h i) (P j k))) N) LEmpty
go15 :: q o p -> q n o -> q m n -> q l m -> q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level q a p
go15 a b c d e f g h i j k l m n o                   = BigG (GG (B3 a b c) (B2 n o)) (Y (YX (B1 (P d e)) (B4 (P f g) (P h i) (P j k) (P l m))) N) LEmpty
go16 :: q p r -> q o p -> q n o -> q m n -> q l m -> q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level q a r
go16 a b c d e f g h i j k l m n o p                 = BigG (GG (B3 a b c) (B3 n o p)) (Y (YX (B1 (P d e)) (B4 (P f g) (P h i) (P j k) (P l m))) N) LEmpty
go17 :: q r s -> q p r -> q o p -> q n o -> q m n -> q l m -> q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level q a s
go17 a b c d e f g h i j k l m n o p q               = BigG (GG (B3 a b c) (B2 p q)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B2 (P l m) (P n o))) N) LEmpty
go18 :: q s t -> q r s -> q p r -> q o p -> q n o -> q m n -> q l m -> q k l -> q j k -> q i j -> q h i -> q g h -> q f g -> q e f -> q d e -> q c d -> q b c -> q a b -> Level q a t
go18 a b c d e f g h i j k l m n o p q r             = BigG (GG (B3 a b c) (B3 p q r)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B2 (P l m) (P n o))) N) LEmpty
{-
go19 a b c d e f g h i j k l m n o p q r s           = BigG (GG (B3 a b c) (B2 r s)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B3 (P l m) (P n o) (P p q))) N) LEmpty
go20 a b c d e f g h i j k l m n o p q r s t         = BigG (GG (B3 a b c) (B3 r s t)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B3 (P l m) (P n o) (P p q))) N) LEmpty
go21 a b c d e f g h i j k l m n o p q r s t u       = BigG (GG (B3 a b c) (B2 t u)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B4 (P l m) (P n o) (P p q) (P r s))) N) LEmpty
go22 a b c d e f g h i j k l m n o p q r s t u v     = BigG (GG (B3 a b c) (B3 t u v)) (Y (YX (B4 (P d e) (P f g) (P h i) (P j k)) (B4 (P l m) (P n o) (P p q) (P r s))) N) LEmpty
-}

implant :: Yellows q r i j k l -> Level r j k -> Deque q i l
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
  a <| Deque LEmpty                                    = Deque $ TinyL (B1 a)
  a <| Deque (TinyL (B0))                              = Deque $ TinyL (B1 a)
  a <| Deque (TinyL (B1 b))                            = Deque $ TinyL (B2 a b)
  a <| Deque (TinyL (B2 b c))                          = Deque $ TinyL (B3 a b c)
  a <| Deque (TinyL (B3 b c d))                        = Deque $ TinyH (B4 a b c d)
  a <| Deque (TinyH (B4 b c d e))                      = fixup N (TinyH (B5 a b c d e))
  a <| Deque (BigY (YX (B1 b) (B1 i)) y z)             = Deque $ BigY (GY (B2 a b) (B1 i)) y z
  a <| Deque (BigY (YX (B1 b) (B2 i j)) y z)           = Deque $ BigG (GG (B2 a b) (B2 i j)) y z
  a <| Deque (BigY (YX (B1 b) (B3 i j k)) y z)         = Deque $ BigG (GG (B2 a b) (B3 i j k)) y z
  a <| Deque (BigY (YX (B1 b) (B4 i j k l)) y z)       = Deque $ BigY (GY (B2 a b) (B4 i j k l)) y z
  a <| Deque (BigY (GY (B2 b c) x) y z)                = Deque $ BigY (GY (B3 a b c) x) y z
  a <| Deque (BigG (GG (B2 b c) x) y z)                = Deque $ BigG (GG (B3 a b c) x) y z
  a <| Deque (BigY (GY (B3 b c d) x) y z)              = Deque $ BigY (YX (B4 a b c d) x) y z
  a <| Deque (BigG (GG (B3 b c d) x) y LEmpty)         = Deque $ BigY (YX (B4 a b c d) x) y LEmpty
  a <| Deque (BigG (GG (B3 b c d) x) y z@(TinyH B5{})) = Deque $ BigY (YX (B4 a b c d) x) y (fixup' z)
  a <| Deque (BigG (GG (B3 b c d) x) y z@(TinyL{}))    = Deque $ BigY (YX (B4 a b c d) x) y z
  a <| Deque (BigG (GG (B3 b c d) x) y z@(BigR{}))     = Deque $ BigY (YX (B4 a b c d) x) y (fixup' z)
  a <| Deque (BigG (GG (B3 b c d) x) y z@(BigG{}))     = Deque $ BigY (YX (B4 a b c d) x) y z
  a <| Deque (BigY (YX (B4 b c d e) x) y z)            = fixup N (BigR (RX (B5 a b c d e) x) y z)

instance Unsnoc Deque where
  unsnoc (Deque LEmpty)                                  = Empty
  unsnoc (Deque (TinyL (B0)))                            = Empty
  unsnoc (Deque (TinyL (B1 b)))                          = Deque LEmpty :| b
  unsnoc (Deque (TinyL (B2 b c)))                        = Deque (TinyL (B1 b)) :| c
  unsnoc (Deque (TinyL (B3 b c d)))                      = Deque (TinyL (B2 b c)) :| d
  unsnoc (Deque (TinyH (B4 b c d e)))                    = Deque (TinyL (B3 b c d)) :| e
  unsnoc (Deque (BigY (YX b (B1 i)) y z))                = fixup N (BigR (XR b (B0)) y z) :| i
  unsnoc (Deque (BigY (YX b (B2 i j)) y z))              = Deque (BigY (YX b (B1 i)) y z) :| j
  unsnoc (Deque (BigY (YX b (B3 i j k)) y z))            = Deque (BigY (YX b (B2 i j)) y z) :| k
  unsnoc (Deque (BigY (YX b (B4 i j k l)) y z))          = Deque (BigY (YX b (B3 i j k)) y z) :| l
  unsnoc (Deque (BigY (GY b (B1 i)) y z))                = fixup N (BigR (XR b B0) y z) :| i
  unsnoc (Deque (BigY (GY b (B4 i j k l)) y z))          = Deque (BigG (GG b (B3 i j k)) y z) :| l
  unsnoc (Deque (BigG (GG b (B2 i j)) y LEmpty))         = Deque (BigY (GY b (B1 i)) y LEmpty) :| j
  unsnoc (Deque (BigG (GG b (B2 i j)) y z@(TinyH B5{}))) = Deque (BigY (GY b (B1 i)) y (fixup' z)) :| j
  unsnoc (Deque (BigG (GG b (B2 i j)) y z@(TinyL{})))    = Deque (BigY (GY b (B1 i)) y z) :| j
  unsnoc (Deque (BigG (GG b (B2 i j)) y z@(BigR{})))     = Deque (BigY (GY b (B1 i)) y (fixup' z)) :| j
  unsnoc (Deque (BigG (GG b (B2 i j)) y z@(BigG{})))     = Deque (BigY (GY b (B1 i)) y z) :| j
  unsnoc (Deque (BigG (GG b (B3 i j k)) y z))            = Deque (BigG (GG b (B2 i j)) y z) :| k

instance Uncons Deque where
  uncons (Deque LEmpty)                                    = Empty
  uncons (Deque (TinyL (B0)))                              = Empty
  uncons (Deque (TinyL (B1 b)))                            = b :| Deque LEmpty
  uncons (Deque (TinyL (B2 b c)))                          = b :| Deque (TinyL (B1 c))
  uncons (Deque (TinyL (B3 b c d)))                        = b :| Deque (TinyL (B2 c d))
  uncons (Deque (TinyH (B4 b c d e)))                      = b :| Deque (TinyL (B3 c d e))
  uncons (Deque (BigY (YX (B1 b) i) y z))                  = b :| fixup N (BigR (RX B0 i) y z)
  uncons (Deque (BigY (GY (B2 b c) (B1 i)) y z))           = b :| Deque (BigY (YX (B1 c) (B1 i)) y z)
  uncons (Deque (BigY (GY (B2 b c) (B4 i j k l)) y z))     = b :| Deque (BigY (YX (B1 c) (B4 i j k l)) y z)
  uncons (Deque (BigG (GG (B2 b c) i) y LEmpty))           = b :| Deque (BigY (YX (B1 c) i) y LEmpty)
  uncons (Deque (BigG (GG (B2 b c) i) y z@(TinyH B5{})))   = b :| Deque (BigY (YX (B1 c) i) y (fixup' z))
  uncons (Deque (BigG (GG (B2 b c) i) y z@(TinyL{})))      = b :| Deque (BigY (YX (B1 c) i) y z)
  uncons (Deque (BigG (GG (B2 b c) i) y z@(BigR{})))       = b :| Deque (BigY (YX (B1 c) i) y (fixup' z))
  uncons (Deque (BigG (GG (B2 b c) i) y z@(BigG{})))       = b :| Deque (BigY (YX (B1 c) i) y z)
  uncons (Deque (BigY (GY (B3 b c d) i) y z))              = b :| Deque (BigY (GY (B2 c d) i) y z)
  uncons (Deque (BigG (GG (B3 b c d) i) y z))              = b :| Deque (BigG (GG (B2 c d) i) y z)
  uncons (Deque (BigY (YX (B4 b c d e) (B1 i)) y z))       = b :| Deque (BigY (GY (B3 c d e) (B1 i)) y z)
  uncons (Deque (BigY (YX (B4 b c d e) (B2 i j)) y z))     = b :| Deque (BigG (GG (B3 c d e) (B2 i j)) y z)
  uncons (Deque (BigY (YX (B4 b c d e) (B3 i j k)) y z))   = b :| Deque (BigG (GG (B3 c d e) (B3 i j k)) y z)
  uncons (Deque (BigY (YX (B4 b c d e) (B4 i j k l)) y z)) = b :| Deque (BigY (GY (B3 c d e) (B4 i j k l)) y z)

instance Snoc Deque where
  Deque LEmpty                                    |> a = Deque $ TinyL (B1 a)
  Deque (TinyL (B0))                              |> a = Deque $ TinyL (B1 a)
  Deque (TinyL (B1 b))                            |> a = Deque $ TinyL (B2 b a)
  Deque (TinyL (B2 b c))                          |> a = Deque $ TinyL (B3 b c a)
  Deque (TinyL (B3 b c d))                        |> a = Deque $ TinyH (B4 b c d a)
  Deque (TinyH (B4 b c d e))                      |> a = fixup N (TinyH (B5 b c d e a))
  Deque (BigY (YX b (B1 i)) y z)                  |> a = Deque $ BigY (YX b (B2 i a)) y z
  Deque (BigY (YX b (B2 i j)) y z)                |> a = Deque $ BigY (YX b (B3 i j a)) y z
  Deque (BigY (YX b (B3 i j k)) y z)              |> a = Deque $ BigY (YX b (B4 i j k a)) y z
  Deque (BigY (YX b (B4 i j k l)) y z)            |> a = fixup N (BigR (XR b (B5 i j k l a)) y z)
  Deque (BigY (GY b (B1 i)) y z)                  |> a = Deque $ BigG (GG b (B2 i a)) y z
  Deque (BigY (GY b (B4 i j k l)) y z)            |> a = fixup N (BigR (XR b (B5 i j k l a)) y z)
  Deque (BigG (GG b (B2 i j)) y z)                |> a = Deque $ BigG (GG b (B3 i j a)) y z
  Deque (BigG (GG b (B3 i j k)) y z@LEmpty)       |> a = Deque $ BigY (GY b (B4 i j k a)) y z
  Deque (BigG (GG b (B3 i j k)) y z@(TinyH B5{})) |> a = Deque $ BigY (GY b (B4 i j k a)) y (fixup' z)
  Deque (BigG (GG b (B3 i j k)) y z@TinyL{})      |> a = Deque $ BigY (GY b (B4 i j k a)) y z
  Deque (BigG (GG b (B3 i j k)) y z@BigR{})       |> a = Deque $ BigY (GY b (B4 i j k a)) y (fixup' z)
  Deque (BigG (GG b (B3 i j k)) y z@BigG{})       |> a = Deque $ BigY (GY b (B4 i j k a)) y z
