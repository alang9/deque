{-# LANGUAGE EmptyDataDecls, GADTs, DataKinds, BangPatterns,
    MultiParamTypeClasses #-}
module Data.Deque.NonCat where

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

data Fringe c q i j k l where
  RX :: !(Buffer s F F F F t q k l) -> !(Buffer u v w x y z q i j) -> Fringe Red q i j k l
  XR :: !(Buffer F u v w x F q k l) -> !(Buffer y F F F F z q i j) -> Fringe Red q i j k l
  YX :: !(Buffer F u F F v F q k l) -> !(Buffer F w x y z F q i j) -> Fringe Yellow q i j k l
  GY :: !(Buffer F F w x F F q k l) -> !(Buffer F y F F z F q i j) -> Fringe Yellow q i j k l
  GG :: !(Buffer F F w x F F q k l) -> !(Buffer F F y z F F q i j) -> Fringe Green q i j k l

data Yellows q r i j k l where
  N :: Yellows q q i i l l
  Y :: !(Fringe Yellow q i m n l) -> !(Yellows (Pair q) r m j k n) -> Yellows q r i j k l
  Y1 :: !(Buffer F x F F y F q i j) -> Yellows q Nope i j j j

data Level r y q i j where
  Empty :: Level F F q i i
  TinyH :: !(Buffer F F F g y r q i j) -> Level r y q i j
  TinyL :: !(Buffer r y g F F F q i j) -> Level r y q i j
  BigG :: !(Fringe Green q i j m n) -> !(Yellows (Pair q) r j k l m) -> !(Level c F r k l) -> Level F F q i n
  BigY :: !(Fringe Yellow q i j m n) -> !(Yellows (Pair q) r j k l m) -> !(Level F F r k l) -> Level F T q i n
  BigR :: !(Fringe Red q i j m n) -> !(Yellows (Pair q) r j k l m) -> !(Level F F r k l) -> Level T F q i n

data Deque q i j where
  Deque :: !(Level F y q i j) -> Deque q i j

fixup :: Yellows q r i j k l -> Level T F r j k -> Deque q i l
fixup y z = implant y (fixup' z)

fixup' :: Level T F q i j -> Level F F q i j
fixup' (TinyL B0) = Empty -- probably can't happen, but it's handled

implant :: Yellows q r i j k l -> Level F F r j k -> Deque q i l
implant N Empty = Deque $ Empty
implant N (TinyL b) = Deque $ TinyL b
implant N (TinyH b) = Deque $ TinyH b
implant N (BigG b y z) = Deque $ BigG b y z
implant (Y1 b@B1{}) _ = Deque $ TinyL b -- in agda we could properly eliminate the impossible cases here :( however the thristing ensures we can't throw anything away.
implant (Y1 b@B4{}) _ = Deque $ TinyH b
implant (Y y ys) z = Deque $ BigY y ys z

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
