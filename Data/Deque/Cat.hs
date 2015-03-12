{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -Wall #-}

module Data.Deque.Cat where

import Control.DeepSeq
import Data.Type.Bool
import qualified Data.Deque.NonCat as NC

type T = True
type F = False

data Buffer k1 k2 k3 k4 k5 k6 k7 k8 k9 q i j where
  B1 :: !(q i j) -> Buffer T F F F F F F F F q i j
  B2 :: !(q j k) -> !(q i j) -> Buffer F T F F F F F F F q i k
  B3 :: !(q k l) -> !(q j k) -> !(q i j) -> Buffer F F T F F F F F F q i l
  B4 :: !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer F F F T F F F F F q i m
  B5 :: !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer F F F F T F F F F q i n
  B6 :: !(q n o) -> !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer F F F F F T F F F q i o
  B7 :: !(q o p) -> !(q n o) -> !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer F F F F F F T F F q i p
  B8 :: !(q p r) -> !(q o p) -> !(q n o) -> !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j)  -> Buffer F F F F F F F T F q i r
  B9 :: !(NC.Deque q s t) -> !(q r s) -> !(q p r) -> !(q o p) -> !(q n o) -> !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> !(NC.Deque q h i) -> Buffer F F F F F F F F T q h t

instance NFData (Buffer k1 k2 k3 k4 k5 k6 k7 k8 k9 q i j) where
  rnf !_ = ()

instance Show (Buffer k1 k2 k3 k4 k5 k6 k7 k8 k9 q i j) where
  show B1{} = "B1"
  show B2{} = "B2"
  show B3{} = "B3"
  show B4{} = "B4"
  show B5{} = "B5"
  show B6{} = "B6"
  show B7{} = "B7"
  show B8{} = "B8"
  show B9{} = "B9"

pushB :: q j k -> Buffer k1 k2 k3 k4 k5 k6 k7 k8 k9 q i j -> Buffer F k1 k2 k3 k4 k5 k6 k7 (k8 || k9) q i k
pushB a (B1 b)                         = B2 a b
pushB a (B2 b c)                       = B3 a b c
pushB a (B3 b c d)                     = B4 a b c d
pushB a (B4 b c d e)                   = B5 a b c d e
pushB a (B5 b c d e f)                 = B6 a b c d e f
pushB a (B6 b c d e f g)               = B7 a b c d e f g
pushB a (B7 b c d e f g h)             = B8 a b c d e f g h
pushB a (B8 b c d e f g h i)           = B9 NC.empty a b c d e f g h i NC.empty
pushB a (B9 ncl b c d e f g h i j ncr) = B9 (a NC.<| ncl) b c d e f g h i j ncr

injectB :: Buffer k1 k2 k3 k4 k5 k6 k7 k8 k9 q j k -> q i j -> Buffer F k1 k2 k3 k4 k5 k6 k7 (k8 || k9) q i k
injectB (B1 b)                         a = B2 b a
injectB (B2 b c)                       a = B3 b c a
injectB (B3 b c d)                     a = B4 b c d a
injectB (B4 b c d e)                   a = B5 b c d e a
injectB (B5 b c d e f)                 a = B6 b c d e f a
injectB (B6 b c d e f g)               a = B7 b c d e f g a
injectB (B7 b c d e f g h)             a = B8 b c d e f g h a
injectB (B8 b c d e f g h i)           a = B9 NC.empty b c d e f g h i a NC.empty
injectB (B9 ncl b c d e f g h i j ncr) a = B9 ncl b c d e f g h i j (ncr NC.|> a)

data HPair q r i k where
  H :: !(q j k) -> !(r i j) -> HPair q r i k

data ViewB k1 k2 k3 k4 k5 k6 k7 k8 k9 q i j where
  NoB :: ViewB T F F F F F F F F q i i
  Shift :: Buffer k2 k3 k4 k5 k6 k7 k8 k9 F q i j -> ViewB F k2 k3 k4 k5 k6 k7 k8 k9 q i j
  NoShift :: Buffer F F F F F F F F T q i j -> ViewB F F F F F F F F T q i j

popB :: Buffer k1 k2 k3 k4 k5 k6 k7 k8 k9 q i k -> HPair q (ViewB k1 k2 k3 k4 k5 k6 k7 k8 k9 q) i k
popB (B1 a)               = a `H` NoB
popB (B2 a b)             = a `H` Shift (B1 b)
popB (B3 a b c)           = a `H` Shift (B2 b c)
popB (B4 a b c d)         = a `H` Shift (B3 b c d)
popB (B5 a b c d e)       = a `H` Shift (B4 b c d e)
popB (B6 a b c d e f)     = a `H` Shift (B5 b c d e f)
popB (B7 a b c d e f g)   = a `H` Shift (B6 b c d e f g)
popB (B8 a b c d e f g h) = a `H` Shift (B7 b c d e f g h)
popB (B9 dp a b c d e f g h i ds) = case NC.uncons dp of
  p1 NC.:| rem1 -> p1 `H` NoShift (B9 rem1 a b c d e f g h i ds)
  NC.Empty -> case NC.uncons ds of
    s1 NC.:| rem1 -> a `H` NoShift (B9 NC.empty b c d e f g h i s1 rem1)
    NC.Empty -> a `H` Shift (B8 b c d e f g h i)

ejectB :: Buffer k1 k2 k3 k4 k5 k6 k7 k8 k9 q i k -> HPair (ViewB k1 k2 k3 k4 k5 k6 k7 k8 k9 q) q i k
ejectB (B1 a)               = NoB `H` a
ejectB (B2 a b)             = Shift (B1 a) `H` b
ejectB (B3 a b c)           = Shift (B2 a b) `H` c
ejectB (B4 a b c d)         = Shift (B3 a b c) `H` d
ejectB (B5 a b c d e)       = Shift (B4 a b c d) `H` e
ejectB (B6 a b c d e f)     = Shift (B5 a b c d e) `H` f
ejectB (B7 a b c d e f g)   = Shift (B6 a b c d e f) `H` g
ejectB (B8 a b c d e f g h) = Shift (B7 a b c d e f g) `H` h
ejectB (B9 dp a b c d e f g h i ds) = case NC.unsnoc ds of
  rem1 NC.:| s1 -> NoShift (B9 dp a b c d e f g h i rem1) `H` s1
  NC.Empty -> case NC.unsnoc dp of
    rem1 NC.:| s1 -> NoShift (B9 rem1 s1 a b c d e f g h NC.empty) `H` i
    NC.Empty -> Shift (B8 a b c d e f g h) `H` i

data StoredTriple q i j where
  S1 :: !(Buffer F F k3 k4 k5 k6 k7 k8 k9 q j k) -> StoredTriple q j k
  S3 :: !(Buffer F F k3 k4 k5 k6 k7 k8 k9 q l m) -> Deque (Closed lg) (Closed rg) (StoredTriple q) k l -> !(Buffer F F c3 c4 c5 c6 c7 c8 c9 q j k) -> StoredTriple q j m

instance NFData (StoredTriple q i j) where
  rnf !_ = ()

deriving instance Show (StoredTriple q i j)

data OnlyTriple ge q i j where
  O0  :: !(Buffer k1 k2 k3 k4 k5 k6 k7 k8 k9 q j k) -> OnlyTriple (Closed Green) q j k
  ORX :: !(Buffer F F F F T F F F F q l m) -> !(Deque (Closed Green) (Closed Green) (StoredTriple q) k l) -> !(Buffer F F F F c5 c6 c7 c8 c9 q j k) -> OnlyTriple (Closed Red) q j m
  OXR :: !(Buffer F F F F F k6 k7 k8 k9 q l m) -> !(Deque (Closed Green) (Closed Green) (StoredTriple q) k l) -> !(Buffer F F F F T F F F F q j k) -> OnlyTriple (Closed Red) q j m
  OOX :: !(Buffer F F F F F T F F F q l m) -> !(Deque (Closed Green) (Open r s t u) (StoredTriple q) k l) -> !(Buffer F F F F F c6 c7 c8 c9 q j k) -> OnlyTriple (Open r s t u) q j m
  OXO :: !(Buffer F F F F F F k7 k8 k9 q l m) -> !(Deque (Closed Green) (Open r s t u) (StoredTriple q) k l) -> !(Buffer F F F F F T F F F q j k) -> OnlyTriple (Open r s t u) q j m
  OYX :: !(Buffer F F F F F F T F F q l m) -> !(Deque (Open r s t u) (Closed kr) (StoredTriple q) k l) -> !(Buffer F F F F F F c7 c8 c9 q j k) -> OnlyTriple (Open r s t u) q j m
  OGY :: !(Buffer F F F F F F F k8 k9 q l m) -> !(Deque (Open r s t u) (Closed kr) (StoredTriple q) k l) -> !(Buffer F F F F F F T F F q j k) -> OnlyTriple (Open r s t u) q j m
  OGG :: !(Buffer F F F F F F F k8 k9 q l m) -> !(Deque (Closed k1) (Closed k2) (StoredTriple q) k l) -> !(Buffer F F F F F F F c8 c9 q j k) -> OnlyTriple (Closed Green) q j m

instance NFData (OnlyTriple ge q i j) where
  rnf !_ = ()

deriving instance Show (OnlyTriple ge q i j)

data LeftTriple ge q i j where
  L0 :: !(Buffer F F F F k5 k6 k7 k8 k9 q k l) -> !(Buffer F T F F F F F F F q j k) -> LeftTriple (Closed Green) q j l
  LR :: !(Buffer F F F F T F F F F q l m) -> !(Deque (Closed Green) (Closed Green) (StoredTriple q) k l) -> !(Buffer F T F F F F F F F q j k) -> LeftTriple (Closed Red) q j m
  LO :: !(Buffer F F F F F T F F F q l m) -> !(Deque (Closed Green) (Open r s t u) (StoredTriple q) k l) -> !(Buffer F T F F F F F F F q j k) -> LeftTriple (Open r s t u) q j m
  LY :: !(Buffer F F F F F F T F F q l m) -> !(Deque (Open r s t u) (Closed cr) (StoredTriple q) k l) -> !(Buffer F T F F F F F F F q j k) -> LeftTriple (Open r s t u) q j m
  LG :: !(Buffer F F F F F F F c8 c9 q l m) -> !(Deque (Closed cl) (Closed cr) (StoredTriple q) k l) -> !(Buffer F T F F F F F F F q j k) -> LeftTriple (Closed Green) q j m

instance NFData (LeftTriple ge q i j) where
  rnf !_ = ()

deriving instance Show (LeftTriple ge q i j)

data Cap (r :: Genus * -> (* -> * -> *) -> * -> * -> *) (s :: Genus *) (t :: * -> * -> *) u b where
  Opening :: Cap r (Open r s t u) s t u
  Triple :: !(r g q i j) -> Cap r g q i j
  Cap :: !(r (Open r' q' s t) q i j) -> !(r' (Closed k) q' s t) -> Cap r (Closed k) q i j

instance Show (Cap r s t u b) where
  show Opening = "Opening"
  show (Triple _) = "Triple"
  show (Cap _ _) = "Cap"

data Nope (a :: Genus *) (b :: * -> * -> *) c d

data Colour = Red | Green

data Dir = Le | Ri

data Genus k where
  Open :: (Genus k -> (k -> k -> k) -> k -> k -> k) -> (k -> k -> k) -> k -> k -> Genus k
  Closed :: Colour -> Genus k

data RightTriple (ge :: Genus *) (q :: * -> * -> *) i j where
  R0 :: !(Buffer F T F F F F F F F q k l) -> !(Buffer F F F F k5 k6 k7 k8 k9 q j k) -> RightTriple (Closed Green) q j l
  RR :: !(Buffer F T F F F F F F F q l m) -> !(Deque (Closed Green) (Closed Green) (StoredTriple q) k l) -> !(Buffer F F F F T F F F F q j k) -> RightTriple (Closed Red) q j m
  RO :: !(Buffer F T F F F F F F F q l m) -> !(Deque (Closed Green) (Open r s t u) (StoredTriple q) k l) -> !(Buffer F F F F F T F F F q j k) -> RightTriple (Open r s t u) q j m
  RY :: !(Buffer F T F F F F F F F q l m) -> !(Deque (Open r s t u) (Closed kr) (StoredTriple q) k l) -> !(Buffer F F F F F F T F F q j k) -> RightTriple (Open r s t u) q j m
  RG :: !(Buffer F T F F F F F F F q l m) -> !(Deque (Closed kl) (Closed kr) (StoredTriple q) k l) -> !(Buffer F F F F F F F c8 c9 q j k) -> RightTriple (Closed Green) q j m

instance NFData (RightTriple ge q i j) where
  rnf !_ = ()

deriving instance Show (RightTriple ge q i j)

data Deque lg rg q i j where
  D0 :: Deque (Closed Green) (Closed Green) q i i
  D2 :: !(Cap LeftTriple lg q j k) -> !(Cap RightTriple rg q i j) -> Deque lg rg q i k
  DOL :: !(Cap OnlyTriple b q i j) -> Deque b (Closed Green) q i j
  DOR :: !(Cap OnlyTriple b q i j) -> Deque (Closed Green) b q i j

instance NFData (Deque lg rg q i j) where
  rnf !_ = ()

deriving instance Show (Deque lg rg q i j)

cap :: Cap r (Open r' s t u) q i j -> r' (Closed k) s t u -> Cap r (Closed k) q i j
cap Opening t = Triple t
cap (Triple c) t = Cap c t

singleton :: q i j -> Deque (Closed Green) (Closed Green) q i j
singleton a = DOL (Triple (O0 (B1 a)))

plugL :: r (Closed k) s t u -> Deque (Open r s t u) rg q i j -> Deque (Closed k) rg q i j
plugL c (D2 l r) = D2 (cap l c) r
plugL c (DOL ot) = DOL (cap ot c)

plugR :: Deque lg (Open r s t u) q i j -> r (Closed k) s t u -> Deque lg (Closed k) q i j
plugR (D2 l rt) c = D2 l (cap rt c)
plugR (DOR ot) c = DOR (cap ot c)

data ViewCap r k q i j where
  ViewCap :: Cap r (Open r' s t u) q i j -> r' (Closed k) s t u -> ViewCap r k q i j

uncap :: Cap r (Closed k) q i j -> ViewCap r k q i j
uncap (Triple c) = ViewCap Opening c
uncap (Cap o c) = ViewCap (Triple o) c

push :: q j k -> Deque (Closed Green) (Closed Green) q i j -> Deque (Closed Green) (Closed Green) q i k
push a D0       = DOL (Triple (O0 (B1 a)))
push a (D2 l r) = D2 (pushLeftG a l) r
push a (DOL o)  = DOL (pushOnlyG a o)
push a (DOR o)  = DOR (pushOnlyG a o)

pushWith :: q j k -> Deque (Closed kl) (Closed kr) q i j -> ((forall cl cr. Deque (Closed cl) (Closed cr) q i k -> g) -> g)
pushWith a D0       = \f -> f $ DOL (Triple (O0 (B1 a)))
pushWith a (D2 l r) = \f -> pushLeft a l (\l' -> f $ D2 l' r)
pushWith a (DOL o)  = \f -> pushOnly a o (\o' -> f $ DOL o')
pushWith a (DOR o)  = \f -> pushOnly a o (\o' -> f $ DOR o')

inject :: Deque (Closed Green) (Closed Green) q j k -> q i j -> Deque (Closed Green) (Closed Green) q i k
inject D0       a = DOL (Triple (O0 (B1 a)))
inject (D2 l r) a = D2 l (injectRightG r a)
inject (DOL o)  a = DOL (injectOnlyG o a)
inject (DOR o)  a = DOR (injectOnlyG o a)

injectWith :: Deque (Closed kl) (Closed kr) q j k -> q i j -> ((forall cl cr. Deque (Closed cl) (Closed cr) q i k -> g) -> g)
injectWith D0       a = \f -> f $ DOL (Triple (O0 (B1 a)))
injectWith (D2 l r) a = \f -> injectRight r a (\r' -> f $ D2 l r')
injectWith (DOL o)  a = \f -> injectOnly o a (\o' -> f $ DOL o')
injectWith (DOR o)  a = \f -> injectOnly o a (\o' -> f $ DOR o')

injectRight :: Cap RightTriple (Closed cl) q j k -> q i j -> ((forall cr. Cap RightTriple (Closed cr) q i k -> g) -> g)
injectRight (Triple (R0 bl br))              a      = \f -> f $ Triple (R0 bl (injectB br a))
injectRight (Cap (RO bl (D2 lt rt) br) cap1) a      = \f -> f $ case uncap lt of ViewCap lt2 cap2 -> Cap (RY bl (D2 lt2 (cap rt cap1)) (injectB br a)) cap2
injectRight (Cap (RO bl (DOR ot) br) cap1)   a      = \f -> f $ Cap (RY bl (DOL ot) (injectB br a)) cap1
injectRight (Cap (RY bl (D2 lt rt) br) cap1) a      = \f -> f $ Triple (RG bl (D2 (cap lt cap1) rt) (injectB br a))
injectRight (Cap (RY bl (DOL ot) br) cap1)   a      = \f -> f $ Triple (RG bl (DOL (cap ot cap1)) (injectB br a))
injectRight (Triple (RG bl d br))            a      = \f -> f $ Triple (RG bl d (injectB br a))
injectRight (Triple (RR bl (D2 lt rt) br))   a      = \f -> f $ case uncap rt of ViewCap rt2 cap2 -> Cap (RO bl (D2 lt rt2) (injectB br a)) cap2
injectRight (Triple (RR bl (DOL ot) br))     a      = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (RO bl (DOR ot2) (injectB br a)) cap2
injectRight (Triple (RR bl (DOR ot) br))     a      = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (RO bl (DOR ot2) (injectB br a)) cap2
injectRight (Triple (RR bl D0 br))           a      = \f -> f $ Triple (R0 bl (injectB br a))

injectRightG :: Cap RightTriple (Closed Green) q j k -> q i j -> Cap RightTriple (Closed Green) q i k
injectRightG (Triple (R0 bl br))              a      = Triple (R0 bl (injectB br a))
injectRightG (Cap (RO bl (D2 lt rt) br) cap1) a      = case uncap lt of ViewCap lt2 cap2 -> Cap (RY bl (D2 lt2 (cap rt cap1)) (injectB br a)) cap2
injectRightG (Cap (RO bl (DOR ot) br) cap1)   a      = Cap (RY bl (DOL ot) (injectB br a)) cap1
injectRightG (Cap (RY bl (D2 lt rt) br) cap1) a      = Triple (RG bl (D2 (cap lt cap1) rt) (injectB br a))
injectRightG (Cap (RY bl (DOL ot) br) cap1)   a      = Triple (RG bl (DOL (cap ot cap1)) (injectB br a))
injectRightG (Triple (RG bl d br))            a      = Triple (RG bl d (injectB br a))

injectOnly :: Cap OnlyTriple (Closed cl) q j k -> q i j -> ((forall cr. Cap OnlyTriple (Closed cr) q i k -> g) -> g)
injectOnly (Triple (O0 b))                        a = \f -> f $ Triple (O0 (injectB b a))
injectOnly (Cap (OOX bl d br) cap1)               a = \f -> f $ Cap (OOX bl d (injectB br a)) cap1
injectOnly (Cap (OXO bl@B7{} (D2 lt rt) br) cap1) a = \f -> f $ case uncap lt of ViewCap lt2 cap2 -> Cap (OYX bl (D2 lt2 (cap rt cap1)) (injectB br a)) cap2
injectOnly (Cap (OXO bl@B7{} (DOR ot) br) cap1)   a = \f -> f $ Cap (OYX bl (DOL ot) (injectB br a)) cap1
injectOnly (Cap (OXO bl@B8{} (D2 lt rt) br) cap1) a = \f -> f $ case uncap lt of ViewCap lt2 cap2 -> Cap (OGY bl (D2 lt2 (cap rt cap1)) (injectB br a)) cap2
injectOnly (Cap (OXO bl@B8{} (DOR ot) br) cap1)   a = \f -> f $ Cap (OGY bl (DOL ot) (injectB br a)) cap1
injectOnly (Cap (OXO bl@B9{} (D2 lt rt) br) cap1) a = \f -> f $ case uncap lt of ViewCap lt2 cap2 -> Cap (OGY bl (D2 lt2 (cap rt cap1)) (injectB br a)) cap2
injectOnly (Cap (OXO bl@B9{} (DOR ot) br) cap1)   a = \f -> f $ Cap (OGY bl (DOL ot) (injectB br a)) cap1
injectOnly (Cap (OYX bl d br) cap1)               a = \f -> f $ Cap (OYX bl d (injectB br a)) cap1
injectOnly (Cap (OGY bl d br) cap1)               a = \f -> f $ Triple (OGG bl (plugL cap1 d) (injectB br a))
injectOnly (Triple (OGG bl d br))                 a = \f -> f $ Triple (OGG bl d (injectB br a))
injectOnly (Triple (ORX bl d br))                 a = \f -> f $ Triple (ORX bl d (injectB br a))
injectOnly (Triple (OXR bl D0 br))                a = \f -> f $ Triple (O0 (injectB (catenateB bl br) a))
injectOnly (Triple (OXR bl@B6{} (D2 lt rt) br))   a = \f -> f $ case uncap rt of ViewCap rt2 cap2 -> Cap (OOX bl (D2 lt rt2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B6{} (DOL ot) br))     a = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OOX bl (DOR ot2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B6{} (DOR ot) br))     a = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OOX bl (DOR ot2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B7{} (D2 lt rt) br))   a = \f -> f $ case uncap rt of ViewCap rt2 cap2 -> Cap (OXO bl (D2 lt rt2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B7{} (DOL ot) br))     a = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B7{} (DOR ot) br))     a = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B8{} (D2 lt rt) br))   a = \f -> f $ case uncap rt of ViewCap rt2 cap2 -> Cap (OXO bl (D2 lt rt2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B8{} (DOL ot) br))     a = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B8{} (DOR ot) br))     a = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B9{} (D2 lt rt) br))   a = \f -> f $ case uncap rt of ViewCap rt2 cap2 -> Cap (OXO bl (D2 lt rt2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B9{} (DOL ot) br))     a = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) (injectB br a)) cap2
injectOnly (Triple (OXR bl@B9{} (DOR ot) br))     a = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OXO bl (DOR ot2) (injectB br a)) cap2

injectOnlyG :: Cap OnlyTriple (Closed Green) q j k -> q i j -> Cap OnlyTriple (Closed Green) q i k
injectOnlyG (Triple (O0 b))                        a = Triple (O0 (injectB b a))
injectOnlyG (Cap (OOX bl d br) cap1)               a = Cap (OOX bl d (injectB br a)) cap1
injectOnlyG (Cap (OXO bl@B7{} (D2 lt rt) br) cap1) a = case uncap lt of ViewCap lt2 cap2 -> Cap (OYX bl (D2 lt2 (cap rt cap1)) (injectB br a)) cap2
injectOnlyG (Cap (OXO bl@B7{} (DOR ot) br) cap1)   a = Cap (OYX bl (DOL ot) (injectB br a)) cap1
injectOnlyG (Cap (OXO bl@B8{} (D2 lt rt) br) cap1) a = case uncap lt of ViewCap lt2 cap2 -> Cap (OGY bl (D2 lt2 (cap rt cap1)) (injectB br a)) cap2
injectOnlyG (Cap (OXO bl@B8{} (DOR ot) br) cap1)   a = Cap (OGY bl (DOL ot) (injectB br a)) cap1
injectOnlyG (Cap (OXO bl@B9{} (D2 lt rt) br) cap1) a = case uncap lt of ViewCap lt2 cap2 -> Cap (OGY bl (D2 lt2 (cap rt cap1)) (injectB br a)) cap2
injectOnlyG (Cap (OXO bl@B9{} (DOR ot) br) cap1)   a = Cap (OGY bl (DOL ot) (injectB br a)) cap1
injectOnlyG (Cap (OYX bl d br) cap1)               a = Cap (OYX bl d (injectB br a)) cap1
injectOnlyG (Cap (OGY bl d br) cap1)               a = Triple (OGG bl (plugL cap1 d) (injectB br a))
injectOnlyG (Triple (OGG bl d br))                 a = Triple (OGG bl d (injectB br a))

pushOnlyG :: q j k -> Cap OnlyTriple (Closed Green) q i j -> Cap OnlyTriple (Closed Green) q i k
pushOnlyG a (Triple (O0 b))                        = Triple (O0 (pushB a b))
pushOnlyG a (Cap (OOX bl d br@B6{}) cap1)          = Cap (OXO (pushB a bl) d br) cap1
pushOnlyG a (Cap (OOX bl (D2 lt rt) br@B7{}) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (OYX (pushB a bl) (D2 lt2 (cap rt cap1)) br) cap2
pushOnlyG a (Cap (OOX bl (DOR ot) br@B7{}) cap1)   = Cap (OYX (pushB a bl) (DOL ot) br) cap1
pushOnlyG a (Cap (OOX bl (D2 lt rt) br@B8{}) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (OYX (pushB a bl) (D2 lt2 (cap rt cap1)) br) cap2
pushOnlyG a (Cap (OOX bl (DOR ot) br@B8{}) cap1)   = Cap (OYX (pushB a bl) (DOL ot) br) cap1
pushOnlyG a (Cap (OOX bl (D2 lt rt) br@B9{}) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (OYX (pushB a bl) (D2 lt2 (cap rt cap1)) br) cap2
pushOnlyG a (Cap (OOX bl (DOR ot) br@B9{}) cap1)   = Cap (OYX (pushB a bl) (DOL ot) br) cap1
pushOnlyG a (Cap (OXO bl d br) cap1)               = Cap (OXO (pushB a bl) d br) cap1
pushOnlyG a (Cap (OYX bl d br@B7{}) cap1)          = Cap (OGY (pushB a bl) d br) cap1
pushOnlyG a (Cap (OYX bl (D2 lt rt) br@B8{}) cap1) = Triple (OGG (pushB a bl) (D2 (cap lt cap1) rt) br)
pushOnlyG a (Cap (OYX bl (DOL ot) br@B8{}) cap1)   = Triple (OGG (pushB a bl) (DOL (cap ot cap1)) br)
pushOnlyG a (Cap (OYX bl (D2 lt rt) br@B9{}) cap1) = Triple (OGG (pushB a bl) (D2 (cap lt cap1) rt) br)
pushOnlyG a (Cap (OYX bl (DOL ot) br@B9{}) cap1)   = Triple (OGG (pushB a bl) (DOL (cap ot cap1)) br)
pushOnlyG a (Cap (OGY bl d br) cap1)               = Cap (OGY (pushB a bl) d br) cap1
pushOnlyG a (Triple (OGG bl d br))                 = Triple (OGG (pushB a bl) d br)

pushLeft :: q j k -> Cap LeftTriple (Closed cl) q i j -> ((forall cr. Cap LeftTriple (Closed cr) q i k -> g) -> g)
pushLeft a (Triple (L0 bl br))                   = \f -> f $ Triple (L0 (pushB a bl) br)
pushLeft a (Cap (LO bl (D2 lt rt) br) cap1)      = \f -> f $ case uncap lt of ViewCap lt2 cap2 -> Cap (LY (pushB a bl) (D2 lt2 (cap rt cap1)) br) cap2
pushLeft a (Cap (LO bl (DOR ot) br) cap1)        = \f -> f $ Cap (LY (pushB a bl) (DOL ot) br) cap1
pushLeft a (Cap (LY bl (D2 lt rt) br) cap1)      = \f -> f $ Triple (LG (pushB a bl) (D2 (cap lt cap1) rt) br)
pushLeft a (Cap (LY bl (DOL ot) br) cap1)        = \f -> f $ Triple (LG (pushB a bl) (DOL (cap ot cap1)) br)
pushLeft a (Triple (LR bl D0 br))                = \f -> f $ Triple (L0 (pushB a bl) br)
pushLeft a (Triple (LR bl (D2 lt rt) br))        = \f -> f $ case uncap rt of ViewCap rt2 cap2 -> Cap (LO (pushB a bl) (D2 lt rt2) br) cap2
pushLeft a (Triple (LR bl (DOL ot) br))          = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (LO (pushB a bl) (DOR ot2) br) cap2
pushLeft a (Triple (LR bl (DOR ot) br))          = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (LO (pushB a bl) (DOR ot2) br) cap2
pushLeft a (Triple (LG bl d br))                 = \f -> f $ Triple (LG (pushB a bl) d br)

pushLeftG :: q j k -> Cap LeftTriple (Closed Green) q i j -> Cap LeftTriple (Closed Green) q i k
pushLeftG a (Triple (L0 bl br))                   = Triple (L0 (pushB a bl) br)
pushLeftG a (Cap (LO bl (D2 lt rt) br) cap1)      = case uncap lt of ViewCap lt2 cap2 -> Cap (LY (pushB a bl) (D2 lt2 (cap rt cap1)) br) cap2
pushLeftG a (Cap (LO bl (DOR ot) br) cap1)        = Cap (LY (pushB a bl) (DOL ot) br) cap1
pushLeftG a (Cap (LY bl (D2 lt rt) br) cap1)      = Triple (LG (pushB a bl) (D2 (cap lt cap1) rt) br)
pushLeftG a (Cap (LY bl (DOL ot) br) cap1)        = Triple (LG (pushB a bl) (DOL (cap ot cap1)) br)
pushLeftG a (Triple (LG bl d br))                 = Triple (LG (pushB a bl) d br)

pushOnly :: q j k -> Cap OnlyTriple (Closed cl) q i j -> ((forall cr. Cap OnlyTriple (Closed cr) q i k -> g) -> g)
pushOnly a (Triple (O0 b))                        = \f -> f $ Triple (O0 (pushB a b))
pushOnly a (Cap (OOX bl d br@B6{}) cap1)          = \f -> f $ Cap (OXO (pushB a bl) d br) cap1
pushOnly a (Cap (OOX bl (D2 lt rt) br@B7{}) cap1) = \f -> f $ case uncap lt of ViewCap lt2 cap2 -> Cap (OYX (pushB a bl) (D2 lt2 (cap rt cap1)) br) cap2
pushOnly a (Cap (OOX bl (DOR ot) br@B7{}) cap1)   = \f -> f $ Cap (OYX (pushB a bl) (DOL ot) br) cap1
pushOnly a (Cap (OOX bl (D2 lt rt) br@B8{}) cap1) = \f -> f $ case uncap lt of ViewCap lt2 cap2 -> Cap (OYX (pushB a bl) (D2 lt2 (cap rt cap1)) br) cap2
pushOnly a (Cap (OOX bl (DOR ot) br@B8{}) cap1)   = \f -> f $ Cap (OYX (pushB a bl) (DOL ot) br) cap1
pushOnly a (Cap (OOX bl (D2 lt rt) br@B9{}) cap1) = \f -> f $ case uncap lt of ViewCap lt2 cap2 -> Cap (OYX (pushB a bl) (D2 lt2 (cap rt cap1)) br) cap2
pushOnly a (Cap (OOX bl (DOR ot) br@B9{}) cap1)   = \f -> f $ Cap (OYX (pushB a bl) (DOL ot) br) cap1
pushOnly a (Cap (OXO bl d br) cap1)               = \f -> f $ Cap (OXO (pushB a bl) d br) cap1
pushOnly a (Cap (OYX bl d br@B7{}) cap1)          = \f -> f $ Cap (OGY (pushB a bl) d br) cap1
pushOnly a (Cap (OYX bl (D2 lt rt) br@B8{}) cap1) = \f -> f $ Triple (OGG (pushB a bl) (D2 (cap lt cap1) rt) br)
pushOnly a (Cap (OYX bl (DOL ot) br@B8{}) cap1)   = \f -> f $ Triple (OGG (pushB a bl) (DOL (cap ot cap1)) br)
pushOnly a (Cap (OYX bl (D2 lt rt) br@B9{}) cap1) = \f -> f $ Triple (OGG (pushB a bl) (D2 (cap lt cap1) rt) br)
pushOnly a (Cap (OYX bl (DOL ot) br@B9{}) cap1)   = \f -> f $ Triple (OGG (pushB a bl) (DOL (cap ot cap1)) br)
pushOnly a (Cap (OGY bl d br) cap1)               = \f -> f $ Cap (OGY (pushB a bl) d br) cap1
pushOnly a (Triple (OGG bl d br))                 = \f -> f $ Triple (OGG (pushB a bl) d br)
pushOnly a (Triple (ORX bl d br@B5{}))            = \f -> f $ Triple (OXR (pushB a bl) d br)
pushOnly a (Triple (ORX bl D0         br))        = \f -> f $ Triple (O0 (catenateB (pushB a bl) br))
pushOnly a (Triple (ORX bl (D2 lt rt) br@B6{}))   = \f -> f $ case uncap rt of ViewCap rt2 cap2 -> Cap (OOX (pushB a bl) (D2 lt rt2) br) cap2
pushOnly a (Triple (ORX bl (DOL ot)   br@B6{}))   = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (ORX bl (DOR ot)   br@B6{}))   = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (ORX bl (D2 lt rt) br@B7{}))   = \f -> f $ case uncap rt of ViewCap rt2 cap2 -> Cap (OOX (pushB a bl) (D2 lt rt2) br) cap2
pushOnly a (Triple (ORX bl (DOL ot)   br@B7{}))   = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (ORX bl (DOR ot)   br@B7{}))   = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (ORX bl (D2 lt rt) br@B8{}))   = \f -> f $ case uncap rt of ViewCap rt2 cap2 -> Cap (OOX (pushB a bl) (D2 lt rt2) br) cap2
pushOnly a (Triple (ORX bl (DOL ot)   br@B8{}))   = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (ORX bl (DOR ot)   br@B8{}))   = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (ORX bl (D2 lt rt) br@B9{}))   = \f -> f $ case uncap rt of ViewCap rt2 cap2 -> Cap (OOX (pushB a bl) (D2 lt rt2) br) cap2
pushOnly a (Triple (ORX bl (DOL ot)   br@B9{}))   = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (ORX bl (DOR ot)   br@B9{}))   = \f -> f $ case uncap ot of ViewCap ot2 cap2 -> Cap (OOX (pushB a bl) (DOR ot2) br) cap2
pushOnly a (Triple (OXR bl d br))                 = \f -> f $ Triple (OXR (pushB a bl) d br)

catenateB :: (c9 ~ (b9 || a9 || (a1 && b8) || (a2 && b7) ||(a3 && b6) || (a4  && b5) || (a5 && b4) || (a6 && b3) || (a7 && b2) || (a8 && b1) || (a2 && b8) ||(a3 && b7) || (a4  && b6) || (a5 && b5) || (a6 && b4) || (a7 && b3) || (a8 && b2) || (a3 && b8) || (a4  && b7) || (a5 && b6) || (a6 && b5) || (a7 && b4) || (a8 && b3) || (a4  && b8) || (a5 && b7) || (a6 && b6) || (a7 && b5) || (a8 && b4) || (a5 && b8) || (a6 && b7) || (a7 && b6) || (a8 && b5) || (a6 && b8) || (a7 && b7) || (a8 && b6) || (a7 && b8) || (a8 && b7) || (a8 && b8)), c8 ~ ((a1 && b7) || (a2 && b6) ||(a3 && b5) || (a4  && b4) || (a5 && b3) || (a6 && b2) || (a7 && b1)), c7 ~ ((a1 && b6) || (a2 && b5) || (a3 && b4) || (a4 && b3) || (a5 && b2) || (a6 && b1)), c6 ~ ((a1 && b5) || (a2 && b4) || (a3 && b3) || (a4 && b2) || (a5 && b1)), c5 ~ ((a1 && b4) || (a2 && b3) || (a3 && b2) || (a4 && b1)), c4 ~ ((a1 && b3) || (a2 && b2) || (a3 && b1)), c3 ~ ((a1 && b2) || (a2 && b1)), c2 ~ (a1 && b1)) => Buffer a1 a2 a3 a4 a5 a6 a7 a8 a9 q j k -> Buffer b1 b2 b3 b4 b5 b6 b7 b8 b9 q i j -> Buffer F c2 c3 c4 c5 c6 c7 c8 c9 q i k
catenateB B9{} B9{} = error "Bad"
catenateB (B1 a) br@B1{} = pushB a br
catenateB (B1 a) br@B2{} = pushB a br
catenateB (B1 a) br@B3{} = pushB a br
catenateB (B1 a) br@B4{} = pushB a br
catenateB (B1 a) br@B5{} = pushB a br
catenateB (B1 a) br@B6{} = pushB a br
catenateB (B1 a) br@B7{} = pushB a br
catenateB (B1 a) br@B8{} = pushB a br
catenateB (B1 a) br@B9{} = pushB a br
catenateB (B2 a b) br@B1{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B2{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B3{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B4{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B5{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B6{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B7{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B8{} = pushB a $ pushB b $ br
catenateB (B2 a b) br@B9{} = pushB a $ pushB b $ br
catenateB (B3 a b c) br@B1{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B2{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B3{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B4{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B5{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B6{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B7{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B8{} = pushB a $ pushB b $ pushB c $ br
catenateB (B3 a b c) br@B9{} = pushB a $ pushB b $ pushB c $ br
catenateB (B4 a b c d) br@B1{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B2{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B3{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B4{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B5{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B6{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B7{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B8{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B4 a b c d) br@B9{} = pushB a $ pushB b $ pushB c $ pushB d $ br
catenateB (B5 a b c d e) br@B1{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B2{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B3{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B4{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B5{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B6{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B7{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B8{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B5 a b c d e) br@B9{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ br
catenateB (B6 a b c d e f) br@B1{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B2{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B3{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B4{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B5{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B6{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B7{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B8{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B6 a b c d e f) br@B9{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ br
catenateB (B7 a b c d e f g) br@B1{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B2{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B3{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B4{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B5{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B6{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B7{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B8{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B7 a b c d e f g) br@B9{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ br
catenateB (B8 a b c d e f g h) br@B1{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B2{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B3{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B4{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B5{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B6{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B7{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B8{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB (B8 a b c d e f g h) br@B9{} = pushB a $ pushB b $ pushB c $ pushB d $ pushB e $ pushB f $ pushB g $ pushB h $ br
catenateB bl@B9{} (B1 a) = injectB bl a
catenateB bl@B9{} (B2 a b) = injectB (injectB bl a) b
catenateB bl@B9{} (B3 a b c) = injectB (injectB (injectB bl a) b) c
catenateB bl@B9{} (B4 a b c d) = injectB (injectB (injectB (injectB bl a) b) c) d
catenateB bl@B9{} (B5 a b c d e) = injectB (injectB (injectB (injectB (injectB bl a) b) c) d) e
catenateB bl@B9{} (B6 a b c d e f) = injectB (injectB (injectB (injectB (injectB (injectB bl a) b) c) d) e) f
catenateB bl@B9{} (B7 a b c d e f g) = injectB (injectB (injectB (injectB (injectB (injectB (injectB bl a) b) c) d) e) f) g
catenateB bl@B9{} (B8 a b c d e f g h) = injectB (injectB (injectB (injectB (injectB (injectB (injectB (injectB bl a) b) c) d) e) f) g) h

catenate :: Deque (Closed Green) (Closed Green) q j k -> Deque (Closed Green) (Closed Green) q i j -> Deque (Closed Green) (Closed Green) q i k
-- Trivial
catenate D0 a = a
catenate a D0 = a
-- Case 4:
catenate (DOL (Triple (O0 bl@B8{}))) (DOL (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOL (Triple (O0 bl)))      (DOL (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
catenate (DOL (Triple (O0 bl@B8{}))) (DOR (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOL (Triple (O0 bl)))      (DOR (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
catenate (DOR (Triple (O0 bl@B8{}))) (DOL (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOR (Triple (O0 bl)))      (DOL (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
catenate (DOR (Triple (O0 bl@B8{}))) (DOR (Triple (O0 br@B8{}))) = DOL (Triple (OGG bl D0 br))
catenate (DOR (Triple (O0 bl)))      (DOR (Triple (O0 br)))      = DOL (Triple (O0 (catenateB bl br)))
-- Case 2:
catenate (DOL (Triple (O0 bl))) (D2 lt rt) = D2 (onlyL bl lt) rt
catenate (DOR (Triple (O0 bl))) (D2 lt rt) = D2 (onlyL bl lt) rt
-- Case 3
catenate (D2 lt rt) (DOL (Triple (O0 br))) = D2 lt (onlyR rt br)
catenate (D2 lt rt) (DOR (Triple (O0 br))) = D2 lt (onlyR rt br)
-- Case 1
catenate d e = D2 (fixLeft d) (fixRight e)

catenate' :: Deque (Closed cl1) (Closed cr1) q j k -> Deque (Closed cl2) (Closed cr2) q i j -> (forall cl3 cr3. Deque (Closed cl3) (Closed cr3) q i k -> g) -> g
-- Trivial
catenate' D0 a f = f a
catenate' a D0 f = f a
-- Case 4:
catenate' (DOL (Triple (O0 bl@B8{}))) (DOL (Triple (O0 br@B8{}))) f = f $ DOL (Triple (OGG bl D0 br))
catenate' (DOL (Triple (O0 bl)))      (DOL (Triple (O0 br)))      f = f $ DOL (Triple (O0 (catenateB bl br)))
catenate' (DOL (Triple (O0 bl@B8{}))) (DOR (Triple (O0 br@B8{}))) f = f $ DOL (Triple (OGG bl D0 br))
catenate' (DOL (Triple (O0 bl)))      (DOR (Triple (O0 br)))      f = f $ DOL (Triple (O0 (catenateB bl br)))
catenate' (DOR (Triple (O0 bl@B8{}))) (DOL (Triple (O0 br@B8{}))) f = f $ DOL (Triple (OGG bl D0 br))
catenate' (DOR (Triple (O0 bl)))      (DOL (Triple (O0 br)))      f = f $ DOL (Triple (O0 (catenateB bl br)))
catenate' (DOR (Triple (O0 bl@B8{}))) (DOR (Triple (O0 br@B8{}))) f = f $ DOL (Triple (OGG bl D0 br))
catenate' (DOR (Triple (O0 bl)))      (DOR (Triple (O0 br)))      f = f $ DOL (Triple (O0 (catenateB bl br)))
-- -- Case 2:
catenate' (DOL (Triple (O0 bl))) d f = onlyL' bl d f
catenate' (DOR (Triple (O0 bl))) d f = onlyL' bl d f
-- -- Case 3
catenate' d (DOL (Triple (O0 br))) f = onlyR' d br f
catenate' d (DOR (Triple (O0 br))) f = onlyR' d br f
-- -- Case 1
-- catenate' d e f = f $ D2 (fixLeft d) (fixRight e)

onlyL :: Buffer k1 k2 k3 k4 k5 k6 k7 k8 k9 q j k -> Cap LeftTriple (Closed Green) q i j -> Cap LeftTriple (Closed Green) q i k
onlyL bl@B8{} (Triple (L0 ll lr))              = Triple (LG bl (push (S1 ll) D0) lr)
onlyL bl@B8{} (Cap (LO ll d lr) cap1)          = Triple (LG bl (push (S1 ll) (plugR d cap1)) lr)
onlyL bl@B8{} (Cap (LY ll d lr) cap1)          = Triple (pushWith (S1 ll) (plugL cap1 d) (\e -> LG bl e lr))
onlyL bl@B8{} (Triple (LG ll d lr))            = Triple (pushWith (S1 ll) d (\e -> LG bl e lr))
onlyL bl@B9{} (Triple (L0 ll lr))              = Triple (LG bl (push (S1 ll) D0) lr)
onlyL bl@B9{} (Cap (LO ll d lr) cap1)          = Triple (LG bl (push (S1 ll) (plugR d cap1)) lr)
onlyL bl@B9{} (Cap (LY ll d lr) cap1)          = Triple (pushWith (S1 ll) (plugL cap1 d) (\e -> LG bl e lr))
onlyL bl@B9{} (Triple (LG ll d lr))            = Triple (pushWith (S1 ll) d (\e -> LG bl e lr))
onlyL bl      (Triple (L0 ll lr))              = Triple (L0 (catenateB bl ll) lr)
onlyL bl@B1{} (Cap (LO ll (D2 lt rt) lr) cap1) = case uncap lt of ViewCap lt2 cap2 -> Cap (LY (catenateB bl ll) (D2 lt2 (cap rt cap1)) lr) cap2
onlyL bl@B1{} (Cap (LO ll (DOR ot) lr) cap1)   = Cap (LY (catenateB bl ll) (DOL ot) lr) cap1
onlyL bl@B2{} (Cap (LO ll d lr) cap1)          = Triple (LG (catenateB bl ll) d2 lr) where d2 = plugR d cap1
onlyL bl@B3{} (Cap (LO ll d lr) cap1)          = Triple (LG (catenateB bl ll) d2 lr) where d2 = plugR d cap1
onlyL bl@B4{} (Cap (LO ll d lr) cap1)          = Triple (LG (catenateB bl ll) d2 lr) where d2 = plugR d cap1
onlyL bl@B5{} (Cap (LO ll d lr) cap1)          = Triple (LG (catenateB bl ll) d2 lr) where d2 = plugR d cap1
onlyL bl@B6{} (Cap (LO ll d lr) cap1)          = Triple (LG (catenateB bl ll) d2 lr) where d2 = plugR d cap1
onlyL bl@B7{} (Cap (LO ll d lr) cap1)          = Triple (LG (catenateB bl ll) d2 lr) where d2 = plugR d cap1
onlyL bl      (Cap (LY ll d lr) cap1)          = Triple (LG (catenateB bl ll) d2 lr) where d2 = plugL cap1 d
onlyL bl      (Triple (LG ll d lr))            = Triple (LG (catenateB bl ll) d lr)

onlyL' :: Buffer k1 k2 k3 k4 k5 k6 k7 k8 k9 q j k -> Deque (Closed cl1) (Closed cr1) q i j -> (forall cl2 cr2. Deque (Closed cl2) (Closed cr2) q i k -> g) -> g
onlyL' _ D0 _ = error "Impossible"
onlyL' _ DOL{} _ = error "Impossible"
onlyL' _ DOR{} _ = error "Impossible"
onlyL' bl@B8{} (D2 (Triple (L0 ll lr)) r)              f = f $ D2 (Triple (LG bl (push (S1 ll) D0) lr)) r
onlyL' bl@B8{} (D2 (Cap (LO ll d lr) cap1) r)          f = f $ D2 (Triple (pushWith (S1 ll) (plugR d cap1) (\e -> LG bl e lr))) r
onlyL' bl@B8{} (D2 (Cap (LY ll d lr) cap1) r)          f = f $ D2 (Triple (pushWith (S1 ll) (plugL cap1 d) (\e -> LG bl e lr))) r
onlyL' bl@B8{} (D2 (Triple (LG ll d lr)) r)            f = f $ D2 (Triple (pushWith (S1 ll) d (\e -> LG bl e lr))) r
onlyL' bl@B8{} (D2 (Triple (LR ll d lr)) r)            f = f $ D2 (Triple (pushWith (S1 ll) d (\e -> LG bl e lr))) r
onlyL' bl@B9{} (D2 (Triple (L0 ll lr)) r)              f = f $ D2 (Triple (LG bl (push (S1 ll) D0) lr)) r
onlyL' bl@B9{} (D2 (Cap (LO ll d lr) cap1) r)          f = f $ D2 (Triple (pushWith (S1 ll) (plugR d cap1) $ \e -> LG bl e lr)) r
onlyL' bl@B9{} (D2 (Cap (LY ll d lr) cap1) r)          f = f $ D2 (Triple (pushWith (S1 ll) (plugL cap1 d) (\e -> LG bl e lr))) r
onlyL' bl@B9{} (D2 (Triple (LG ll d lr)) r)            f = f $ D2 (Triple (pushWith (S1 ll) d (\e -> LG bl e lr))) r
onlyL' bl@B9{} (D2 (Triple (LR ll d lr)) r)            f = f $ D2 (Triple (pushWith (S1 ll) d (\e -> LG bl e lr))) r
onlyL' bl      (D2 (Triple (L0 ll lr)) r)              f = f $ D2 (Triple (L0 (catenateB bl ll) lr)) r
onlyL' bl@B1{} (D2 (Triple (LR ll D0 lr)) r)           f = f $ D2 (Triple (L0 (catenateB bl ll) lr)) r
onlyL' bl@B1{} (D2 (Triple (LR ll (D2 lt rt) lr)) r) f = f $ case uncap rt of ViewCap rt2 cap2 -> D2 (Cap (LO (catenateB bl ll) (D2 lt rt2) lr) cap2) r
onlyL' bl@B1{} (D2 (Triple (LR ll (DOL ot) lr)) r)   f = f $ case uncap ot of ViewCap ot2 cap2 -> D2 (Cap (LO (catenateB bl ll) (DOR ot2) lr) cap2) r
onlyL' bl@B1{} (D2 (Triple (LR ll (DOR ot) lr)) r)   f = f $ case uncap ot of ViewCap ot2 cap2 -> D2 (Cap (LO (catenateB bl ll) (DOR ot2) lr) cap2) r
onlyL' bl@B2{} (D2 (Triple (LR ll D0 lr)) r)         f = f $ D2 (Triple (L0 (catenateB bl ll) lr)) r
onlyL' bl@B2{} (D2 (Triple (LR ll (D2 lt rt) lr)) r) f = f $ case uncap lt of ViewCap lt2 cap2 -> D2 (Cap (LY (catenateB bl ll) (D2 lt2 rt) lr) cap2) r
onlyL' bl@B2{} (D2 (Triple (LR ll (DOL ot) lr)) r)   f = f $ case uncap ot of ViewCap ot2 cap2 -> D2 (Cap (LY (catenateB bl ll) (DOL ot2) lr) cap2) r
onlyL' bl@B2{} (D2 (Triple (LR ll (DOR ot) lr)) r)   f = f $ case uncap ot of ViewCap ot2 cap2 -> D2 (Cap (LY (catenateB bl ll) (DOL ot2) lr) cap2) r
onlyL' bl@B3{} (D2 (Triple (LR ll d lr)) r)          f = f $ D2 (Triple (LG (catenateB bl ll) d lr)) r
onlyL' bl@B4{} (D2 (Triple (LR ll d lr)) r)          f = f $ D2 (Triple (LG (catenateB bl ll) d lr)) r
onlyL' bl@B5{} (D2 (Triple (LR ll d lr)) r)          f = f $ D2 (Triple (LG (catenateB bl ll) d lr)) r
onlyL' bl@B6{} (D2 (Triple (LR ll d lr)) r)          f = f $ D2 (Triple (LG (catenateB bl ll) d lr)) r
onlyL' bl@B7{} (D2 (Triple (LR ll d lr)) r)          f = f $ D2 (Triple (LG (catenateB bl ll) d lr)) r
onlyL' bl@B1{} (D2 (Cap (LO ll (D2 lt rt) lr) cap1) r) f = f $ case uncap lt of ViewCap lt2 cap2 -> D2 (Cap (LY (catenateB bl ll) (D2 lt2 (cap rt cap1)) lr) cap2) r
onlyL' bl@B1{} (D2 (Cap (LO ll (DOR ot) lr) cap1) r)   f = f $ D2 (Cap (LY (catenateB bl ll) (DOL ot) lr) cap1) r
onlyL' bl@B2{} (D2 (Cap (LO ll d lr) cap1) r)          f = f $ D2 (Triple (LG (catenateB bl ll) d2 lr)) r where d2 = plugR d cap1
onlyL' bl@B3{} (D2 (Cap (LO ll d lr) cap1) r)          f = f $ D2 (Triple (LG (catenateB bl ll) d2 lr)) r where d2 = plugR d cap1
onlyL' bl@B4{} (D2 (Cap (LO ll d lr) cap1) r)          f = f $ D2 (Triple (LG (catenateB bl ll) d2 lr)) r where d2 = plugR d cap1
onlyL' bl@B5{} (D2 (Cap (LO ll d lr) cap1) r)          f = f $ D2 (Triple (LG (catenateB bl ll) d2 lr)) r where d2 = plugR d cap1
onlyL' bl@B6{} (D2 (Cap (LO ll d lr) cap1) r)          f = f $ D2 (Triple (LG (catenateB bl ll) d2 lr)) r where d2 = plugR d cap1
onlyL' bl@B7{} (D2 (Cap (LO ll d lr) cap1) r)          f = f $ D2 (Triple (LG (catenateB bl ll) d2 lr)) r where d2 = plugR d cap1
onlyL' bl      (D2 (Cap (LY ll d lr) cap1) r)          f = f $ D2 (Triple (LG (catenateB bl ll) d2 lr)) r where d2 = plugL cap1 d
onlyL' bl      (D2 (Triple (LG ll d lr)) r)            f = f $ D2 (Triple (LG (catenateB bl ll) d lr)) r

onlyR :: Cap RightTriple (Closed Green) q j k -> Buffer k1 k2 k3 k4 k5 k6 k7 k8 k9 q i j -> Cap RightTriple (Closed Green) q i k
onlyR (Triple (R0 rl rr))              br@B8{} = Triple (RG rl (inject D0 (S1 rr)) br)
onlyR (Cap (RO rl d rr) cap1)          br@B8{} = Triple (RG rl (inject (plugR d cap1) (S1 rr)) br)
onlyR (Cap (RY rl d rr) cap1)          br@B8{} = Triple (injectWith (plugL cap1 d) (S1 rr) (\e -> RG rl e br))
onlyR (Triple (RG rl d rr))            br@B8{} = Triple (injectWith d (S1 rr) (\e -> RG rl e br))
onlyR (Triple (R0 rl rr))              br@B9{} = Triple (RG rl (inject D0 (S1 rr)) br)
onlyR (Cap (RO rl d rr) cap1)          br@B9{} = Triple (RG rl (inject (plugR d cap1) (S1 rr)) br)
onlyR (Cap (RY rl d rr) cap1)          br@B9{} = Triple (injectWith (plugL cap1 d) (S1 rr) (\e -> RG rl e br))
onlyR (Triple (RG rl d rr))            br@B9{} = Triple (injectWith d (S1 rr) (\e -> RG rl e br))
onlyR (Triple (R0 rl rr))              br      = Triple (R0 rl (catenateB rr br))
onlyR (Cap (RO rl (D2 lt rt) rr) cap1) br@B1{} = case uncap lt of ViewCap lt2 cap2 -> Cap (RY rl (D2 lt2 (cap rt cap1)) (catenateB rr br)) cap2
onlyR (Cap (RO rl (DOR ot) rr) cap1)   br@B1{} = Cap (RY rl (DOL ot) (catenateB rr br)) cap1
onlyR (Cap (RO rl d rr) cap1)          br@B2{} = Triple (RG rl d2 (catenateB rr br)) where d2 = plugR d cap1
onlyR (Cap (RO rl d rr) cap1)          br@B3{} = Triple (RG rl d2 (catenateB rr br)) where d2 = plugR d cap1
onlyR (Cap (RO rl d rr) cap1)          br@B4{} = Triple (RG rl d2 (catenateB rr br)) where d2 = plugR d cap1
onlyR (Cap (RO rl d rr) cap1)          br@B5{} = Triple (RG rl d2 (catenateB rr br)) where d2 = plugR d cap1
onlyR (Cap (RO rl d rr) cap1)          br@B6{} = Triple (RG rl d2 (catenateB rr br)) where d2 = plugR d cap1
onlyR (Cap (RO rl d rr) cap1)          br@B7{} = Triple (RG rl d2 (catenateB rr br)) where d2 = plugR d cap1
onlyR (Cap (RY rl d rr) cap1)          br      = Triple (RG rl d2 (catenateB rr br)) where d2 = plugL cap1 d
onlyR (Triple (RG rl d rr))            br      = Triple (RG rl d (catenateB rr br))

onlyR' :: Deque (Closed cl1) (Closed cr1) q j k -> Buffer k1 k2 k3 k4 k5 k6 k7 k8 k9 q i j -> (forall cl2 cr2. Deque (Closed cl2) (Closed cr2) q i k -> g) -> g
onlyR' D0 _ _ = error "Impossible"
onlyR' DOL{} _ _ = error "Impossible"
onlyR' DOR{} _ _ = error "Impossible"
onlyR' (D2 l (Triple (R0 rl rr)))              br@B8{} f = f $ D2 l (Triple (RG rl (inject D0 (S1 rr)) br))
onlyR' (D2 l (Cap (RO rl d rr) cap1))          br@B8{} f = f $ D2 l (Triple (injectWith (plugR d cap1) (S1 rr) $ \e -> RG rl e br))
onlyR' (D2 l (Cap (RY rl d rr) cap1))          br@B8{} f = f $ D2 l (Triple (injectWith (plugL cap1 d) (S1 rr) (\e -> RG rl e br)))
onlyR' (D2 l (Triple (RG rl d rr)))            br@B8{} f = f $ D2 l (Triple (injectWith d (S1 rr) (\e -> RG rl e br)))
onlyR' (D2 l (Triple (RR rl d rr)))            br@B8{} f = f $ D2 l (Triple (injectWith d (S1 rr) (\e -> RG rl e br)))
onlyR' (D2 l (Triple (R0 rl rr)))              br@B9{} f = f $ D2 l (Triple (RG rl (inject D0 (S1 rr)) br))
onlyR' (D2 l (Cap (RO rl d rr) cap1))          br@B9{} f = f $ D2 l (Triple (injectWith (plugR d cap1) (S1 rr) $ \e -> RG rl e br))
onlyR' (D2 l (Cap (RY rl d rr) cap1))          br@B9{} f = f $ D2 l (Triple (injectWith (plugL cap1 d) (S1 rr) (\e -> RG rl e br)))
onlyR' (D2 l (Triple (RG rl d rr)))            br@B9{} f = f $ D2 l (Triple (injectWith d (S1 rr) (\e -> RG rl e br)))
onlyR' (D2 l (Triple (RR rl d rr)))            br@B9{} f = f $ D2 l (Triple (injectWith d (S1 rr) (\e -> RG rl e br)))
onlyR' (D2 l (Triple (R0 rl rr)))              br      f = f $ D2 l (Triple (R0 rl (catenateB rr br)))
onlyR' (D2 l (Triple (RR rl D0 rr)))         br@B1{} f = f $ D2 l (Triple (R0 rl (catenateB rr br)))
onlyR' (D2 l (Triple (RR rl (D2 lt rt) rr))) br@B1{} f = f $ case uncap rt of ViewCap rt2 cap2 -> D2 l (Cap (RO rl (D2 lt rt2) (catenateB rr br)) cap2)
onlyR' (D2 l (Triple (RR rl (DOR ot) rr)))   br@B1{} f = f $ case uncap ot of ViewCap ot2 cap2 -> D2 l (Cap (RO rl (DOR ot2) (catenateB rr br)) cap2)
onlyR' (D2 l (Triple (RR rl (DOL ot) rr)))   br@B1{} f = f $ case uncap ot of ViewCap ot2 cap2 -> D2 l (Cap (RO rl (DOR ot2) (catenateB rr br)) cap2)
onlyR' (D2 l (Triple (RR rl D0 rr)))         br@B2{} f = f $ D2 l (Triple (R0 rl (catenateB rr br)))
onlyR' (D2 l (Triple (RR rl (D2 lt rt) rr))) br@B2{} f = f $ case uncap lt of ViewCap lt2 cap2 -> D2 l (Cap (RY rl (D2 lt2 rt) (catenateB rr br)) cap2)
onlyR' (D2 l (Triple (RR rl (DOR ot) rr)))   br@B2{} f = f $ case uncap ot of ViewCap ot2 cap2 -> D2 l (Cap (RY rl (DOL ot2) (catenateB rr br)) cap2)
onlyR' (D2 l (Triple (RR rl (DOL ot) rr)))   br@B2{} f = f $ case uncap ot of ViewCap ot2 cap2 -> D2 l (Cap (RY rl (DOL ot2) (catenateB rr br)) cap2)
onlyR' (D2 l (Triple (RR rl d rr)))          br@B3{} f = f $ D2 l (Triple (RG rl d (catenateB rr br)))
onlyR' (D2 l (Triple (RR rl d rr)))          br@B4{} f = f $ D2 l (Triple (RG rl d (catenateB rr br)))
onlyR' (D2 l (Triple (RR rl d rr)))          br@B5{} f = f $ D2 l (Triple (RG rl d (catenateB rr br)))
onlyR' (D2 l (Triple (RR rl d rr)))          br@B6{} f = f $ D2 l (Triple (RG rl d (catenateB rr br)))
onlyR' (D2 l (Triple (RR rl d rr)))          br@B7{} f = f $ D2 l (Triple (RG rl d (catenateB rr br)))
onlyR' (D2 l (Cap (RO rl (D2 lt rt) rr) cap1)) br@B1{} f = f $ case uncap lt of ViewCap lt2 cap2 -> D2 l (Cap (RY rl (D2 lt2 (cap rt cap1)) (catenateB rr br)) cap2)
onlyR' (D2 l (Cap (RO rl (DOR ot) rr) cap1))   br@B1{} f = f $ D2 l (Cap (RY rl (DOL ot) (catenateB rr br)) cap1)
onlyR' (D2 l (Cap (RO rl d rr) cap1))          br@B2{} f = f $ D2 l (Triple (RG rl d2 (catenateB rr br))) where d2 = plugR d cap1
onlyR' (D2 l (Cap (RO rl d rr) cap1))          br@B3{} f = f $ D2 l (Triple (RG rl d2 (catenateB rr br))) where d2 = plugR d cap1
onlyR' (D2 l (Cap (RO rl d rr) cap1))          br@B4{} f = f $ D2 l (Triple (RG rl d2 (catenateB rr br))) where d2 = plugR d cap1
onlyR' (D2 l (Cap (RO rl d rr) cap1))          br@B5{} f = f $ D2 l (Triple (RG rl d2 (catenateB rr br))) where d2 = plugR d cap1
onlyR' (D2 l (Cap (RO rl d rr) cap1))          br@B6{} f = f $ D2 l (Triple (RG rl d2 (catenateB rr br))) where d2 = plugR d cap1
onlyR' (D2 l (Cap (RO rl d rr) cap1))          br@B7{} f = f $ D2 l (Triple (RG rl d2 (catenateB rr br))) where d2 = plugR d cap1
onlyR' (D2 l (Cap (RY rl d rr) cap1))          br      f = f $ D2 l (Triple (RG rl d2 (catenateB rr br))) where d2 = plugL cap1 d
onlyR' (D2 l (Triple (RG rl d rr)))            br      f = f $ D2 l (Triple (RG rl d (catenateB rr br)))

fixLeft :: Deque (Closed Green) (Closed Green) q i j -> Cap LeftTriple (Closed Green) q i j
fixLeft d = case d of
  D0 -> error "Impossible"
  (DOL c) -> only c
  (DOR c) -> only c
  (D2 (Triple (LG p1 D0 s1)) (Triple (R0 p2 s2@B9{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (LG p1 D0 s1)) (Triple (R0 p2 s2@B8{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (LG p1 D0 s1)) (Triple (R0 p2 s2))) -> only (Triple (O0 (catenateB (catenateB (catenateB p1 s1) p2) s2)))
  (D2 (Triple (LG p1 D0 s1)) (Triple (RG p2 d2 s2))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) d2 s2))
  (D2 (Triple (LG p1 D0 s1)) (Cap (RO p2 d2 s2) c)) -> only (Cap (OXO (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (LG p1 D0 s1)) (Cap (RY p2 d2 s2) c)) -> only (Cap (OGY (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (L0 p1 s1)) (Triple (R0 p2 s2@B9{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (L0 p1 s1)) (Triple (R0 p2 s2@B8{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (L0 p1 s1)) (Triple (R0 p2 s2))) -> only (Triple (O0 (catenateB (catenateB (catenateB p1 s1) p2) s2)))
  (D2 (Triple (L0 p1 s1)) (Triple (RG p2 d2 s2))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) d2 s2))
  (D2 (Triple (L0 p1 s1)) (Cap (RO p2 d2 s2) c)) -> only (Cap (OXO (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (L0 p1 s1)) (Cap (RY p2 d2 s2) c)) -> only (Cap (OGY (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (LG p1 d1 s1)) (Triple (RG p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> Triple $ injectWith d1 (S3 (catenateB s1 p2) d2 rem2) $ (\e -> LG p1 e (B2 s2r2 s2r1))
  (D2 (Triple (LG p1 d1 s1)) (Triple (R0 p2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> Triple $ injectWith d1 (S3 (catenateB s1 p2) D0 rem2) $ (\e -> LG p1 e (B2 s2r2 s2r1))
  (D2 (Triple (LG p1 d1 s1)) (Cap (RY p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> Triple $ injectWith d1 (S3 (catenateB s1 p2) (plugL c d2) rem2) $ (\e -> LG p1 e (B2 s2r2 s2r1))
  (D2 (Triple (LG p1 d1 s1)) (Cap (RO p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> Triple $ injectWith d1 (S3 (catenateB s1 p2) (plugR d2 c) rem2) $ (\e -> LG p1 e (B2 s2r2 s2r1))
  (D2 (Cap (LY p1 d1 s1) cl) (Triple (RG p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight d1r (S3 (catenateB s1 p2) d2 rem2) $ (\e -> Cap (LY p1 (D2 d1l e) (B2 s2r2 s2r1)) cl)
    DOL ot -> case uncap (injectOnlyG (cap ot cl) (S3 (catenateB s1 p2) d2 rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LY p1 d1 s1) cl) (Triple (R0 p2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight d1r (S3 (catenateB s1 p2) D0 rem2) $ (\e -> Cap (LY p1 (D2 d1l e) (B2 s2r2 s2r1)) cl)
    DOL ot -> case uncap (injectOnlyG (cap ot cl) (S3 (catenateB s1 p2) D0 rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LY p1 d1 s1) cl) (Cap (RY p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight d1r (S3 (catenateB s1 p2) (plugL c d2) rem2) $ (\e -> Cap (LY p1 (D2 d1l e) (B2 s2r2 s2r1)) cl)
    DOL ot -> case uncap (injectOnlyG (cap ot cl) (S3 (catenateB s1 p2) (plugL c d2) rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LY p1 d1 s1) cl) (Cap (RO p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight d1r (S3 (catenateB s1 p2) (plugR d2 c) rem2) $ (\e -> Cap (LY p1 (D2 d1l e) (B2 s2r2 s2r1)) cl)
    DOL ot -> case uncap (injectOnlyG (cap ot cl) (S3 (catenateB s1 p2) (plugR d2 c) rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Triple (RG p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> case uncap (injectRightG (cap d1r cl) (S3 (catenateB s1 p2) d2 rem2)) of ViewCap d1r' c2 -> Cap (LO p1 (D2 d1l d1r') (B2 s2r2 s2r1)) c2
    DOR ot -> case uncap (injectOnlyG (cap ot cl) (S3 (catenateB s1 p2) d2 rem2)) of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Triple (R0 p2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> case uncap (injectRightG (cap d1r cl) (S3 (catenateB s1 p2) D0 rem2)) of ViewCap d1r' c2 -> Cap (LO p1 (D2 d1l d1r') (B2 s2r2 s2r1)) c2
    DOR ot -> case uncap (injectOnlyG (cap ot cl) (S3 (catenateB s1 p2) D0 rem2)) of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Cap (RY p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> case uncap (injectRightG (cap d1r cl) (S3 (catenateB s1 p2) (plugL c d2) rem2)) of ViewCap d1r' c2 -> Cap (LO p1 (D2 d1l d1r') (B2 s2r2 s2r1)) c2
    DOR ot -> case uncap (injectOnlyG (cap ot cl) (S3 (catenateB s1 p2) (plugL c d2) rem2)) of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Cap (RO p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> case uncap (injectRightG (cap d1r cl) (S3 (catenateB s1 p2) (plugR d2 c) rem2)) of ViewCap d1r' c2 -> Cap (LO p1 (D2 d1l d1r') (B2 s2r2 s2r1)) c2
    DOR ot -> case uncap (injectOnlyG (cap ot cl) (S3 (catenateB s1 p2) (plugR d2 c) rem2)) of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s2r2 s2r1)) c2
  where
    aux :: Buffer F F F F c5 c6 c7 c8 c9 q i l -> (forall k3 k4 k5 k6 k7 k8 k9 j k. Buffer F F k3 k4 k5 k6 k7 k8 k9 q k l -> q j k-> q i j -> g) -> g
    aux s2 f = case ejectB s2 of
      H (Shift rem1) s2r1 -> case ejectB rem1 of
        H (Shift rem2) s2r2 -> f rem2 s2r2 s2r1
      H (NoShift rem1) s2r1 -> case ejectB rem1 of
        H (Shift rem2) s2r2 -> f rem2 s2r2 s2r1
        H (NoShift rem2) s2r2 -> f rem2 s2r2 s2r1

    only :: Cap OnlyTriple (Closed Green) q i j -> Cap LeftTriple (Closed Green) q i j
    only (Triple O0{}) = error "Impossible"
    only (Triple (OGG p1 D0 s1)) = Triple (onlyPS p1 s1)
    only (Triple (OGG p1 d1 s1)) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple $ injectWith d1 (S1 rem2) $ (\e -> LG p1 e (B2 s1r2 s1r1))
           H (NoShift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple $ injectWith d1 (S1 rem2) $ (\e -> LG p1 e (B2 s1r2 s1r1))
             H (NoShift rem2) s1r2 -> Triple $ injectWith d1 (S1 rem2) $ (\e -> LG p1 e (B2 s1r2 s1r1))
    only (Cap (OOX p1 d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> foo $ inject (plugR d1 c) (S1 rem2)
               where
                 foo D0 = error "Impossible"
                 foo (D2 lt rt) = case uncap rt of ViewCap rt2 c2 -> Cap (LO p1 (D2 lt rt2) (B2 s1r2 s1r1)) c2
                 foo (DOL ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
                 foo (DOR ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
           H (NoShift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> foo $ inject (plugR d1 c) (S1 rem2)
               where
                 foo D0 = error "Impossible"
                 foo (D2 lt rt) = case uncap rt of ViewCap rt2 c2 -> Cap (LO p1 (D2 lt rt2) (B2 s1r2 s1r1)) c2
                 foo (DOL ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
                 foo (DOR ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
             H (NoShift rem2) s1r2 -> foo $ inject (plugR d1 c) (S1 rem2)
               where
                 foo D0 = error "Impossible"
                 foo (D2 lt rt) = case uncap rt of ViewCap rt2 c2 -> Cap (LO p1 (D2 lt rt2) (B2 s1r2 s1r1)) c2
                 foo (DOL ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
                 foo (DOR ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
    only (Cap (OXO p1@B7{} d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> foo $ inject (plugR d1 c) (S1 rem2)
               where
                 foo D0 = error "Impossible"
                 foo (D2 lt rt) = case uncap lt of ViewCap lt2 c2 -> Cap (LY p1 (D2 lt2 rt) (B2 s1r2 s1r1)) c2
                 foo (DOL ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
                 foo (DOR ot) = case uncap ot of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
    only (Cap (OXO p1@B8{} d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple (LG p1 (inject (plugR d1 c) (S1 rem2)) (B2 s1r2 s1r1))
    only (Cap (OXO p1@B9{} d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple (LG p1 (inject (plugR d1 c) (S1 rem2)) (B2 s1r2 s1r1))
    only (Cap (OYX p1 d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> case uncap lt of ViewCap lt2 c2 -> Cap (LY p1 (D2 lt2 e) (B2 s1r2 s1r1)) c2
               DOL ot -> case uncap (injectOnlyG ot (S1 rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
           H (NoShift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> case uncap lt of ViewCap lt2 c2 -> Cap (LY p1 (D2 lt2 e) (B2 s1r2 s1r1)) c2
               DOL ot -> case uncap (injectOnlyG ot (S1 rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
             H (NoShift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> case uncap lt of ViewCap lt2 c2 -> Cap (LY p1 (D2 lt2 e) (B2 s1r2 s1r1)) c2
               DOL ot -> case uncap (injectOnlyG ot (S1 rem2)) of ViewCap ot2 c2 -> Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
    only (Cap (OGY p1 d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> Triple (LG p1 (D2 lt e) (B2 s1r2 s1r1))
               DOL ot -> Triple (LG p1 (DOL (injectOnlyG ot (S1 rem2))) (B2 s1r2 s1r1))
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"

    onlyPS :: Buffer F F F F F F F a8 a9 q j k -> Buffer F F F F F F F b8 b9 q i j -> LeftTriple (Closed Green) q i k
    onlyPS p1 s1@B9{} = case popB s1 of
        H s1l1 (Shift rem1) -> case popB rem1 of
          H s1l2 (Shift rem2) -> case popB rem2 of
            H s1l3 (Shift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = injectB (injectB (injectB p1 s1l1) s1l2) s1l3
                    s2 = B2 s1r2 s1r1
        H s1l1 (NoShift rem1) -> case popB rem1 of
          H s1l2 (Shift rem2) -> case popB rem2 of
            H s1l3 (Shift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
          H s1l2 (NoShift rem2) -> case popB rem2 of
            H s1l3 (Shift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
            H s1l3 (NoShift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
              H (NoShift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
                H (NoShift rem5) s1r2 -> LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
    onlyPS p1 s1 = case ejectB s1 of
      H (Shift rem1) s1r1 -> case ejectB rem1 of
        H (Shift rem2) s1r2 -> LG (catenateB p1 rem2) D0 (B2 s1r2 s1r1)
      H (NoShift rem1) s1r1 -> case ejectB rem1 of
        H (Shift rem2) s1r2 -> LG (catenateB p1 rem2) D0 (B2 s1r2 s1r1)
        H (NoShift rem2) s1r2 -> LG (catenateB p1 rem2) D0 (B2 s1r2 s1r1)

fixLeft' :: forall cl cr q i j g. Deque (Closed cl) (Closed cr) q i j -> (forall cl'. Cap LeftTriple (Closed cl') q i j -> g) -> g
fixLeft' d f = case d of
  D0 -> error "Impossible"
  (DOL c) -> only c
  (DOR c) -> only c
  (D2 (Triple (LG p1 D0 s1)) (Triple (R0 p2 s2@B9{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (LG p1 D0 s1)) (Triple (R0 p2 s2@B8{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (LG p1 D0 s1)) (Triple (R0 p2 s2))) -> only (Triple (O0 (catenateB (catenateB (catenateB p1 s1) p2) s2)))
  (D2 (Triple (LG p1 D0 s1)) (Triple (RG p2 d2 s2))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) d2 s2))
  (D2 (Triple (LG p1 D0 s1)) (Triple (RR p2 d2 s2))) -> only (Triple (OXR (catenateB (catenateB p1 s1) p2) d2 s2))
  (D2 (Triple (LG p1 D0 s1)) (Cap (RO p2 d2 s2) c)) -> only (Cap (OXO (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (LG p1 D0 s1)) (Cap (RY p2 d2 s2) c)) -> only (Cap (OGY (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (L0 p1 s1)) (Triple (R0 p2 s2@B9{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (L0 p1 s1)) (Triple (R0 p2 s2@B8{}))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) D0 s2))
  (D2 (Triple (L0 p1 s1)) (Triple (R0 p2 s2))) -> only (Triple (O0 (catenateB (catenateB (catenateB p1 s1) p2) s2)))
  (D2 (Triple (L0 p1 s1)) (Triple (RG p2 d2 s2))) -> only (Triple (OGG (catenateB (catenateB p1 s1) p2) d2 s2))
  (D2 (Triple (L0 p1 s1)) (Triple (RR p2 d2 s2))) -> only (Triple (OXR (catenateB (catenateB p1 s1) p2) d2 s2))
  (D2 (Triple (L0 p1 s1)) (Cap (RO p2 d2 s2) c)) -> only (Cap (OXO (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (L0 p1 s1)) (Cap (RY p2 d2 s2) c)) -> only (Cap (OGY (catenateB (catenateB p1 s1) p2) d2 s2) c)
  (D2 (Triple (LG p1 d1 s1)) (Triple (RG p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ injectWith d1 (S3 (catenateB s1 p2) d2 rem2) $ (\e -> LG p1 e (B2 s2r2 s2r1))
  (D2 (Triple (LG p1 d1 s1)) (Triple (RR p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ injectWith d1 (S3 (catenateB s1 p2) d2 rem2) $ (\e -> LG p1 e (B2 s2r2 s2r1))
  (D2 (Triple (LG p1 d1 s1)) (Triple (R0 p2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ injectWith d1 (S3 (catenateB s1 p2) D0 rem2) $ (\e -> LG p1 e (B2 s2r2 s2r1))
  (D2 (Triple (LG p1 d1 s1)) (Cap (RY p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ injectWith d1 (S3 (catenateB s1 p2) (plugL c d2) rem2) $ (\e -> LG p1 e (B2 s2r2 s2r1))
  (D2 (Triple (LG p1 d1 s1)) (Cap (RO p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ injectWith d1 (S3 (catenateB s1 p2) (plugR d2 c) rem2) $ (\e -> LG p1 e (B2 s2r2 s2r1))
  (D2 (Triple (LR p1 d1 s1)) (Triple (RG p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ LR p1 (inject d1 (S3 (catenateB s1 p2) d2 rem2)) (B2 s2r2 s2r1)
  (D2 (Triple (LR p1 d1 s1)) (Triple (RR p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ LR p1 (inject d1 (S3 (catenateB s1 p2) d2 rem2)) (B2 s2r2 s2r1)
  (D2 (Triple (LR p1 d1 s1)) (Triple (R0 p2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ LR p1 (inject d1 (S3 (catenateB s1 p2) D0 rem2)) (B2 s2r2 s2r1)
  (D2 (Triple (LR p1 d1 s1)) (Cap (RY p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ LR p1 (inject d1 (S3 (catenateB s1 p2) (plugL c d2) rem2)) (B2 s2r2 s2r1)
  (D2 (Triple (LR p1 d1 s1)) (Cap (RO p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> f $ Triple $ LR p1 (inject d1 (S3 (catenateB s1 p2) (plugR d2 c) rem2)) (B2 s2r2 s2r1)
  (D2 (Cap (LY p1 d1 s1) cl) (Triple (RG p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight d1r (S3 (catenateB s1 p2) d2 rem2) $ (\e -> f $ Cap (LY p1 (D2 d1l e) (B2 s2r2 s2r1)) cl)
    DOL ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) d2 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LY p1 d1 s1) cl) (Triple (RR p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight d1r (S3 (catenateB s1 p2) d2 rem2) $ (\e -> f $ Cap (LY p1 (D2 d1l e) (B2 s2r2 s2r1)) cl)
    DOL ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) d2 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LY p1 d1 s1) cl) (Triple (R0 p2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight d1r (S3 (catenateB s1 p2) D0 rem2) $ (\e -> f $ Cap (LY p1 (D2 d1l e) (B2 s2r2 s2r1)) cl)
    DOL ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) D0 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LY p1 d1 s1) cl) (Cap (RY p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight d1r (S3 (catenateB s1 p2) (plugL c d2) rem2) $ (\e -> f $ Cap (LY p1 (D2 d1l e) (B2 s2r2 s2r1)) cl)
    DOL ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugL c d2) rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LY p1 d1 s1) cl) (Cap (RO p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight d1r (S3 (catenateB s1 p2) (plugR d2 c) rem2) $ (\e -> f $ Cap (LY p1 (D2 d1l e) (B2 s2r2 s2r1)) cl)
    DOL ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugR d2 c) rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Triple (RG p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight (cap d1r cl) (S3 (catenateB s1 p2) d2 rem2) $ \e -> case uncap e of ViewCap d1r' c2 -> f $ Cap (LO p1 (D2 d1l d1r') (B2 s2r2 s2r1)) c2
    DOR ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) d2 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LO p1 (DOR ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Triple (RR p2 d2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight (cap d1r cl) (S3 (catenateB s1 p2) d2 rem2) $ \e -> case uncap e of ViewCap d1r' c2 -> f $ Cap (LO p1 (D2 d1l d1r') (B2 s2r2 s2r1)) c2
    DOR ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) d2 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LO p1 (DOR ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Triple (R0 p2 s2))) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight (cap d1r cl) (S3 (catenateB s1 p2) D0 rem2) $ \e -> case uncap e of ViewCap d1r' c2 -> f $ Cap (LO p1 (D2 d1l d1r') (B2 s2r2 s2r1)) c2
    DOR ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) D0 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LO p1 (DOR ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Cap (RY p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight (cap d1r cl) (S3 (catenateB s1 p2) (plugL c d2) rem2) $ \e -> case uncap e of ViewCap d1r' c2 -> f $ Cap (LO p1 (D2 d1l d1r') (B2 s2r2 s2r1)) c2
    DOR ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugL c d2) rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LO p1 (DOR ot2) (B2 s2r2 s2r1)) c2
  (D2 (Cap (LO p1 d1 s1) cl) (Cap (RO p2 d2 s2) c)) -> aux s2 $ \rem2 s2r2 s2r1 -> case d1 of
    D2 d1l d1r -> injectRight (cap d1r cl) (S3 (catenateB s1 p2) (plugR d2 c) rem2) $ \e -> case uncap e of ViewCap d1r' c2 -> f $ Cap (LO p1 (D2 d1l d1r') (B2 s2r2 s2r1)) c2
    DOR ot -> injectOnly (cap ot cl) (S3 (catenateB s1 p2) (plugR d2 c) rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LO p1 (DOR ot2) (B2 s2r2 s2r1)) c2
  where
    aux :: Buffer F F F F c5 c6 c7 c8 c9 q i l -> (forall k3 k4 k5 k6 k7 k8 k9 j' k. Buffer F F k3 k4 k5 k6 k7 k8 k9 q k l -> q j' k-> q i j' -> h) -> h
    aux s2 h = case ejectB s2 of
      H (Shift rem1) s2r1 -> case ejectB rem1 of
        H (Shift rem2) s2r2 -> h rem2 s2r2 s2r1
      H (NoShift rem1) s2r1 -> case ejectB rem1 of
        H (Shift rem2) s2r2 -> h rem2 s2r2 s2r1
        H (NoShift rem2) s2r2 -> h rem2 s2r2 s2r1

    only :: Cap OnlyTriple (Closed cl'') q i j -> g --Cap LeftTriple (Closed Green) q i j
    only (Triple O0{}) = error "Impossible"
    only (Triple (OGG p1 D0 s1)) = onlyPS p1 s1
    only (Triple (ORX p1 D0 s1)) = onlyPS p1 s1
    only (Triple (OXR p1 D0 s1)) = onlyPS p1 s1
    only (Triple (OGG p1 d1 s1)) = f $ case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple $ injectWith d1 (S1 rem2) $ (\e -> LG p1 e (B2 s1r2 s1r1))
           H (NoShift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple $ injectWith d1 (S1 rem2) $ (\e -> LG p1 e (B2 s1r2 s1r1))
             H (NoShift rem2) s1r2 -> Triple $ injectWith d1 (S1 rem2) $ (\e -> LG p1 e (B2 s1r2 s1r1))
    only (Triple (ORX p1 d1 s1)) = f $ case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple $ LR p1 (inject d1 (S1 rem2)) (B2 s1r2 s1r1)
           H (NoShift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> Triple $ LR p1 (inject d1 (S1 rem2)) (B2 s1r2 s1r1)
             H (NoShift rem2) s1r2 -> Triple $ LR p1 (inject d1 (S1 rem2)) (B2 s1r2 s1r1)
    only (Triple (OXR p1@B6{} d1 s1)) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case inject d1 (S1 rem2) of
                 D0 -> error "Impossible"
                 (D2 lt rt) -> case uncap rt of ViewCap rt2 c2 -> f $ Cap (LO p1 (D2 lt rt2) (B2 s1r2 s1r1)) c2
                 (DOL ot) -> case uncap ot of ViewCap ot2 c2 -> f $ Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
                 (DOR ot) -> case uncap ot of ViewCap ot2 c2 -> f $ Cap (LO p1 (DOR ot2) (B2 s1r2 s1r1)) c2
    only (Triple (OXR p1@B7{} d1 s1)) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> injectWith d1 (S1 rem2) $ \foo -> case foo of
                 D0 -> error "Impossible"
                 (D2 lt rt) -> case uncap lt of ViewCap lt2 c2 -> f $ Cap (LY p1 (D2 lt2 rt) (B2 s1r2 s1r1)) c2
                 (DOL ot) -> case uncap ot of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
                 (DOR ot) -> case uncap ot of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
    only (Triple (OXR p1@B8{} d1 s1)) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> injectWith d1 (S1 rem2) $ \e -> f $ Triple (LG p1 e (B2 s1r2 s1r1))
    only (Triple (OXR p1@B9{} d1 s1)) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> injectWith d1 (S1 rem2) $ \e -> f $ Triple (LG p1 e (B2 s1r2 s1r1))

    only (Cap (OOX p1 d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case (plugR d1 c) of -- (S1 rem2) foo
               D2 lt rt -> injectRight rt (S1 rem2) $ \rt2 -> case uncap rt2 of ViewCap rt3 c3 -> f $ Cap (LO p1 (D2 lt rt3) (B2 s1r2 s1r1)) c3
               DOL ot -> injectOnly ot (S1 rem2) $ \ot2 -> case uncap ot2 of ViewCap ot3 c3 -> f $ Cap (LO p1 (DOR ot3) (B2 s1r2 s1r1)) c3
               DOR ot -> injectOnly ot (S1 rem2) $ \ot2 -> case uncap ot2 of ViewCap ot3 c3 -> f $ Cap (LO p1 (DOR ot3) (B2 s1r2 s1r1)) c3
               D0 -> error "Impossible"
           H (NoShift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case (plugR d1 c) of -- (S1 rem2) foo
               D2 lt rt -> injectRight rt (S1 rem2) $ \rt2 -> case uncap rt2 of ViewCap rt3 c3 -> f $ Cap (LO p1 (D2 lt rt3) (B2 s1r2 s1r1)) c3
               DOL ot -> injectOnly ot (S1 rem2) $ \ot2 -> case uncap ot2 of ViewCap ot3 c3 -> f $ Cap (LO p1 (DOR ot3) (B2 s1r2 s1r1)) c3
               DOR ot -> injectOnly ot (S1 rem2) $ \ot2 -> case uncap ot2 of ViewCap ot3 c3 -> f $ Cap (LO p1 (DOR ot3) (B2 s1r2 s1r1)) c3
               D0 -> error "Impossible"
             H (NoShift rem2) s1r2 -> case (plugR d1 c) of -- (S1 rem2) foo
               D2 lt rt -> injectRight rt (S1 rem2) $ \rt2 -> case uncap rt2 of ViewCap rt3 c3 -> f $ Cap (LO p1 (D2 lt rt3) (B2 s1r2 s1r1)) c3
               DOL ot -> injectOnly ot (S1 rem2) $ \ot2 -> case uncap ot2 of ViewCap ot3 c3 -> f $ Cap (LO p1 (DOR ot3) (B2 s1r2 s1r1)) c3
               DOR ot -> injectOnly ot (S1 rem2) $ \ot2 -> case uncap ot2 of ViewCap ot3 c3 -> f $ Cap (LO p1 (DOR ot3) (B2 s1r2 s1r1)) c3
               D0 -> error "Impossible"
    only (Cap (OXO p1@B7{} d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> injectWith (plugR d1 c) (S1 rem2) $ \foo -> case foo of
                 D0 -> error "Impossible"
                 (D2 lt rt) -> case uncap lt of ViewCap lt2 c2 -> f $ Cap (LY p1 (D2 lt2 rt) (B2 s1r2 s1r1)) c2
                 (DOL ot) -> case uncap ot of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
                 (DOR ot) -> case uncap ot of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
    only (Cap (OXO p1@B8{} d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> injectWith (plugR d1 c) (S1 rem2) $ \e -> f $ Triple (LG p1 e (B2 s1r2 s1r1))
    only (Cap (OXO p1@B9{} d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> injectWith (plugR d1 c) (S1 rem2) $ \e -> f $ Triple (LG p1 e (B2 s1r2 s1r1))
    only (Cap (OYX p1 d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> case uncap lt of ViewCap lt2 c2 -> f $ Cap (LY p1 (D2 lt2 e) (B2 s1r2 s1r1)) c2
               DOL ot -> injectOnly ot (S1 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
           H (NoShift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> case uncap lt of ViewCap lt2 c2 -> f $ Cap (LY p1 (D2 lt2 e) (B2 s1r2 s1r1)) c2
               DOL ot -> injectOnly ot (S1 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
             H (NoShift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> case uncap lt of ViewCap lt2 c2 -> f $ Cap (LY p1 (D2 lt2 e) (B2 s1r2 s1r1)) c2
               DOL ot -> injectOnly ot (S1 rem2) $ \e -> case uncap e of ViewCap ot2 c2 -> f $ Cap (LY p1 (DOL ot2) (B2 s1r2 s1r1)) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
    only (Cap (OGY p1 d1 s1) c) = case ejectB s1 of
           H (Shift rem1) s1r1 -> case ejectB rem1 of
             H (Shift rem2) s1r2 -> case plugL c d1 of
               D2 lt rt -> injectRight rt (S1 rem2) $ \e -> f $ Triple (LG p1 (D2 lt e) (B2 s1r2 s1r1))
               DOL ot -> injectOnly ot (S1 rem2) $ \e -> f $ Triple (LG p1 (DOL e) (B2 s1r2 s1r1))
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"

    onlyPS :: Buffer F F F F a5 a6 a7 a8 a9 q j' j -> Buffer F F F F b5 b6 b7 b8 b9 q i j' -> g -- LeftTriple (Closed Green) q i k
    onlyPS p1 s1@B9{} = case popB s1 of
        H s1l1 (Shift rem1) -> case popB rem1 of
          H s1l2 (Shift rem2) -> case popB rem2 of
            H s1l3 (Shift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> f $ Triple $ LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = injectB (injectB (injectB p1 s1l1) s1l2) s1l3
                    s2 = B2 s1r2 s1r1
        H s1l1 (NoShift rem1) -> case popB rem1 of
          H s1l2 (Shift rem2) -> case popB rem2 of
            H s1l3 (Shift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> f $ Triple $ LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
          H s1l2 (NoShift rem2) -> case popB rem2 of
            H s1l3 (Shift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> f $ Triple $ LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
            H s1l3 (NoShift rem3) -> case ejectB rem3 of
              H (Shift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> f $ Triple $ LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
              H (NoShift rem4) s1r1 -> case ejectB rem4 of
                H (Shift rem5) s1r2 -> f $ Triple $ LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
                H (NoShift rem5) s1r2 -> f $ Triple $ LG p1' (push (S1 rem5) D0) s2
                  where
                    p1' = flip injectB s1l3 $ flip injectB s1l2 $ flip injectB s1l1 p1
                    s2 = B2 s1r2 s1r1
    onlyPS p1 s1 = case ejectB s1 of
      H (Shift rem1) s1r1 -> case ejectB rem1 of
        H (Shift rem2) s1r2 -> f $ Triple $ LG (catenateB p1 rem2) D0 (B2 s1r2 s1r1)
      H (NoShift rem1) s1r1 -> case ejectB rem1 of
        H (Shift rem2) s1r2 -> f $ Triple $ LG (catenateB p1 rem2) D0 (B2 s1r2 s1r1)
        H (NoShift rem2) s1r2 -> f $ Triple $ LG (catenateB p1 rem2) D0 (B2 s1r2 s1r1)


fixRight :: Deque (Closed Green) (Closed Green) q i j -> Cap RightTriple (Closed Green) q i j
fixRight d = case d of
  D0 -> error "Impossible"
  (DOL c) -> only c
  (DOR c) -> only c
  (D2 (Triple (L0 p2@B9{} s2)) (Triple (RG p1 D0 s1))) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  (D2 (Triple (L0 p2@B8{} s2)) (Triple (RG p1 D0 s1))) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  (D2 (Triple (L0 p2 s2))      (Triple (RG p1 D0 s1))) -> only (Triple (O0 (catenateB p2 (catenateB s2 (catenateB p1 s1)))))
  (D2 (Triple (LG p2 d2 s2))    (Triple (RG p1 D0 s1))) -> only (Triple (OGG p2 d2 (catenateB s2 (catenateB p1 s1))))
  (D2 (Cap (LO p2 d2 s2) c)     (Triple (RG p1 D0 s1))) -> only (Cap (OOX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  (D2 (Cap (LY p2 d2 s2) c)     (Triple (RG p1 D0 s1))) -> only (Cap (OYX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  (D2 (Triple (L0 p2@B9{} s2)) (Triple (R0 p1 s1))) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  (D2 (Triple (L0 p2@B8{} s2)) (Triple (R0 p1 s1))) -> only (Triple (OGG p2 D0 (catenateB s2 (catenateB p1 s1))))
  (D2 (Triple (L0 p2 s2))      (Triple (R0 p1 s1))) -> only (Triple (O0 (catenateB p2 (catenateB s2 (catenateB p1 s1)))))
  (D2 (Triple (LG p2 d2 s2))    (Triple (R0 p1 s1))) -> only (Triple (OGG p2 d2 (catenateB s2 (catenateB p1 s1))))
  (D2 (Cap (LO p2 d2 s2) c)     (Triple (R0 p1 s1))) -> only (Cap (OOX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  (D2 (Cap (LY p2 d2 s2) c)     (Triple (R0 p1 s1))) -> only (Cap (OYX p2 d2 (catenateB (catenateB s2 p1) s1)) c)
  (D2 (Triple (LG p2 d2 s2)) (Triple (RG p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> Triple $ pushWith (S3 rem2 d2 (catenateB s2 p1)) d1 $ \e -> RG (B2 p2l1 p2l2) e s1
  (D2 (Triple (L0 p2 s2))    (Triple (RG p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> Triple $ pushWith (S3 rem2 D0 (catenateB s2 p1))           d1 $ \e -> RG (B2 p2l1 p2l2) e s1
  (D2 (Cap (LY p2 d2 s2) c)  (Triple (RG p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> Triple $ pushWith (S3 rem2 (plugL c d2) (catenateB s2 p1)) d1 $ \e -> RG (B2 p2l1 p2l2) e s1
  (D2 (Cap (LO p2 d2 s2) c)  (Triple (RG p1 d1 s1))) -> aux p2 $ \p2l1 p2l2 rem2 -> Triple $ pushWith (S3 rem2 (plugR d2 c) (catenateB s2 p1)) d1 $ \e -> RG (B2 p2l1 p2l2) e s1
  (D2 (Triple (LG p2 d2 s2)) (Cap (RO p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> Cap (RO (B2 p2l1 p2l2) (D2 (pushLeftG (S3 rem2 d2 (catenateB s2 p1)) d1l) d1r) s1) cl
    DOR ot -> case uncap (pushOnlyG (S3 rem2 d2 (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RO (B2 p2l1 p2l2) (DOR ot2) s1) c2
  (D2 (Triple (L0 p2 s2)) (Cap (RO p1 d1 s1) cl)) ->    aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> Cap (RO (B2 p2l1 p2l2) (D2 (pushLeftG (S3 rem2 D0 (catenateB s2 p1)) d1l) d1r) s1) cl
    DOR ot -> case uncap (pushOnlyG (S3 rem2 D0 (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RO (B2 p2l1 p2l2) (DOR ot2) s1) c2
  (D2 (Cap (LY p2 d2 s2) cr) (Cap (RO p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> Cap (RO (B2 p2l1 p2l2) (D2 (pushLeftG (S3 rem2 (plugL cr d2) (catenateB s2 p1)) d1l) d1r) s1) cl
    DOR ot -> case uncap (pushOnlyG (S3 rem2 (plugL cr d2) (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RO (B2 p2l1 p2l2) (DOR ot2) s1) c2
  (D2 (Cap (LO p2 d2 s2) cr) (Cap (RO p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> Cap (RO (B2 p2l1 p2l2) (D2 (pushLeftG (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) d1l) d1r) s1) cl
    DOR ot -> case uncap (pushOnlyG (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RO (B2 p2l1 p2l2) (DOR ot2) s1) c2
  (D2 (Triple (LG p2 d2 s2)) (Cap (RY p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> case uncap (pushLeftG (S3 rem2 d2 (catenateB s2 p1)) (cap d1l cl)) of ViewCap d1l' c2 -> Cap (RY (B2 p2l1 p2l2) (D2 d1l' d1r) s1) c2
    DOL ot -> case uncap (pushOnlyG (S3 rem2 d2 (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RY (B2 p2l1 p2l2) (DOL ot2) s1) c2
  (D2 (Triple (L0 p2 s2)) (Cap (RY p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> case uncap (pushLeftG (S3 rem2 D0 (catenateB s2 p1)) (cap d1l cl)) of ViewCap d1l' c2 -> Cap (RY (B2 p2l1 p2l2) (D2 d1l' d1r) s1) c2
    DOL ot -> case uncap (pushOnlyG (S3 rem2 D0 (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RY (B2 p2l1 p2l2) (DOL ot2) s1) c2
  (D2 (Cap (LY p2 d2 s2) cr) (Cap (RY p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> case uncap (pushLeftG (S3 rem2 (plugL cr d2) (catenateB s2 p1)) (cap d1l cl)) of ViewCap d1l' c2 -> Cap (RY (B2 p2l1 p2l2) (D2 d1l' d1r) s1) c2
    DOL ot -> case uncap (pushOnlyG (S3 rem2 (plugL cr d2) (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RY (B2 p2l1 p2l2) (DOL ot2) s1) c2
  (D2 (Cap (LO p2 d2 s2) cr) (Cap (RY p1 d1 s1) cl)) -> aux p2 $ \p2l1 p2l2 rem2 -> case d1 of
    D2 d1l d1r -> case uncap (pushLeftG (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) (cap d1l cl)) of ViewCap d1l' c2 -> Cap (RY (B2 p2l1 p2l2) (D2 d1l' d1r) s1) c2
    DOL ot -> case uncap (pushOnlyG (S3 rem2 (plugR d2 cr) (catenateB s2 p1)) (cap ot cl)) of ViewCap ot2 c2 -> Cap (RY (B2 p2l1 p2l2) (DOL ot2) s1) c2
  where
    aux :: Buffer F F F F c5 c6 c7 c8 c9 q i l -> (forall k3 k4 k5 k6 k7 k8 k9 j k. q k l -> q j k-> Buffer F F k3 k4 k5 k6 k7 k8 k9 q i j -> g) -> g
    aux p1 f = case popB p1 of
      H p1l1 (Shift rem1) -> case popB rem1 of
        H p1l2 (Shift rem2) -> f p1l1 p1l2 rem2
      H p1l1 (NoShift rem1) -> case popB rem1 of
        H p1l2 (Shift rem2) -> f p1l1 p1l2 rem2
        H p1l2 (NoShift rem2) -> f p1l1 p1l2 rem2

    only :: Cap OnlyTriple (Closed Green) q i j -> Cap RightTriple (Closed Green) q i j
    only (Triple O0{}) = error "Impossible"
    only (Triple (OGG p1 D0 s1)) = Triple (onlyPS p1 s1)
    only (Triple (OGG p1 d1 s1)) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> Triple $ pushWith (S1 rem2) d1 $ \e -> RG (B2 p1l1 p1l2) e s1
           H p1l1 (NoShift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> Triple $ pushWith (S1 rem2) d1 $ \e -> RG (B2 p1l1 p1l2) e s1
             H p1l2 (NoShift rem2) -> Triple $ pushWith (S1 rem2) d1 $ \e -> RG (B2 p1l1 p1l2) e s1
    only (Cap (OOX p1 d1 s1@B6{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> foo $ push (S1 rem2) (plugR d1 c)
               where
                 foo (D2 lt rt) = case uncap rt of ViewCap rt2 c2 -> Cap (RO (B2 p1l1 p1l2) (D2 lt rt2) s1) c2
                 foo (DOL ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo (DOR ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo D0 = error "Impossible"
    only (Cap (OOX p1 d1 s1@B7{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> foo $ push (S1 rem2) (plugR d1 c)
               where
                 foo (D2 lt rt) = case uncap lt of ViewCap lt2 c2 -> Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) c2
                 foo (DOL ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
                 foo (DOR ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
                 foo D0 = error "Impossible"
    only (Cap (OOX p1 d1 s1@B8{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> Triple (RG (B2 p1l1 p1l2) (push (S1 rem2) (plugR d1 c)) s1)
    only (Cap (OOX p1 d1 s1@B9{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> Triple (RG (B2 p1l1 p1l2) (push (S1 rem2) (plugR d1 c)) s1)
    only (Cap (OXO p1 d1 s1) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> foo $ push (S1 rem2) (plugR d1 c)
               where
                 foo (D2 lt rt) = case uncap rt of ViewCap rt2 c2 -> Cap (RO (B2 p1l1 p1l2) (D2 lt rt2) s1) c2
                 foo (DOL ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo (DOR ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo D0 = error "Impossible"
           H p1l1 (NoShift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> foo $ push (S1 rem2) (plugR d1 c)
               where
                 foo (D2 lt rt) = case uncap rt of ViewCap rt2 c2 -> Cap (RO (B2 p1l1 p1l2) (D2 lt rt2) s1) c2
                 foo (DOL ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo (DOR ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo D0 = error "Impossible"
             H p1l2 (NoShift rem2) -> foo $ push (S1 rem2) (plugR d1 c)
               where
                 foo (D2 lt rt) = case uncap rt of ViewCap rt2 c2 -> Cap (RO (B2 p1l1 p1l2) (D2 lt rt2) s1) c2
                 foo (DOL ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo (DOR ot)   = case uncap ot of ViewCap ot2 c2 -> Cap (RO (B2 p1l1 p1l2) (DOR ot2) s1) c2
                 foo D0 = error "Impossible"
    only (Cap (OYX p1 d1 s1@B7{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case plugL c d1 of
               D2 lt rt -> case uncap (pushLeftG (S1 rem2) lt) of ViewCap lt2 c2 -> Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) c2
               DOL ot -> case uncap (pushOnlyG (S1 rem2) ot) of ViewCap ot2 c2 -> Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
    only (Cap (OYX p1 d1 s1@B8{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> pushWith (S1 rem2) (plugL c d1) $ \e -> Triple (RG (B2 p1l1 p1l2) e s1)
    only (Cap (OYX p1 d1 s1@B9{}) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> pushWith (S1 rem2) (plugL c d1) $ \e -> Triple (RG (B2 p1l1 p1l2) e s1)
    only (Cap (OGY p1 d1 s1) c) = case popB p1 of
           H p1l1 (Shift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case plugL c d1 of
               D2 lt rt -> case uncap (pushLeftG (S1 rem2) lt) of ViewCap lt2 c2 -> Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) c2
               DOL ot -> case uncap (pushOnlyG (S1 rem2) ot) of ViewCap ot2 c2 -> Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
           H p1l1 (NoShift rem1) -> case popB rem1 of
             H p1l2 (Shift rem2) -> case plugL c d1 of
               D2 lt rt -> case uncap (pushLeftG (S1 rem2) lt) of ViewCap lt2 c2 -> Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) c2
               DOL ot -> case uncap (pushOnlyG (S1 rem2) ot) of ViewCap ot2 c2 -> Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"
             H p1l2 (NoShift rem2) -> case plugL c d1 of
               D2 lt rt -> case uncap (pushLeftG (S1 rem2) lt) of ViewCap lt2 c2 -> Cap (RY (B2 p1l1 p1l2) (D2 lt2 rt) s1) c2
               DOL ot -> case uncap (pushOnlyG (S1 rem2) ot) of ViewCap ot2 c2 -> Cap (RY (B2 p1l1 p1l2) (DOL ot2) s1) c2
               DOR _ -> error "Impossible"
               D0 -> error "Impossible"

    onlyPS :: Buffer F F F F F F F a8 a9 q j k -> Buffer F F F F F F F b8 b9 q i j -> RightTriple (Closed Green) q i k
    onlyPS p1@B9{} s1 = case ejectB p1 of
        H (Shift rem1) p1r1 -> case ejectB rem1 of
          H (Shift rem2) p1r2 -> case ejectB rem2 of
            H (Shift rem3) p1r3 -> case popB rem3 of
              H p1l1 (Shift rem4) -> case popB rem4 of
                H p1l2 (Shift rem5) -> RG p2 (push (S1 rem5) D0) s2
                  where
                    p2 = B2 p1l1 p1l2
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
        H (NoShift rem1) p1r1 -> case ejectB rem1 of
          H (Shift rem2) p1r2 -> case ejectB rem2 of
            H (Shift rem3) p1r3 -> case popB rem3 of
              H p1l1 (Shift rem4) -> case popB rem4 of
                H p1l2 (Shift rem5) -> RG p2 (push (S1 rem5) D0) s2
                  where
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
                    p2 = B2 p1l1 p1l2
          H (NoShift rem2) p1r2 -> case ejectB rem2 of
            H (Shift rem3) p1r3 -> case popB rem3 of
              H p1l1 (Shift rem4) -> case popB rem4 of
                H p1l2 (Shift rem5) -> RG p2 (push (S1 rem5) D0) s2
                  where
                    p2 = B2 p1l1 p1l2
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
            H (NoShift rem3) p1r3 -> case popB rem3 of
              H p1l1 (Shift rem4) -> case popB rem4 of
                H p1l2 (Shift rem5) -> RG p2 (push (S1 rem5) D0) s2
                  where
                    p2 = B2 p1l1 p1l2
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
              H p1l1 (NoShift rem4) -> case popB rem4 of
                H p1l2 (Shift rem5) -> RG p2 (push (S1 rem5) D0) s2
                  where
                    p2 = B2 p1l1 p1l2
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
                H p1l2 (NoShift rem5) -> RG p2 (push (S1 rem5) D0) s2
                  where
                    p2 = B2 p1l1 p1l2
                    s2 = pushB p1r3 (pushB p1r2 (pushB p1r1 s1))
    onlyPS p1 s1 = case popB p1 of
      H p1l1 (Shift rem1) -> case popB rem1 of
        H p1l2 (Shift rem2) -> RG (B2 p1l1 p1l2) D0 (catenateB rem2 s1)
      H p1l1 (NoShift rem1) -> case popB rem1 of
        H p1l2 (Shift rem2) -> RG (B2 p1l1 p1l2) D0 (catenateB rem2 s1)
        H p1l2 (NoShift rem2) -> RG (B2 p1l1 p1l2) D0 (catenateB rem2 s1)

data ClosedDeque q i j where
  CD :: Deque (Closed lg) (Closed rg) q i j -> ClosedDeque q i j

data View l r a c where
  Empty :: View l r a a
  (:|) :: l b c -> r a b -> View l r a c

popNoRepair :: Deque (Closed Green) (Closed Green) q i j -> View q (ClosedDeque q) i j
popNoRepair d = case d of
  D0 -> Empty
  D2 (Triple (LG p1 d1 s1)) rt -> case popB p1 of
    H p1l1 (Shift rem1@B7{}) -> case d1 of
      D2 lt2 rt2 -> case uncap lt2 of ViewCap lt3 cap3 -> p1l1 :| (CD $ D2 (Cap (LY rem1 (D2 lt3 rt2) s1) cap3) rt)
      DOL ot -> case uncap ot of ViewCap ot2 cap2 -> p1l1 :| (CD $ D2 (Cap (LY rem1 (DOL ot2) s1) cap2) rt)
      DOR ot -> case uncap ot of ViewCap ot2 cap2 -> p1l1 :| (CD $ D2 (Cap (LY rem1 (DOL ot2) s1) cap2) rt)
      D0 -> p1l1 :| (CD $ D2 (Triple (L0 rem1 s1)) rt)
    H p1l1 (Shift rem1@B8{}) -> p1l1 :| (CD $ D2 (Triple (LG rem1 d1 s1)) rt)
    H p1l1 (NoShift rem1) -> p1l1 :| (CD $ D2 (Triple (LG rem1 d1 s1)) rt)
  D2 (Cap (LY p1 d1 s1) cap1) rt -> case popB p1 of
    H p1l1 (Shift rem1) -> case d1 of
      D2 lt2 rt2 -> case uncap rt2 of ViewCap rt3 cap3 -> p1l1 :| (CD $ D2 (Cap (LO rem1 (D2 (cap lt2 cap1) rt3) s1) cap3) rt)
      DOL ot -> p1l1 :| (CD $ D2 (Cap (LO rem1 (DOR ot) s1) cap1) rt)
  D2 (Cap (LO p1 d1 s1) cap1) rt -> case popB p1 of
    H p1l1 (Shift rem1) -> case d1 of
      D2 lt2 rt2 -> p1l1 :| (CD $ D2 (Triple (LR rem1 (D2 lt2 (cap rt2 cap1)) s1)) rt)
      DOR ot -> p1l1 :| (CD $ D2 (Triple (LR rem1 (DOR (cap ot cap1)) s1)) rt)
  D2 (Triple (L0 p1 s1)) rt -> case popB p1 of
    H p1l1 (Shift rem1@B4{}) -> case rt of
      Triple (R0 lt2 rt2) -> p1l1 :| (CD $ DOL (Triple (O0 (catenateB rem1 (catenateB s1 (catenateB lt2 rt2))))))
      Triple (RG lt2 d2 rt2) -> p1l1 :| (CD $ DOL (Triple (OGG (catenateB rem1 (catenateB s1 lt2)) d2 rt2)))
      Cap (RY lt2 d2 rt2) cap2 -> p1l1 :| (CD $ DOL (Cap (OGY (catenateB rem1 (catenateB s1 lt2)) d2 rt2) cap2))
      Cap (RO lt2 d2 rt2) cap2 -> p1l1 :| (CD $ DOL (Cap (OXO (catenateB rem1 (catenateB s1 lt2)) d2 rt2) cap2))
    H p1l1 (Shift rem1@B5{}) -> p1l1 :| (CD $ D2 (Triple (L0 rem1 s1)) rt)
    H p1l1 (Shift rem1@B6{}) -> p1l1 :| (CD $ D2 (Triple (L0 rem1 s1)) rt)
    H p1l1 (Shift rem1@B7{}) -> p1l1 :| (CD $ D2 (Triple (L0 rem1 s1)) rt)
    H p1l1 (Shift rem1@B8{}) -> p1l1 :| (CD $ D2 (Triple (L0 rem1 s1)) rt)
    H p1l1 (NoShift rem1) -> p1l1 :| (CD $ D2 (Triple (L0 rem1 s1)) rt)
  DOL ot -> only ot
  DOR ot -> only ot
  where
    only :: Cap OnlyTriple (Closed Green) q i j -> View q (ClosedDeque q) i j
    only (Triple (O0 p1)) = case popB p1 of
      H p1l1 NoB -> p1l1 :| (CD D0)
      H p1l1 (Shift rem1) -> p1l1 :| (CD $ DOL (Triple (O0 rem1)))
      H p1l1 (NoShift rem1) -> p1l1 :| (CD $ DOL (Triple (O0 rem1)))
    only (Triple (OGG p1 d1 s1)) = case popB p1 of
      H p1l1 (Shift rem1@B7{}) -> case d1 of
        D2 lt2 rt2 -> case uncap lt2 of ViewCap lt3 cap3 -> p1l1 :| (CD $ DOL (Cap (OYX rem1 (D2 lt3 rt2) s1) cap3))
        DOL ot -> case uncap ot of ViewCap ot3 cap3 -> p1l1 :| (CD $ DOL (Cap (OYX rem1 (DOL ot3) s1) cap3))
        DOR ot -> case uncap ot of ViewCap ot3 cap3 -> p1l1 :| (CD $ DOL (Cap (OYX rem1 (DOL ot3) s1) cap3))
        D0 -> p1l1 :| (CD $ DOL (Triple (O0 (catenateB rem1 s1))))
      H p1l1 (Shift rem1@B8{}) -> p1l1 :| (CD $ DOL (Triple (OGG rem1 d1 s1)))
      H p1l1 (NoShift rem1) -> p1l1 :| (CD $ DOL (Triple (OGG rem1 d1 s1)))
    only (Cap (OOX p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> p1l1 :| (CD $ DOL (Triple (ORX rem1 (plugR d1 cap1) s1)))
    only (Cap (OXO p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1@B6{}) -> p1l1 :| (CD $ DOL (Cap (OOX rem1 d1 s1) cap1))
      H p1l1 (Shift rem1@B7{}) -> p1l1 :| (CD $ DOL (Cap (OXO rem1 d1 s1) cap1))
      H p1l1 (Shift rem1@B8{}) -> p1l1 :| (CD $ DOL (Cap (OXO rem1 d1 s1) cap1))
      H p1l1 (NoShift rem1)    -> p1l1 :| (CD $ DOL (Cap (OXO rem1 d1 s1) cap1))
    only (Cap (OYX p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> case d1 of
        D2 lt2 rt2 -> case uncap rt2 of ViewCap rt3 cap3 -> p1l1 :| (CD $ DOL (Cap (OOX rem1 (D2 (cap lt2 cap1) rt3) s1) cap3))
        DOL ot -> p1l1 :| (CD $ DOL (Cap (OOX rem1 (DOR ot) s1) cap1))
    only (Cap (OGY p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1@B7{}) -> p1l1 :| (CD $ DOL (Cap (OYX rem1 d1 s1) cap1))
      H p1l1 (Shift rem1@B8{}) -> p1l1 :| (CD $ DOL (Cap (OGY rem1 d1 s1) cap1))
      H p1l1 (NoShift rem1)    -> p1l1 :| (CD $ DOL (Cap (OGY rem1 d1 s1) cap1))

popThenPush :: forall lg lr q i k foo m. (Monad m) => Deque (Closed lg) (Closed lr) q i k -> (forall j. q j k -> m (HPair foo q j k)) -> m (View foo (Deque (Closed lg) (Closed lr) q) i k)
popThenPush d f = case d of
  D0 -> return Empty
  D2 (Triple (LG p1 d1 s1)) rt -> case popB p1 of
    H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo :| D2 (Triple (LG (pushB q rem1) d1 s1)) rt
    H p1l1 (NoShift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo :| D2 (Triple (LG (pushB q rem1) d1 s1)) rt
  D2 (Triple (L0 p1 s1)) rt -> case popB p1 of
    H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo :| D2 (Triple (L0 (pushB q rem1) s1)) rt
    H p1l1 (NoShift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo :| D2 (Triple (L0 (pushB q rem1) s1)) rt
  D2 (Triple (LR p1 d1 s1)) rt -> case popB p1 of
    H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo :| D2 (Triple (LR (pushB q rem1) d1 s1)) rt
  D2 (Cap (LY p1 d1 s1) cap1) rt -> case popB p1 of
    H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo :| D2 (Cap (LY (pushB q rem1) d1 s1) cap1) rt
  D2 (Cap (LO p1 d1 s1) cap1) rt -> case popB p1 of
    H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo :| D2 (Cap (LO (pushB q rem1) d1 s1) cap1) rt
  DOL ot -> only ot >>= \bar -> case bar of H foo c -> return $ foo :| DOL c
  DOR ot -> only ot >>= \bar -> case bar of H foo c -> return $ foo :| DOR c
  where
    only :: Cap OnlyTriple (Closed cl) q i' k -> m (HPair foo (Cap OnlyTriple (Closed cl) q) i' k)
    only (Triple (O0 p1)) = case popB p1 of
      H p1l1 NoB -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (O0 (B1 q)))
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (O0 (pushB q rem1)))
      H p1l1 (NoShift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (O0 (pushB q rem1)))
    only (Triple (OGG p1 d1 s1)) = case popB p1 of
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (OGG (pushB q rem1) d1 s1))
      H p1l1 (NoShift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (OGG (pushB q rem1) d1 s1))
    only (Triple (ORX p1 d1 s1)) = case popB p1 of
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (ORX (pushB q rem1) d1 s1))
    only (Triple (OXR p1 d1 s1)) = case popB p1 of
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (OXR (pushB q rem1) d1 s1))
      H p1l1 (NoShift rem1) -> f p1l1 >>= \bar -> case bar of  H foo q -> return $ foo `H` (Triple (OXR (pushB q rem1) d1 s1))
    only (Cap (OXO p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of H foo q -> return $ foo `H` (Cap (OXO (pushB q rem1) d1 s1) cap1)
      H p1l1 (NoShift rem1) -> f p1l1 >>= \bar -> case bar of H foo q -> return $ foo `H` (Cap (OXO (pushB q rem1) d1 s1) cap1)
    only (Cap (OOX p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of H foo q -> return $ foo `H` (Cap (OOX (pushB q rem1) d1 s1) cap1)
    only (Cap (OYX p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of H foo q -> return $ foo `H` (Cap (OYX (pushB q rem1) d1 s1) cap1)
    only (Cap (OGY p1 d1 s1) cap1) = case popB p1 of
      H p1l1 (Shift rem1) -> f p1l1 >>= \bar -> case bar of H foo q -> return $ foo `H` (Cap (OGY (pushB q rem1) d1 s1) cap1)
      H p1l1 (NoShift rem1) -> f p1l1 >>= \bar -> case bar of H foo q -> return $ foo `H` (Cap (OGY (pushB q rem1) d1 s1) cap1)

data SomeBuffer3 q j k where
  SB3 :: Buffer F F k3 k4 k5 k6 k7 k8 k9 q j k -> SomeBuffer3 q j k

{-
repairLeft :: Cap LeftTriple (Closed Red) q i j -> Cap LeftTriple (Closed Green) q i j
repairLeft (Triple (LR p1 d1 s1)) = case popThenPush d1 foo of
  Just ((H p2 d2) :| d1') -> Triple (LG (catenateB p1 p2) (catenate d2 d1') s1)
  where
    foo :: StoredTriple q j k -> Maybe (HPair (HPair (SommBuffer3 q) (
    foo (S1 _) = Nothing
    foo (S3 p2 d2 s2) = Just $ H (H (SB3 p2) d2) (S1 s2)
-}
-- Buffer F F k3 k4 k5 k6 k7 k8 k9 q l m) -> Deque (Closed lg) (Closed rg) (StoredTriple q) k l
data Foo a b where
  F :: !Int -> Foo () ()

instance NFData (Foo a b) where
  rnf !_ = ()

deriving instance Show (Foo a b)
