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

module Data.Deque.Cat where

import Data.Type.Bool
import qualified Data.Deque.NonCat as NC

type T = True
type F = False

data Buffer k1 k2 k3 k4 k5 k6 k7 k8 q i j where
  B1 :: !(q i j) -> Buffer T F F F F F F F q i j
  B2 :: !(q j k) -> !(q i j) -> Buffer F T F F F F F F q i k
  B3 :: !(q k l) -> !(q j k) -> !(q i j) -> Buffer F F T F F F F F q i l
  B4 :: !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer F F F T F F F F q i m
  B5 :: !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer F F F F T F F F q i n
  B6 :: !(q n o) -> !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer F F F F F T F F q i o
  B7 :: !(q o p) -> !(q n o) -> !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> Buffer F F F F F F T F q i p
  B8 :: !(NC.Deque q r s) -> !(q p r) -> !(q o p) -> !(q n o) -> !(q m n) -> !(q l m) -> !(q k l) -> !(q j k) -> !(q i j) -> !(NC.Deque q h i) -> Buffer F F F F F F F T q h s

data StoredTriple q i j where
  S1 :: Buffer F F k3 k4 k5 k6 k7 k8 q j k -> StoredTriple q j k
  S3 :: Buffer F F k3 k4 k5 k6 k7 k8 q l m -> Deque lg rg (StoredTriple q) k l -> Buffer F F c3 c4 c5 c6 c7 c8 q j k -> StoredTriple q j m

data OnlyTriple ge q i j where
  O0 :: Buffer k1 k2 k3 k4 k5 k6 k7 k8 q j k -> OnlyTriple (Closed Green) q j k
  ORX :: Buffer F F F F T F F F q l m -> Deque (Closed Green) (Closed Green) (StoredTriple q) k l -> Buffer F F F F c5 c6 c7 c8 q j k -> OnlyTriple (Closed Red) q j m
  OXR :: Buffer F F F F F k6 k7 k8 q l m -> Deque (Closed Green) (Closed Green) (StoredTriple q) k l -> Buffer F F F F T F F F q j k -> OnlyTriple (Closed Red) q j m
  OOX :: Buffer F F F F F T F F q l m -> Deque (Closed Green) (Open r s t u) (StoredTriple q) k l -> Buffer F F F F F c6 c7 c8 q j k -> Cap r s t u b -> OnlyTriple b q j m
  OXO :: Buffer F F F F F F k7 k8 q l m -> Deque (Closed Green) (Open r s t u) (StoredTriple q) k l -> Buffer F F F F F T F F q j k -> Cap r s t u b -> OnlyTriple b q j m
  OYX :: Buffer F F F F F F T F q l m -> Deque (Open r s t u) (Closed kr) (StoredTriple q) k l -> Buffer F F F F F F c7 c8 q j k -> Cap r s t u b -> OnlyTriple b q j m
  OGY :: Buffer F F F F F F F T q l m -> Deque (Open r s t u) (Closed kr) (StoredTriple q) k l -> Buffer F F F F F F T F q j k -> Cap r s t u b -> OnlyTriple b q j m
  OGG :: Buffer F F F F F F F T q l m -> Deque (Closed k1) (Closed k2) (StoredTriple q) k l -> Buffer F F F F F F F T q j k -> OnlyTriple (Closed Green) q j m

data LeftTriple ge q i j where
  L0 :: Buffer F F F F k5 k6 k7 k8 q l m -> Buffer F T F F F F F F q j k -> LeftTriple (Closed Green) q j m
  LR :: Buffer F F F F T F F F q l m -> Deque (Closed Green) (Closed Green) (StoredTriple q) k l -> Buffer F T F F F F F F q j k -> LeftTriple (Closed Red) q j m
  LO :: Buffer F F F F F T F F q l m -> Deque (Closed Green) (Open r s t u) (StoredTriple q) k l -> Buffer F T F F F F F F q j k -> Cap r s t u b -> LeftTriple b q j m
  LY :: Buffer F F F F F F T F q l m -> Deque (Open r s t u) (Closed cr) (StoredTriple q) k l -> Buffer F T F F F F F F q j k -> Cap r s t u b -> LeftTriple b q j m
  LG :: Buffer F F F F F F F T q l m -> Deque (Closed cl) (Closed cr) (StoredTriple q) k l -> Buffer F T F F F F F F q j k -> LeftTriple (Closed Green) q j m

data Cap r s t u b where
  NoCap :: Cap  r s t u (Open r s t u)
  Cap :: r (Closed k) s t u -> Cap r s t u (Closed k)

data Colour = Red | Green

data Genus k where
  Open :: (Genus k -> (k -> k -> k) -> k -> k -> k) -> (k -> k -> k) -> k -> k -> Genus k
  Closed :: Colour -> Genus k

data RightTriple ge q i j where
  R0 :: Buffer F T F F F F F F q l m -> Buffer F F F F k5 k6 k7 k8 q j k -> RightTriple (Closed Green) q j m
  RR :: Buffer F T F F F F F F q l m -> Deque (Closed Green) (Closed Green) (StoredTriple q) k l -> Buffer F F F F T F F F q j k -> RightTriple (Closed Red) q j m
  RO :: Buffer F T F F F F F F q l m -> Deque (Closed Green) (Open r s t u) (StoredTriple q) k l -> Buffer F F F F F T F F q j k -> Cap r s t u b -> RightTriple b q j m
  RY :: Buffer F T F F F F F F q l m -> Deque (Open r s t u) (Closed kr) (StoredTriple q) k l -> Buffer F F F F F F T F q j k -> Cap r s t u b -> RightTriple b q j m
  RG :: Buffer F T F F F F F F q l m -> Deque (Closed kl) (Closed kr) (StoredTriple q) k l -> Buffer F F F F F F F T q j k -> RightTriple (Closed Green) q j m

data Deque lg rg q i j where
  D0 :: Deque (Closed Green) (Closed Green) q i i
  D2 :: LeftTriple lg q j k -> RightTriple rg q i j -> Deque lg rg q i k
  DL :: LeftTriple (Closed c) q j k -> Deque (Closed c) (Open RightTriple q i j) q i k
  DR :: RightTriple (Closed c) q i j -> Deque (Open LeftTriple q j k) (Closed c) q i k
  DOL :: OnlyTriple b q i j -> Deque b (Closed Green) q i j
  DOR :: OnlyTriple b q i j -> Deque (Closed Green) b q i j
  DHL :: Deque (Open OnlyTriple q i j) (Closed Green) q i j
  DHR :: Deque (Closed Green) (Open OnlyTriple q i j) q i j

pushB :: q j k -> Buffer k1 k2 k3 k4 k5 k6 k7 k8 q i j -> Buffer F k1 k2 k3 k4 k5 k6 (k7 || k8) q i k
pushB = undefined

plugL :: Cap r s t u b -> Deque (Open r s t u) rg q i j -> Deque b rg q i j
plugL = undefined

plugR :: Deque lg (Open r s t u) q i j -> Cap r s t u b -> Deque lg b q i j
plugR = undefined

unplugL :: Deque (Closed cl) (Closed cr) q i j -> (Cap r s t u (Closed cl), Deque (Open r s t u) (Closed cr) q i j)
unplugL = undefined

unplugR :: Deque (Closed cl) (Closed cr) q i j -> (Deque (Closed cl) (Open r s t u) q i j, Cap r s t u (Closed cr))
unplugR = undefined

push :: q j k -> Deque (Closed Green) (Closed Green) q i j -> Deque (Closed Green) (Closed Green) q i k
push a D0 = DOL (O0 (B1 a))
push a (D2 (L0 bl br) r) = (D2 (L0 (pushB a bl) br) r)
push a (D2 (LO bl d br cap) r) = case unplugL (plugR d cap) of (cap2, d2) -> (D2 (LY (pushB a bl) d2 br cap2) r)
push a (D2 (LY bl d br cap) r) = (D2 (LG (pushB a bl) (plugL cap d) br) r)
push a (D2 (LG bl d br) r) = (D2 (LG (pushB a bl) d br) r)
push a (DOL (O0 b)) = DOL (O0 (pushB a b))
push a (DOL (OOX bl d br@B6{} cap)) = DOL (OXO (pushB a bl) d br cap)
push a (DOL (OOX bl d br@B7{} cap)) = case unplugL (plugR d cap) of (cap2, d2) -> DOL (OYX (pushB a bl) d2 br cap2)
push a (DOL (OOX bl d br@B8{} cap)) = case unplugL (plugR d cap) of (cap2, d2) -> DOL (OYX (pushB a bl) d2 br cap2) -- Why can't i write just one term for both of these?
push a (DOL (OXO bl d br cap)) = DOL (OXO (pushB a bl) d br cap)
push a (DOL (OYX bl d br@B7{} cap)) = DOL (OGY (pushB a bl) d br cap)
push a (DOL (OYX bl d br@B8{} cap)) = DOL (OGG (pushB a bl) (plugL cap d) br)
push a (DOL (OGY bl d br cap)) = DOL (OGY (pushB a bl) d br cap)
push a (DOL (OGG bl d br)) = DOL (OGG (pushB a bl) d br)
push a (DOR (O0 b)) = DOL (O0 (pushB a b))
push a (DOR (OOX bl d br@B6{} cap)) = DOL (OXO (pushB a bl) d br cap)
push a (DOR (OOX bl d br@B7{} cap)) = case unplugL (plugR d cap) of (cap2, d2) -> DOL (OYX (pushB a bl) d2 br cap2)
push a (DOR (OOX bl d br@B8{} cap)) = case unplugL (plugR d cap) of (cap2, d2) -> DOL (OYX (pushB a bl) d2 br cap2) -- Why can't i write just one term for both of these?
push a (DOR (OXO bl d br cap)) = DOL (OXO (pushB a bl) d br cap)
push a (DOR (OYX bl d br@B7{} cap)) = DOL (OGY (pushB a bl) d br cap)
push a (DOR (OYX bl d br@B8{} cap)) = DOL (OGG (pushB a bl) (plugL cap d) br)
push a (DOR (OGY bl d br cap)) = DOL (OGY (pushB a bl) d br cap)
push a (DOR (OGG bl d br)) = DOL (OGG (pushB a bl) d br)

catenateB :: (c7 ~ ((a1 && b6) || (a2 && b5) || (a3 && b4) || (a4 && b3) || (a5 && b2) || (a6 && b1)), c6 ~ ((a1 && b5) || (a2 && b4) || (a3 && b3) || (a4 && b2) || (a5 && b1)), c5 ~ ((a1 && b4) || (a2 && b3) || (a3 && b2) || (a4 && b1)), c4 ~ ((a1 && b3) || (a2 && b2) || (a3 && b1)), c3 ~ ((a1 && b2) || (a2 && b1)), c2 ~ (a1 && b1)) => Buffer a1 a2 a3 a4 a5 a6 a7 a8 q j k -> Buffer b1 b2 b3 b4 b5 b6 b7 b8 q i j -> Buffer F c2 c3 c4 c5 c6 c7 (Not (c2 || c3 || c4 || c5 || c6 || c7)) q i k
catenateB = undefined

catenate :: Deque (Closed Green) (Closed Green) q j k -> Deque (Closed Green) (Closed Green) q i j -> Deque (Closed Green) (Closed Green) q i k
catenate (DOL (O0 bl@B8{})) (DOL (O0 br@B8{})) = DOL (OGG bl D0 br)

