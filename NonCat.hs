{-# OPTIONS -Wall #-}
{-- OPTIONS -fdefer-type-errors #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module NonCat where

import Control.Arrow
import Data.Type.Equality
import GHC.TypeLits

data Colour = R | Y | G

type family MinO (a :: Nat) (b :: Nat) :: Colour where
  MinO 0 a = R
  MinO 5 a = R
  MinO a 0 = R
  MinO a 5 = R
  MinO 1 1 = Y
  MinO 1 2 = Y
  MinO 1 3 = Y
  MinO 1 4 = Y
  MinO 2 1 = Y
  MinO 3 1 = Y
  MinO 4 1 = Y
  MinO 4 2 = Y
  MinO 4 3 = Y
  MinO 4 4 = Y
  MinO 2 4 = Y
  MinO 3 4 = Y
  MinO 2 2 = G
  MinO 2 3 = G
  MinO 3 2 = G
  MinO 3 3 = G

type family MinC (a :: Nat) (b :: Nat) :: Colour where
  MinC 0 0 = G
  MinC 0 1 = Y
  MinC 0 2 = G
  MinC 0 3 = G
  MinC 0 4 = Y
  MinC 1 0 = Y
  MinC 2 0 = G
  MinC 3 0 = G
  MinC 4 0 = Y
  MinC 5 a = R
  MinC a 5 = R
  MinC 1 1 = Y
  MinC 1 2 = Y
  MinC 1 3 = Y
  MinC 1 4 = Y
  MinC 2 1 = Y
  MinC 3 1 = Y
  MinC 4 1 = Y
  MinC 4 2 = Y
  MinC 4 3 = Y
  MinC 4 4 = Y
  MinC 2 4 = Y
  MinC 3 4 = Y
  MinC 2 2 = G
  MinC 2 3 = G
  MinC 3 2 = G
  MinC 3 3 = G

data Buffer n r a b where
  B0 :: Buffer 0 r a a
  B1 :: r a b -> Buffer 1 r a b
  B2 :: r b c -> r a b -> Buffer 2 r a c
  B3 :: r c d -> r b c -> r a b -> Buffer 3 r a d
  B4 :: r d e -> r c d -> r b c -> r a b -> Buffer 4 r a e
  B5 :: r e f -> r d e -> r c d -> r b c -> r a b -> Buffer 5 r a f

type family Up (n :: Nat) :: Nat where
  Up 0  = 0
  Up 1  = 1
  Up 2  = 2
  Up 3  = 3
  Up 4  = 2
  Up 5  = 3
  Up 6  = 2
  Up 7  = 3
  Up 8  = 2
  Up 9  = 3
  Up 10 = 2
  Up 11 = 3
  Up 12 = 2
  Up 13 = 3

type family Down (n :: Nat) :: Nat where
  Down 0  = 0
  Down 1  = 0
  Down 2  = 0
  Down 3  = 0
  Down 4  = 1
  Down 5  = 1
  Down 6  = 2
  Down 7  = 2
  Down 8  = 3
  Down 9  = 3
  Down 10 = 4
  Down 11 = 4
  Down 12 = 5
  Down 13 = 5

data LBufferPair (u :: Nat) (d :: Nat) r a b where
  LBP20 :: Buffer 2 r b c -> Buffer 0 (Pair r) a b -> LBufferPair 2 0 r a c
  LBP21 :: Buffer 2 r b c -> Buffer 1 (Pair r) a b -> LBufferPair 2 1 r a c
  LBP22 :: Buffer 2 r b c -> Buffer 2 (Pair r) a b -> LBufferPair 2 2 r a c
  LBP23 :: Buffer 2 r b c -> Buffer 3 (Pair r) a b -> LBufferPair 2 3 r a c
  LBP24 :: Buffer 2 r b c -> Buffer 4 (Pair r) a b -> LBufferPair 2 4 r a c
  LBP25 :: Buffer 2 r b c -> Buffer 5 (Pair r) a b -> LBufferPair 2 5 r a c
  LBP30 :: Buffer 3 r b c -> Buffer 0 (Pair r) a b -> LBufferPair 3 0 r a c
  LBP31 :: Buffer 3 r b c -> Buffer 1 (Pair r) a b -> LBufferPair 3 1 r a c
  LBP32 :: Buffer 3 r b c -> Buffer 2 (Pair r) a b -> LBufferPair 3 2 r a c
  LBP33 :: Buffer 3 r b c -> Buffer 3 (Pair r) a b -> LBufferPair 3 3 r a c
  LBP34 :: Buffer 3 r b c -> Buffer 4 (Pair r) a b -> LBufferPair 3 4 r a c
  LBP35 :: Buffer 3 r b c -> Buffer 5 (Pair r) a b -> LBufferPair 3 5 r a c

data RBufferPair (u :: Nat) (d :: Nat) r a b where
  RBP20 :: Buffer 0 (Pair r) b c -> Buffer 2 r a b -> RBufferPair 2 0 r a c
  RBP21 :: Buffer 1 (Pair r) b c -> Buffer 2 r a b -> RBufferPair 2 1 r a c
  RBP22 :: Buffer 2 (Pair r) b c -> Buffer 2 r a b -> RBufferPair 2 2 r a c
  RBP23 :: Buffer 3 (Pair r) b c -> Buffer 2 r a b -> RBufferPair 2 3 r a c
  RBP24 :: Buffer 4 (Pair r) b c -> Buffer 2 r a b -> RBufferPair 2 4 r a c
  RBP25 :: Buffer 5 (Pair r) b c -> Buffer 2 r a b -> RBufferPair 2 5 r a c
  RBP30 :: Buffer 0 (Pair r) b c -> Buffer 3 r a b -> RBufferPair 3 0 r a c
  RBP31 :: Buffer 1 (Pair r) b c -> Buffer 3 r a b -> RBufferPair 3 1 r a c
  RBP32 :: Buffer 2 (Pair r) b c -> Buffer 3 r a b -> RBufferPair 3 2 r a c
  RBP33 :: Buffer 3 (Pair r) b c -> Buffer 3 r a b -> RBufferPair 3 3 r a c
  RBP34 :: Buffer 4 (Pair r) b c -> Buffer 3 r a b -> RBufferPair 3 4 r a c
  RBP35 :: Buffer 5 (Pair r) b c -> Buffer 3 r a b -> RBufferPair 3 5 r a c

data Genus a where
  Closed :: Genus a
  Open :: (a -> a -> a) -> a -> a -> Genus a

data Pair r a b where
  P :: r b c -> r a b -> Pair r a c

data Node c (t :: Genus *) r a b where
  NO :: Buffer c2 r c d -> Buffer c1 r a b -> Node (MinO c1 c2) (Open (Pair r) b c) r a d
  NC :: Buffer c2 r b c -> Buffer c1 r a b -> Node (MinC c1 c2) Closed r a c

data SubStack c (t :: Genus *) r a b where
  SS1 :: Node c1 t r a b -> SubStack c1 t r a b
  SSC :: Node c1 (Open (Pair r) a b) r c d -> SubStack Y t (Pair r) a b -> SubStack c1 t r c d

data Regular = Full | Semi

data Stack reg c1 r a b where
  SY :: SubStack Y Closed r a b -> Stack Full Y r a b
  SG :: SubStack G Closed r a b -> Stack Full G r a b
  SR :: SubStack R Closed r a b -> Stack Semi R r a b
  SYG :: SubStack Y (Open t c d) r a b -> Stack Full G t c d -> Stack Full Y r a b
  SRG :: SubStack R (Open t c d) r a b -> Stack Full G t c d -> Stack Semi R r a b
  SYR :: SubStack Y (Open t c d) r a b -> Stack Semi R t c d -> Stack Semi Y r a b
  SGR :: SubStack G (Open t c d) r a b -> Stack Semi R t c d -> Stack Full G r a b
  SGG :: SubStack G (Open t c d) r a b -> Stack Full G t c d -> Stack Full G r a b

class Reg reg c1 c2 r a b where
  regular :: Stack reg c1 r a b -> Stack Full c2 r a b

instance Reg Full c1 c1 r a b where
  regular = id

instance Reg Semi Y Y r a b where
  regular (SYR foo bar) = SYG foo (regular bar)

go2 a b = SG (SS1 (NC (B2 a b) B0))
go3 a b c = SG (SS1 (NC (B3 a b c) B0))
go4 a b c d = SG (SS1 (NC (B2 a b) (B2 c d)))
go5 a b c d e = SG (SS1 (NC (B3 a b c) (B2 d e)))
go6 a b c d e f = SG (SS1 (NC (B3 a b c) (B3 d e f)))
go7 a b c d e f g = SG (SSC (NO (B3 a b c) (B2 f g)) (SS1 (NC (B1 (P d e)) B0)))
go8 a b c d e f g h = SG (SSC (NO (B3 a b c) (B3 f g h)) (SS1 (NC (B1 (P d e)) B0)))
go9 a b c d e f g h i = SG (SSC (NO (B3 a b c) (B2 h i)) (SS1 (NC (B1 (P d e)) (B1 (P f g)))))
go10 a b c d e f g h i j = SG (SSC (NO (B3 a b c) (B3 h i j)) (SS1 (NC (B1 (P d e)) (B1 (P f g)))))
go11 a b c d e f g h i j k = SG (SSC (NO (B3 a b c) (B2 j k)) (SS1 (NC (B1 (P d e)) (B2 (P f g) (P h i)))))
go12 a b c d e f g h i j k l = SG (SSC (NO (B2 a b) (B2 k l)) (SS1 (NC (B4 (P c d) (P e f) (P g h) (P i j)) B0)))
go13 a b c d e f g h i j k l m = SG (SSC (NO (B2 a b) (B3 k l m)) (SS1 (NC (B4 (P c d) (P e f) (P g h) (P i j)) B0)))
go14 a b c d e f g h i j k l m n = SG (SSC (NO (B3 a b c) (B3 l m n)) (SS1 (NC (B4 (P d e) (P f g) (P h i) (P j k)) B0)))
go15 a b c d e f g h i j k l m n o = SG (SSC (NO (B3 a b c) (B2 n o)) (SS1 (NC (B4 (P d e) (P f g) (P h i) (P j k)) (B1 (P l m)))))
go16 a b c d e f g h i j k l m n o p = SG (SSC (NO (B3 a b c) (B3 n o p)) (SS1 (NC (B4 (P d e) (P f g) (P h i) (P j k)) (B1 (P l m)))))
go17 a b c d e f g h i j k l m n o p q = SG (SSC (NO (B3 a b c) (B2 p q)) (SS1 (NC (B4 (P d e) (P f g) (P h i) (P j k)) (B2 (P l m) (P n o)))))
go18 a b c d e f g h i j k l m n o p q r = SG (SSC (NO (B3 a b c) (B3 p q r)) (SS1 (NC (B4 (P d e) (P f g) (P h i) (P j k)) (B2 (P l m) (P n o)))))
go19 a b c d e f g h i j k l m n o p q r s = SG (SSC (NO (B3 a b c) (B2 r s)) (SS1 (NC (B4 (P d e) (P f g) (P h i) (P j k)) (B3 (P l m) (P n o) (P p q)))))
go20 a b c d e f g h i j k l m n o p q r s t = SG (SSC (NO (B3 a b c) (B3 r s t)) (SS1 (NC (B4 (P d e) (P f g) (P h i) (P j k)) (B3 (P l m) (P n o) (P p q)))))
go21 a b c d e f g h i j k l m n o p q r s t u = SG (SSC (NO (B3 a b c) (B2 t u)) (SS1 (NC (B4 (P d e) (P f g) (P h i) (P j k)) (B4 (P l m) (P n o) (P p q) (P r s)))))
go22 a b c d e f g h i j k l m n o p q r s t u v = SG (SSC (NO (B3 a b c) (B3 t u v)) (SS1 (NC (B4 (P d e) (P f g) (P h i) (P j k)) (B4 (P l m) (P n o) (P p q) (P r s)))))
go23 a b c d e f g h i j k l m n o p q r s t u v w = SGR (SS1 (NO (B3 a b c) (B2 v w))) (SR (SS1 (NC (B4 (P d e) (P f g) (P h i) (P j k)) (B5 (P l m) (P n o) (P p q) (P r s) (P t u)))))
go24 a b c d e f g h i j k l m n o p q r s t u v w x = SGR (SS1 (NO (B3 a b c) (B3 v w x))) (SR (SS1 (NC (B4 (P d e) (P f g) (P h i) (P j k)) (B5 (P l m) (P n o) (P p q) (P r s) (P t u)))))
go25 a b c d e f g h i j k l m n o p q r s t u v w x y = SGR (SS1 (NO (B3 a b c) (B2 x y))) (SR (SS1 (NC (B5 (P d e) (P f g) (P h i) (P j k) (P l m)) (B5 (P n o) (P p q) (P r s) (P t u) (P v w)))))
go26 a b c d e f g h i j k l m n o p q r s t u v w x y z = SGR (SS1 (NO (B3 a b c) (B3 x y z))) (SR (SS1 (NC (B5 (P d e) (P f g) (P h i) (P j k) (P l m)) (B5 (P n o) (P p q) (P r s) (P t u) (P v w)))))


l2 a b = (B2 a b, B0)
l3 a b c = (B3 a b c, B0)
l4 a b c d = (B2 a b, B1 (P c d))
l5 a b c d e = (B3 a b c, B1 (P d e))
l6 a b c d e f = (B2 a b, B2 (P c d) (P e f))
l7 a b c d e f g = (B3 a b c, B2 (P d e) (P f g))
l8 a b c d e f g h = (B2 a b, B3 (P c d) (P e f) (P g h))
l9 a b c d e f g h i = (B3 a b c, B3 (P d e) (P f g) (P h i))
l10 a b c d e f g h i j = (B2 a b, B4 (P c d) (P e f) (P g h) (P i j))
l11 a b c d e f g h i j k = (B3 a b c, B4 (P d e) (P f g) (P h i) (P j k))
l12 a b c d e f g h i j k l = (B2 a b, B5 (P c d) (P e f) (P g h) (P i j) (P k l))
l13 a b c d e f g h i j k l m = (B3 a b c, B5 (P d e) (P f g) (P h i) (P j k) (P l m))
r2 a b = (B0, B2 a b)
r3 a b c = (B0, B3 a b c)
r4 a b c d = (B1 (P a b), B2 c d)
r5 a b c d e = (B1 (P a b), B3 c d e)
r6 a b c d e f = (B2 (P a b) (P c d), B2 e f)
r7 a b c d e f g = (B2 (P a b) (P c d), B3 e f g)
r8 a b c d e f g h = (B3 (P a b) (P c d) (P e f), B2 g h)
r9 a b c d e f g h i = (B3 (P a b) (P c d) (P e f), B3 g h i)
r10 a b c d e f g h i j = (B4 (P a b) (P c d) (P e f) (P g h), B2 i j)
r11 a b c d e f g h i j k = (B4 (P a b) (P c d) (P e f) (P g h), B3 i j k)
r12 a b c d e f g h i j k l = (B5 (P a b) (P c d) (P e f) (P g h) (P i j), B2 k l)
r13 a b c d e f g h i j k l m = (B5 (P a b) (P c d) (P e f) (P g h) (P i j), B3 k l m)

lb :: (k ~ (n + 2 * m)) => Buffer n r b c -> Buffer m (Pair r) a b -> LBufferPair (Up k) (Down k) r a c
lb B0 (B1 (P f g))                                     = uncurry LBP20 $ l2 f g
lb B0 (B2 (P f g) (P h i))                             = uncurry LBP21 $ l4 f g h i
lb B0 (B3 (P f g) (P h i) (P j k))                     = uncurry LBP22 $ l6 f g h i j k
lb B0 (B4 (P f g) (P h i) (P j k) (P l m))             = uncurry LBP23 $ l8 f g h i j k l m
lb (B1 a) (B1 (P f g))                                 = uncurry LBP30 $ l3 a f g
lb (B1 a) (B2 (P f g) (P h i))                         = uncurry LBP31 $ l5 a f g h i
lb (B1 a) (B3 (P f g) (P h i) (P j k))                 = uncurry LBP32 $ l7 a f g h i j k
lb (B1 a) (B4 (P f g) (P h i) (P j k) (P l m))         = uncurry LBP33 $ l9 a f g h i j k l m
lb (B2 a b) (B1 (P f g))                               = uncurry LBP21 $ l4 a b f g
lb (B2 a b) (B2 (P f g) (P h i))                       = uncurry LBP22 $ l6 a b f g h i
lb (B2 a b) (B3 (P f g) (P h i) (P j k))               = uncurry LBP23 $ l8 a b f g h i j k
lb (B2 a b) (B4 (P f g) (P h i) (P j k) (P l m))       = uncurry LBP24 $ l10 a b f g h i j k l m
lb (B3 a b c) (B1 (P f g))                             = uncurry LBP31 $ l5 a b c f g
lb (B3 a b c) (B2 (P f g) (P h i))                     = uncurry LBP32 $ l7 a b c f g h i
lb (B3 a b c) (B3 (P f g) (P h i) (P j k))             = uncurry LBP33 $ l9 a b c f g h i j k
lb (B3 a b c) (B4 (P f g) (P h i) (P j k) (P l m))     = uncurry LBP34 $ l11 a b c f g h i j k l m
lb (B4 a b c d) (B1 (P f g))                           = uncurry LBP22 $ l6 a b c d f g
lb (B4 a b c d) (B2 (P f g) (P h i))                   = uncurry LBP23 $ l8 a b c d f g h i
lb (B4 a b c d) (B3 (P f g) (P h i) (P j k))           = uncurry LBP24 $ l10 a b c d f g h i j k
lb (B4 a b c d) (B4 (P f g) (P h i) (P j k) (P l m))   = uncurry LBP25 $ l12 a b c d f g h i j k l m
lb (B5 a b c d e) (B1 (P f g))                         = uncurry LBP32 $ l7 a b c d e f g
lb (B5 a b c d e) (B2 (P f g) (P h i))                 = uncurry LBP33 $ l9 a b c d e f g h i
lb (B5 a b c d e) (B3 (P f g) (P h i) (P j k))         = uncurry LBP34 $ l11 a b c d e f g h i j k
lb (B5 a b c d e) (B4 (P f g) (P h i) (P j k) (P l m)) = uncurry LBP35 $ l13 a b c d e f g h i j k l m
lb _ _ = undefined

rb :: (k ~ (n + 2 * m)) => Buffer m (Pair r) b c -> Buffer n r a b -> RBufferPair (Up k) (Down k) r a c
rb (B1 (P n o)) B0                                     = uncurry RBP20 $ r2 n o
rb (B2 (P n o) (P p q)) B0                             = uncurry RBP21 $ r4 n o p q
rb (B3 (P n o) (P p q) (P r s)) B0                     = uncurry RBP22 $ r6 n o p q r s
rb (B4 (P n o) (P p q) (P r s) (P t u)) B0             = uncurry RBP23 $ r8 n o p q r s t u
rb (B1 (P n o)) (B1 v)                                 = uncurry RBP30 $ r3 n o v
rb (B2 (P n o) (P p q)) (B1 v)                         = uncurry RBP31 $ r5 n o p q v
rb (B3 (P n o) (P p q) (P r s)) (B1 v)                 = uncurry RBP32 $ r7 n o p q r s v
rb (B4 (P n o) (P p q) (P r s) (P t u)) (B1 v)         = uncurry RBP33 $ r9 n o p q r s t u v
rb (B1 (P n o)) (B2 v w)                               = uncurry RBP21 $ r4 n o v w
rb (B2 (P n o) (P p q)) (B2 v w)                       = uncurry RBP22 $ r6 n o p q v w
rb (B3 (P n o) (P p q) (P r s)) (B2 v w)               = uncurry RBP23 $ r8 n o p q r s v w
rb (B4 (P n o) (P p q) (P r s) (P t u)) (B2 v w)       = uncurry RBP24 $ r10 n o p q r s t u v w
rb (B1 (P n o)) (B3 v w x)                             = uncurry RBP31 $ r5 n o v w x
rb (B2 (P n o) (P p q)) (B3 v w x)                     = uncurry RBP32 $ r7 n o p q v w x
rb (B3 (P n o) (P p q) (P r s)) (B3 v w x)             = uncurry RBP33 $ r9 n o p q r s v w x
rb (B4 (P n o) (P p q) (P r s) (P t u)) (B3 v w x)     = uncurry RBP34 $ r11 n o p q r s t u v w x
rb (B1 (P n o)) (B4 v w x y)                           = uncurry RBP22 $ r6 n o v w x y
rb (B2 (P n o) (P p q)) (B4 v w x y)                   = uncurry RBP23 $ r8 n o p q v w x y
rb (B3 (P n o) (P p q) (P r s)) (B4 v w x y)           = uncurry RBP24 $ r10 n o p q r s v w x y
rb (B4 (P n o) (P p q) (P r s) (P t u)) (B4 v w x y)   = uncurry RBP25 $ r12 n o p q r s t u v w x y
rb (B1 (P n o)) (B5 v w x y z)                         = uncurry RBP32 $ r7 n o v w x y z
rb (B2 (P n o) (P p q)) (B5 v w x y z)                 = uncurry RBP33 $ r9 n o p q v w x y z
rb (B3 (P n o) (P p q) (P r s)) (B5 v w x y z)         = uncurry RBP34 $ r11 n o p q r s v w x y z
rb (B4 (P n o) (P p q) (P r s) (P t u)) (B5 v w x y z) = uncurry RBP35 $ r13 n o p q r s t u v w x y z
rb _ _ = undefined

go :: (Combine (MinO ld rd) rem) => LBufferPair lu ld r c d -> RBufferPair ru rd r a b -> rem (Pair (Pair r)) b c -> Stack Full G r a d
go (LBP20 a b) (RBP20 c d) = combine (NO a d) (NO b c)
go (LBP20 a b) (RBP21 c d) = combine (NO a d) (NO b c)
go (LBP20 a b) (RBP22 c d) = combine (NO a d) (NO b c)
go (LBP20 a b) (RBP23 c d) = combine (NO a d) (NO b c)
go (LBP20 a b) (RBP24 c d) = combine (NO a d) (NO b c)
go (LBP20 a b) (RBP25 c d) = combine (NO a d) (NO b c)
go (LBP20 a b) (RBP30 c d) = combine (NO a d) (NO b c)
go (LBP20 a b) (RBP31 c d) = combine (NO a d) (NO b c)
go (LBP20 a b) (RBP32 c d) = combine (NO a d) (NO b c)
go (LBP20 a b) (RBP33 c d) = combine (NO a d) (NO b c)
go (LBP20 a b) (RBP34 c d) = combine (NO a d) (NO b c)
go (LBP20 a b) (RBP35 c d) = combine (NO a d) (NO b c)
go (LBP21 a b) (RBP20 c d) = combine (NO a d) (NO b c)
go (LBP21 a b) (RBP21 c d) = combine (NO a d) (NO b c)
go (LBP21 a b) (RBP22 c d) = combine (NO a d) (NO b c)
go (LBP21 a b) (RBP23 c d) = combine (NO a d) (NO b c)
go (LBP21 a b) (RBP24 c d) = combine (NO a d) (NO b c)
go (LBP21 a b) (RBP25 c d) = combine (NO a d) (NO b c)
go (LBP21 a b) (RBP30 c d) = combine (NO a d) (NO b c)
go (LBP21 a b) (RBP31 c d) = combine (NO a d) (NO b c)
go (LBP21 a b) (RBP32 c d) = combine (NO a d) (NO b c)
go (LBP21 a b) (RBP33 c d) = combine (NO a d) (NO b c)
go (LBP21 a b) (RBP34 c d) = combine (NO a d) (NO b c)
go (LBP21 a b) (RBP35 c d) = combine (NO a d) (NO b c)
go (LBP22 a b) (RBP20 c d) = combine (NO a d) (NO b c)
go (LBP22 a b) (RBP21 c d) = combine (NO a d) (NO b c)
go (LBP22 a b) (RBP22 c d) = combine (NO a d) (NO b c)
go (LBP22 a b) (RBP23 c d) = combine (NO a d) (NO b c)
go (LBP22 a b) (RBP24 c d) = combine (NO a d) (NO b c)
go (LBP22 a b) (RBP25 c d) = combine (NO a d) (NO b c)
go (LBP22 a b) (RBP30 c d) = combine (NO a d) (NO b c)
go (LBP22 a b) (RBP31 c d) = combine (NO a d) (NO b c)
go (LBP22 a b) (RBP32 c d) = combine (NO a d) (NO b c)
go (LBP22 a b) (RBP33 c d) = combine (NO a d) (NO b c)
go (LBP22 a b) (RBP34 c d) = combine (NO a d) (NO b c)
go (LBP22 a b) (RBP35 c d) = combine (NO a d) (NO b c)
go (LBP23 a b) (RBP20 c d) = combine (NO a d) (NO b c)
go (LBP23 a b) (RBP21 c d) = combine (NO a d) (NO b c)
go (LBP23 a b) (RBP22 c d) = combine (NO a d) (NO b c)
go (LBP23 a b) (RBP23 c d) = combine (NO a d) (NO b c)
go (LBP23 a b) (RBP24 c d) = combine (NO a d) (NO b c)
go (LBP23 a b) (RBP25 c d) = combine (NO a d) (NO b c)
go (LBP23 a b) (RBP30 c d) = combine (NO a d) (NO b c)
go (LBP23 a b) (RBP31 c d) = combine (NO a d) (NO b c)
go (LBP23 a b) (RBP32 c d) = combine (NO a d) (NO b c)
go (LBP23 a b) (RBP33 c d) = combine (NO a d) (NO b c)
go (LBP23 a b) (RBP34 c d) = combine (NO a d) (NO b c)
go (LBP23 a b) (RBP35 c d) = combine (NO a d) (NO b c)
go (LBP24 a b) (RBP20 c d) = combine (NO a d) (NO b c)
go (LBP24 a b) (RBP21 c d) = combine (NO a d) (NO b c)
go (LBP24 a b) (RBP22 c d) = combine (NO a d) (NO b c)
go (LBP24 a b) (RBP23 c d) = combine (NO a d) (NO b c)
go (LBP24 a b) (RBP24 c d) = combine (NO a d) (NO b c)
go (LBP24 a b) (RBP25 c d) = combine (NO a d) (NO b c)
go (LBP24 a b) (RBP30 c d) = combine (NO a d) (NO b c)
go (LBP24 a b) (RBP31 c d) = combine (NO a d) (NO b c)
go (LBP24 a b) (RBP32 c d) = combine (NO a d) (NO b c)
go (LBP24 a b) (RBP33 c d) = combine (NO a d) (NO b c)
go (LBP24 a b) (RBP34 c d) = combine (NO a d) (NO b c)
go (LBP24 a b) (RBP35 c d) = combine (NO a d) (NO b c)
go (LBP25 a b) (RBP20 c d) = combine (NO a d) (NO b c)
go (LBP25 a b) (RBP21 c d) = combine (NO a d) (NO b c)
go (LBP25 a b) (RBP22 c d) = combine (NO a d) (NO b c)
go (LBP25 a b) (RBP23 c d) = combine (NO a d) (NO b c)
go (LBP25 a b) (RBP24 c d) = combine (NO a d) (NO b c)
go (LBP25 a b) (RBP25 c d) = combine (NO a d) (NO b c)
go (LBP25 a b) (RBP30 c d) = combine (NO a d) (NO b c)
go (LBP25 a b) (RBP31 c d) = combine (NO a d) (NO b c)
go (LBP25 a b) (RBP32 c d) = combine (NO a d) (NO b c)
go (LBP25 a b) (RBP33 c d) = combine (NO a d) (NO b c)
go (LBP25 a b) (RBP34 c d) = combine (NO a d) (NO b c)
go (LBP25 a b) (RBP35 c d) = combine (NO a d) (NO b c)
go (LBP30 a b) (RBP20 c d) = combine (NO a d) (NO b c)
go (LBP30 a b) (RBP21 c d) = combine (NO a d) (NO b c)
go (LBP30 a b) (RBP22 c d) = combine (NO a d) (NO b c)
go (LBP30 a b) (RBP23 c d) = combine (NO a d) (NO b c)
go (LBP30 a b) (RBP24 c d) = combine (NO a d) (NO b c)
go (LBP30 a b) (RBP25 c d) = combine (NO a d) (NO b c)
go (LBP30 a b) (RBP30 c d) = combine (NO a d) (NO b c)
go (LBP30 a b) (RBP31 c d) = combine (NO a d) (NO b c)
go (LBP30 a b) (RBP32 c d) = combine (NO a d) (NO b c)
go (LBP30 a b) (RBP33 c d) = combine (NO a d) (NO b c)
go (LBP30 a b) (RBP34 c d) = combine (NO a d) (NO b c)
go (LBP30 a b) (RBP35 c d) = combine (NO a d) (NO b c)
go (LBP31 a b) (RBP20 c d) = combine (NO a d) (NO b c)
go (LBP31 a b) (RBP21 c d) = combine (NO a d) (NO b c)
go (LBP31 a b) (RBP22 c d) = combine (NO a d) (NO b c)
go (LBP31 a b) (RBP23 c d) = combine (NO a d) (NO b c)
go (LBP31 a b) (RBP24 c d) = combine (NO a d) (NO b c)
go (LBP31 a b) (RBP25 c d) = combine (NO a d) (NO b c)
go (LBP31 a b) (RBP30 c d) = combine (NO a d) (NO b c)
go (LBP31 a b) (RBP31 c d) = combine (NO a d) (NO b c)
go (LBP31 a b) (RBP32 c d) = combine (NO a d) (NO b c)
go (LBP31 a b) (RBP33 c d) = combine (NO a d) (NO b c)
go (LBP31 a b) (RBP34 c d) = combine (NO a d) (NO b c)
go (LBP31 a b) (RBP35 c d) = combine (NO a d) (NO b c)
go (LBP32 a b) (RBP20 c d) = combine (NO a d) (NO b c)
go (LBP32 a b) (RBP21 c d) = combine (NO a d) (NO b c)
go (LBP32 a b) (RBP22 c d) = combine (NO a d) (NO b c)
go (LBP32 a b) (RBP23 c d) = combine (NO a d) (NO b c)
go (LBP32 a b) (RBP24 c d) = combine (NO a d) (NO b c)
go (LBP32 a b) (RBP25 c d) = combine (NO a d) (NO b c)
go (LBP32 a b) (RBP30 c d) = combine (NO a d) (NO b c)
go (LBP32 a b) (RBP31 c d) = combine (NO a d) (NO b c)
go (LBP32 a b) (RBP32 c d) = combine (NO a d) (NO b c)
go (LBP32 a b) (RBP33 c d) = combine (NO a d) (NO b c)
go (LBP32 a b) (RBP34 c d) = combine (NO a d) (NO b c)
go (LBP32 a b) (RBP35 c d) = combine (NO a d) (NO b c)
go (LBP33 a b) (RBP20 c d) = combine (NO a d) (NO b c)
go (LBP33 a b) (RBP21 c d) = combine (NO a d) (NO b c)
go (LBP33 a b) (RBP22 c d) = combine (NO a d) (NO b c)
go (LBP33 a b) (RBP23 c d) = combine (NO a d) (NO b c)
go (LBP33 a b) (RBP24 c d) = combine (NO a d) (NO b c)
go (LBP33 a b) (RBP25 c d) = combine (NO a d) (NO b c)
go (LBP33 a b) (RBP30 c d) = combine (NO a d) (NO b c)
go (LBP33 a b) (RBP31 c d) = combine (NO a d) (NO b c)
go (LBP33 a b) (RBP32 c d) = combine (NO a d) (NO b c)
go (LBP33 a b) (RBP33 c d) = combine (NO a d) (NO b c)
go (LBP33 a b) (RBP34 c d) = combine (NO a d) (NO b c)
go (LBP33 a b) (RBP35 c d) = combine (NO a d) (NO b c)
go (LBP34 a b) (RBP20 c d) = combine (NO a d) (NO b c)
go (LBP34 a b) (RBP21 c d) = combine (NO a d) (NO b c)
go (LBP34 a b) (RBP22 c d) = combine (NO a d) (NO b c)
go (LBP34 a b) (RBP23 c d) = combine (NO a d) (NO b c)
go (LBP34 a b) (RBP24 c d) = combine (NO a d) (NO b c)
go (LBP34 a b) (RBP25 c d) = combine (NO a d) (NO b c)
go (LBP34 a b) (RBP30 c d) = combine (NO a d) (NO b c)
go (LBP34 a b) (RBP31 c d) = combine (NO a d) (NO b c)
go (LBP34 a b) (RBP32 c d) = combine (NO a d) (NO b c)
go (LBP34 a b) (RBP33 c d) = combine (NO a d) (NO b c)
go (LBP34 a b) (RBP34 c d) = combine (NO a d) (NO b c)
go (LBP34 a b) (RBP35 c d) = combine (NO a d) (NO b c)
go (LBP35 a b) (RBP20 c d) = combine (NO a d) (NO b c)
go (LBP35 a b) (RBP21 c d) = combine (NO a d) (NO b c)
go (LBP35 a b) (RBP22 c d) = combine (NO a d) (NO b c)
go (LBP35 a b) (RBP23 c d) = combine (NO a d) (NO b c)
go (LBP35 a b) (RBP24 c d) = combine (NO a d) (NO b c)
go (LBP35 a b) (RBP25 c d) = combine (NO a d) (NO b c)
go (LBP35 a b) (RBP30 c d) = combine (NO a d) (NO b c)
go (LBP35 a b) (RBP31 c d) = combine (NO a d) (NO b c)
go (LBP35 a b) (RBP32 c d) = combine (NO a d) (NO b c)
go (LBP35 a b) (RBP33 c d) = combine (NO a d) (NO b c)
go (LBP35 a b) (RBP34 c d) = combine (NO a d) (NO b c)
go (LBP35 a b) (RBP35 c d) = combine (NO a d) (NO b c)

class Combine c2 rem where
  combine :: Node G (Open (Pair r) c d) r a b -> Node c2 (Open (Pair (Pair r)) e f) (Pair r) c d -> rem (Pair (Pair r)) e f-> Stack Full G r a b

data Remainder r a b where
  YG :: SubStack Y (Open t c d) r a b -> Stack Full G t c d -> Remainder r a b
  YR :: SubStack Y (Open t c d) r a b -> Stack Semi R t c d -> Remainder r a b
  None :: Remainder r a a

data CL (r :: * -> * -> *) a b where
  CL :: CL r a a

instance Combine G (SubStack Y Closed) where
  combine n1 n2 ss = SGG (SS1 n1) (SG (SSC n2 ss))

instance Combine Y (SubStack Y Closed) where
  combine n1 n2 ss = SG (SSC n1 (SSC n2 ss))

instance Combine R (SubStack Y Closed) where
  combine n1 n2 ss = SGR (SS1 n1) (SR (SSC n2 ss))

instance Combine G (Stack Full G) where
  combine n1 n2 s = SGG (SS1 n1) (SGG (SS1 n2) s)

instance Combine Y (Stack Full G) where
  combine n1 n2 s = SGG (SSC n1 (SS1 n2)) s

instance Combine R (Stack Full G) where
  combine n1 n2 s = SGR (SS1 n1) (SRG (SS1 n2) s)

instance Combine G Remainder where
  combine n1 n2 (YG ss s) = SGG (SS1 n1) $ SGG (SSC n2 ss) $ s
  combine n1 n2 (YR ss s) = SGG (SS1 n1) $ SGR (SSC n2 ss) $ s
--  combine (NO b1 b2) (NO B0 B0) None = SGG (SS1 n1) $ SGR (SSC n2 ss) $ s

instance Combine Y Remainder where
  combine n1 n2 (YG ss s) = SGG (SSC n1 (SSC n2 ss)) $ s
  combine n1 n2 (YR ss s) = SGR (SSC n1 (SSC n2 ss)) $ s

instance Combine R Remainder where
  combine n1 n2 (YG ss s) = SGR (SS1 n1) $ SRG (SSC n2 ss) $ s
  combine _ _ (YR _ _) = error "Impossible"

{-
instance Combine G CL where
  combine n1 (NO c1 c2) CL = SGG (SS1 n1) $ SG (SS1 (NC c1 c2))

instance Combine Y CL where
  combine n1 (NO c1 c2) CL = SG (SSC n1 (SS1 (NC c1 c2)))

instance Combine R CL where
  combine n1 (NO c1 c2) CL = SGR (SS1 n1) $ SR (SS1 (NC c1 c2))
-}
pattern B0' <- B0
pattern B1' <- B1 _
pattern B2' <- B2 _ _
pattern B3' <- B3 _ _ _
pattern B4' <- B4 _ _ _ _
pattern B5' <- B5 _ _ _ _ _

instance Reg Semi R G r a b where
--  regular (SR (SSC (NO a b) (SS1 (NC c d)))) = go (lb a c) (rb d b) CL
  regular (SR (SSC (NO a b) (SSC (NO c d) ss))) = go (lb a c) (rb d b) ss
--  regular (SR (SSC (NO a@B0' b@B0') (SSC (NO c@B1' d@B1') ss))) = go (lb a c) (rb d b) ss
--  regular (SR (SSC (NO a@B0' b@B0') (SSC (NO c@B1' d@B2') ss))) = go (lb a c) (rb d b) ss
{-  regular (SR (SSC (NO a@B0' b@B0') (SSC (NO c@B1' d@B3') ss))) = go (lb a c) (rb d b) ss
  regular (SR (SSC (NO a@B0' b@B0') (SSC (NO c@B1' d@B4') ss))) = go (lb a c) (rb d b) ss
  regular (SR (SSC (NO a@B0' b@B0') (SSC (NO c@B2' d@B1') ss))) = go (lb a c) (rb d b) ss
  regular (SR (SSC (NO a@B0' b@B0') (SSC (NO c@B2' d@B4') ss))) = go (lb a c) (rb d b) ss
  regular (SR (SSC (NO a@B0' b@B0') (SSC (NO c@B3' d@B1') ss))) = go (lb a c) (rb d b) ss
  regular (SR (SSC (NO a@B0' b@B0') (SSC (NO c@B3' d@B4') ss))) = go (lb a c) (rb d b) ss
  regular (SR (SSC (NO a@B0' b@B0') (SSC (NO c@B4' d@B1') ss))) = go (lb a c) (rb d b) ss
  regular (SR (SSC (NO a@B0' b@B0') (SSC (NO c@B4' d@B2') ss))) = go (lb a c) (rb d b) ss
  regular (SR (SSC (NO a@B0' b@B0') (SSC (NO c@B4' d@B3') ss))) = go (lb a c) (rb d b) ss
  regular (SR (SSC (NO a@B0' b@B0') (SSC (NO c@B4' d@B4') ss))) = go (lb a c) (rb d b) ss-}

--  regular (SR (SSC (NO a b) (SSC (NO c d) ss))) = go (lb a c) (rb d b) ss
--  regular (SRG (SS1 (NO a b)) (SG (SS1 (NC c d)))) = go (lb a c) (rb d b) CL
{-  regular (SRG (SS1 (NO a b)) (SG (SSC (NO c d) ss))) = go (lb a c) (rb d b) ss
--  regular (SRG (SS1 (NO a b)) (SGR (SS1 (NO c d)) s)) = go (lb a c) (rb d b) s
  regular (SRG (SS1 (NO a b)) (SGG (SS1 (NO c d)) s)) = go (lb a c) (rb d b) s
--  regular (SRG (SS1 (NO a b)) (SGR (SSC (NO c d) ss) s)) = go (lb a c) (rb d b) (YG ss s)
  regular (SRG (SS1 (NO a b)) (SGG (SSC (NO c d) ss) s)) = go (lb a c) (rb d b) (YG ss s)
  regular (SRG (SSC (NO a b) (SS1 (NO c d))) s) = go (lb a c) (rb d b) s
  regular (SRG (SSC (NO a b) (SSC (NO c d) ss)) s) = go (lb a c) (rb d b) (YG ss s)-}
{-
  regular (SR (SS1 (NC B0 B0))) = undefined
  regular (SR (SS1 (NC B0 (B1 _)))) = undefined
  regular (SR (SS1 (NC B0 (B2 _ _)))) = undefined
  regular (SR (SS1 (NC B0 (B3 _ _ _)))) = undefined
  regular (SR (SS1 (NC B0 (B4 _ _ _ _)))) = undefined
  regular (SR (SS1 (NC (B1 _) B0))) = undefined
  regular (SR (SS1 (NC (B1 _) (B1 _)))) = undefined
  regular (SR (SS1 (NC (B1 _) (B2 _ _)))) = undefined
  regular (SR (SS1 (NC (B1 _) (B3 _ _ _)))) = undefined
  regular (SR (SS1 (NC (B1 _) (B4 _ _ _ _)))) = undefined
  regular (SR (SS1 (NC (B2 _ _) B0))) = undefined
  regular (SR (SS1 (NC (B2 _ _) (B1 _)))) = undefined
  regular (SR (SS1 (NC (B2 _ _) (B2 _ _)))) = undefined
  regular (SR (SS1 (NC (B2 _ _) (B3 _ _ _)))) = undefined
  regular (SR (SS1 (NC (B2 _ _) (B4 _ _ _ _)))) = undefined
  regular (SR (SS1 (NC (B3 _ _ _) B0))) = undefined
  regular (SR (SS1 (NC (B3 _ _ _) (B1 _)))) = undefined
  regular (SR (SS1 (NC (B3 _ _ _) (B2 _ _)))) = undefined
  regular (SR (SS1 (NC (B3 _ _ _) (B3 _ _ _)))) = undefined
  regular (SR (SS1 (NC (B3 _ _ _) (B4 _ _ _ _)))) = undefined
  regular (SR (SS1 (NC (B4 _ _ _ _) B0))) = undefined
  regular (SR (SS1 (NC (B4 _ _ _ _) (B1 _)))) = undefined
  regular (SR (SS1 (NC (B4 _ _ _ _) (B2 _ _)))) = undefined
  regular (SR (SS1 (NC (B4 _ _ _ _) (B3 _ _ _)))) = undefined
  regular (SR (SS1 (NC (B4 _ _ _ _) (B4 _ _ _ _)))) = undefined-}
  {-
  regular (SR (SSC (NO (B1 _) (B1 _)) _)) = undefined
  regular (SR (SSC (NO (B1 _) (B2 _ _)) _)) = undefined
  regular (SR (SSC (NO (B1 _) (B3 _ _ _)) _)) = undefined
  regular (SR (SSC (NO (B1 _) (B4 _ _ _ _)) _)) = undefined
  regular (SR (SSC (NO (B2 _ _) (B1 _)) _)) = undefined
  regular (SR (SSC (NO (B2 _ _) (B2 _ _)) _)) = undefined
  regular (SR (SSC (NO (B2 _ _) (B3 _ _ _)) _)) = undefined
  regular (SR (SSC (NO (B2 _ _) (B4 _ _ _ _)) _)) = undefined
  regular (SR (SSC (NO (B3 _ _ _) (B1 _)) _)) = undefined
  regular (SR (SSC (NO (B3 _ _ _) (B2 _ _)) _)) = undefined
  regular (SR (SSC (NO (B3 _ _ _) (B3 _ _ _)) _)) = undefined
  regular (SR (SSC (NO (B3 _ _ _) (B4 _ _ _ _)) _)) = undefined
  regular (SR (SSC (NO (B4 _ _ _ _) (B1 _)) _)) = undefined
  regular (SR (SSC (NO (B4 _ _ _ _) (B2 _ _)) _)) = undefined
  regular (SR (SSC (NO (B4 _ _ _ _) (B3 _ _ _)) _)) = undefined
  regular (SR (SSC (NO (B4 _ _ _ _) (B4 _ _ _ _)) _)) = undefined
  regular (SR (SSC (NO _ _) (SS1 (NC B0 B0)))) = undefined
  regular (SR (SSC (NO _ _) (SS1 (NC B0 (B2 _ _))))) = undefined
  regular (SR (SSC (NO _ _) (SS1 (NC B0 (B3 _ _ _))))) = undefined
  regular (SR (SSC (NO _ _) (SS1 (NC (B2 _ _) B0)))) = undefined
  regular (SR (SSC (NO _ _) (SS1 (NC (B2 _ _) (B2 _ _))))) = undefined
  regular (SR (SSC (NO _ _) (SS1 (NC (B2 _ _) (B3 _ _ _))))) = undefined
  regular (SR (SSC (NO _ _) (SS1 (NC (B3 _ _ _) B0)))) = undefined
  regular (SR (SSC (NO _ _) (SS1 (NC (B3 _ _ _) (B2 _ _))))) = undefined
  regular (SR (SSC (NO _ _) (SS1 (NC (B3 _ _ _) (B3 _ _ _))))) = undefined
  regular (SR (SSC (NO _ _) (SS1 (NC _ (B5 _ _ _ _ _))))) = undefined
  regular (SR (SSC (NO _ _) (SS1 (NC (B5 _ _ _ _ _) _)))) = undefined
-}
{-
  regular (SR (SS1 (NC (B5 a b c d e) B0))) = go5 a b c d e
  regular (SR (SS1 (NC B0 (B5 a b c d e)))) = go5 a b c d e
  regular (SR (SS1 (NC (B5 a b c d e) (B1 f)))) = go6 a b c d e f
  regular (SR (SS1 (NC (B5 a b c d e) (B2 f g)))) = SG (SSC (NO (B3 a b c) (B2 f g)) (SS1 (NC (B1 (P d e)) B0)))
  regular (SR (SS1 (NC (B5 a b c d e) (B3 f g h)))) = SG (SSC (NO (B3 a b c) (B3 f g h)) (SS1 (NC (B1 (P d e)) B0)))
  regular (SR (SS1 (NC (B5 a b c d e) (B4 f g h i)))) = SG (SSC (NO (B3 a b c) (B2 h i)) (SS1 (NC (B1 (P d e)) (B1 (P f g)))))
  regular (SR (SS1 (NC (B5 a b c d e) (B5 f g h i j)))) = SG (SSC (NO (B3 a b c) (B3 h i j)) (SS1 (NC (B1 (P d e)) (B1 (P f g)))))
  regular (SR (SS1 (NC (B4 a b c d) (B5 f g h i j)))) = SG (SSC (NO (B2 a b) (B3 h i j)) (SS1 (NC (B1 (P c d)) (B1 (P f g)))))
  regular (SR (SS1 (NC (B3 a b c) (B5 f g h i j)))) = SG (SSC (NO (B3 a b c) (B3 h i j)) (SS1 (NC B0 (B1 (P f g)))))
  regular (SR (SS1 (NC (B2 a b) (B5 f g h i j)))) = SG (SSC (NO (B2 a b) (B3 h i j)) (SS1 (NC B0 (B1 (P f g)))))
  regular (SR (SS1 (NC (B1 a) (B5 f g h i j)))) = SG (SS1 (NC (B3 a f g) (B3 h i j)))
-}
{-
  regular (SR (SSC (NO B0 B0) (SS1 (NC B0 (B1 (P a b)))))) = go2 a b
  regular (SR (SSC (NO B0 B0) (SS1 (NC (B1 (P a b)) B0)))) = go2 a b
  regular (SR (SSC (NO B0 B0) (SS1 (NC B0 (B4 (P a b) c d (P e f)))))) = SG (SSC (NO (B2 a b) (B2 e f)) (SS1 (NC (B1 c) (B1 d))))
  regular (SR (SSC (NO B0 B0) (SS1 (NC (B4 (P a b) c d (P e f)) B0)))) = SG (SSC (NO (B2 a b) (B2 e f)) (SS1 (NC (B1 c) (B1 d))))
  regular (SR (SSC (NO B0 B0) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go4 a b i j
  regular (SR (SSC (NO B0 B0) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go6 a b i j k l
  regular (SR (SSC (NO B0 B0) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go8 a b i j k l m n
  regular (SR (SSC (NO B0 B0) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go10 a b i j k l m n o p
  regular (SR (SSC (NO B0 B0) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go6 a b c d i j
  regular (SR (SSC (NO B0 B0) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go8 a b c d e f i j
  regular (SR (SSC (NO B0 B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go10 a b c d e f g h i j
  regular (SR (SSC (NO B0 B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go12 a b c d e f g h i j k l
  regular (SR (SSC (NO B0 B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go14 a b c d e f g h i j k l m n
  regular (SR (SSC (NO B0 B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go16 a b c d e f g h i j k l m n o p
  regular (SR (SSC (NO B0 B0) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go12 a b c d i j k l m n o p
  regular (SR (SSC (NO B0 B0) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go14 a b c d e f i j k l m n o p

  regular (SR (SSC (NO B0 (B1 k)) (SS1 (NC B0 (B1 (P a b)))))) = SG (SS1 (NC (B3 a b k) B0))
  regular (SR (SSC (NO B0 (B1 k)) (SS1 (NC (B1 (P a b)) B0)))) = SG (SS1 (NC (B3 a b k) B0))
  regular (SR (SSC (NO B0 (B1 k)) (SS1 (NC B0 (B4 (P a b) c d (P e f)))))) = SG (SSC (NO (B2 a b) (B3 e f k)) (SS1 (NC (B1 c) (B1 d))))
  regular (SR (SSC (NO B0 (B1 k)) (SS1 (NC (B4 (P a b) c d (P e f)) B0)))) = SG (SSC (NO (B2 a b) (B3 e f k)) (SS1 (NC (B1 c) (B1 d))))
  regular (SR (SSC (NO B0 (B1 q)) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go5 a b i j q
  regular (SR (SSC (NO B0 (B1 q)) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go7 a b i j k l q
  regular (SR (SSC (NO B0 (B1 q)) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go9 a b i j k l m n q
  regular (SR (SSC (NO B0 (B1 q)) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go11 a b i j k l m n o p q
  regular (SR (SSC (NO B0 (B1 q)) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go7 a b c d i j q
  regular (SR (SSC (NO B0 (B1 q)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go9 a b c d e f i j q
  regular (SR (SSC (NO B0 (B1 q)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go11 a b c d e f g h i j q
  regular (SR (SSC (NO B0 (B1 q)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go13 a b c d e f g h i j k l q
  regular (SR (SSC (NO B0 (B1 q)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go15 a b c d e f g h i j k l m n q
  regular (SR (SSC (NO B0 (B1 q)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go17 a b c d e f g h i j k l m n o p q
  regular (SR (SSC (NO B0 (B1 q)) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go13 a b c d i j k l m n o p q
  regular (SR (SSC (NO B0 (B1 q)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go15 a b c d e f i j k l m n o p q

  regular (SR (SSC (NO B0 (B2 k l)) (SS1 (NC B0 (B1 (P a b)))))) = SG (SS1 (NC (B2 a b) (B2 k l)))
  regular (SR (SSC (NO B0 (B2 k l)) (SS1 (NC (B1 (P a b)) B0)))) = SG (SS1 (NC (B2 a b) (B2 k l)))
  regular (SR (SSC (NO B0 (B2 k l)) (SS1 (NC B0 (B4 (P a b) c d e))))) = SG (SSC (NO (B2 a b) (B2 k l)) (SS1 (NC (B1 c) (B2 d e))))
  regular (SR (SSC (NO B0 (B2 k l)) (SS1 (NC (B4 (P a b) c d e) B0)))) = SG (SSC (NO (B2 a b) (B2 k l)) (SS1 (NC (B1 c) (B2 d e))))
  regular (SR (SSC (NO B0 (B2 q r)) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go6 a b i j q r
  regular (SR (SSC (NO B0 (B2 q r)) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go8 a b i j k l q r
  regular (SR (SSC (NO B0 (B2 q r)) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go10 a b i j k l m n q r
  regular (SR (SSC (NO B0 (B2 q r)) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go12 a b i j k l m n o p q r
  regular (SR (SSC (NO B0 (B2 q r)) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go8 a b c d i j q r
  regular (SR (SSC (NO B0 (B2 q r)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go10 a b c d e f i j q r
  regular (SR (SSC (NO B0 (B2 q r)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go12 a b c d e f g h i j q r
  regular (SR (SSC (NO B0 (B2 q r)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go14 a b c d e f g h i j k l q r
  regular (SR (SSC (NO B0 (B2 q r)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go16 a b c d e f g h i j k l m n q r
  regular (SR (SSC (NO B0 (B2 q r)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go18 a b c d e f g h i j k l m n o p q r
  regular (SR (SSC (NO B0 (B2 q r)) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go14 a b c d i j k l m n o p q r
  regular (SR (SSC (NO B0 (B2 q r)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go16 a b c d e f i j k l m n o p q r

  regular (SR (SSC (NO B0 (B3 k l m)) (SS1 (NC B0 (B1 (P a b)))))) = SG (SS1 (NC (B2 a b) (B3 k l m)))
  regular (SR (SSC (NO B0 (B3 k l m)) (SS1 (NC (B1 (P a b)) B0)))) = SG (SS1 (NC (B2 a b) (B3 k l m)))
  regular (SR (SSC (NO B0 (B3 k l m)) (SS1 (NC B0 (B4 (P a b) c d e))))) = SG (SSC (NO (B2 a b) (B3 k l m)) (SS1 (NC (B1 c) (B2 d e))))
  regular (SR (SSC (NO B0 (B3 k l m)) (SS1 (NC (B4 (P a b) c d e) B0)))) = SG (SSC (NO (B2 a b) (B3 k l m)) (SS1 (NC (B1 c) (B2 d e))))
  regular (SR (SSC (NO B0 (B3 q r s)) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go7 a b i j q r s
  regular (SR (SSC (NO B0 (B3 q r s)) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go9 a b i j k l q r s
  regular (SR (SSC (NO B0 (B3 q r s)) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go11 a b i j k l m n q r s
  regular (SR (SSC (NO B0 (B3 q r s)) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go13 a b i j k l m n o p q r s
  regular (SR (SSC (NO B0 (B3 q r s)) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go9 a b c d i j q r s
  regular (SR (SSC (NO B0 (B3 q r s)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go11 a b c d e f i j q r s
  regular (SR (SSC (NO B0 (B3 q r s)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go13 a b c d e f g h i j q r s
  regular (SR (SSC (NO B0 (B3 q r s)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go15 a b c d e f g h i j k l q r s
  regular (SR (SSC (NO B0 (B3 q r s)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go17 a b c d e f g h i j k l m n q r s
  regular (SR (SSC (NO B0 (B3 q r s)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go19 a b c d e f g h i j k l m n o p q r s
  regular (SR (SSC (NO B0 (B3 q r s)) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go15 a b c d i j k l m n o p q r s
  regular (SR (SSC (NO B0 (B3 q r s)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go17 a b c d e f i j k l m n o p q r s

  regular (SR (SSC (NO B0 (B4 k l m n)) (SS1 (NC B0 (B1 (P a b)))))) = go6 a b k l m n
  regular (SR (SSC (NO B0 (B4 k l m n)) (SS1 (NC (B1 (P a b)) B0)))) = go6 a b k l m n
  regular (SR (SSC (NO B0 (B4 k l m n)) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go12 a b c d e f g h k l m n
  regular (SR (SSC (NO B0 (B4 k l m n)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go12 a b c d e f g h k l m n
  regular (SR (SSC (NO B0 (B4 q r s t)) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go8 a b i j q r s t
  regular (SR (SSC (NO B0 (B4 q r s t)) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go10 a b i j k l q r s t
  regular (SR (SSC (NO B0 (B4 q r s t)) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go12 a b i j k l m n q r s t
  regular (SR (SSC (NO B0 (B4 q r s t)) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go14 a b i j k l m n o p q r s t
  regular (SR (SSC (NO B0 (B4 q r s t)) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go10 a b c d i j q r s t
  regular (SR (SSC (NO B0 (B4 q r s t)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go12 a b c d e f i j q r s t
  regular (SR (SSC (NO B0 (B4 q r s t)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go14 a b c d e f g h i j q r s t
  regular (SR (SSC (NO B0 (B4 q r s t)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go16 a b c d e f g h i j k l q r s t
  regular (SR (SSC (NO B0 (B4 q r s t)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go18 a b c d e f g h i j k l m n q r s t
  regular (SR (SSC (NO B0 (B4 q r s t)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go20 a b c d e f g h i j k l m n o p q r s t
  regular (SR (SSC (NO B0 (B4 q r s t)) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go16 a b c d i j k l m n o p q r s t
  regular (SR (SSC (NO B0 (B4 q r s t)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go18 a b c d e f i j k l m n o p q r s t

  regular (SR (SSC (NO B0 (B5 k l m n o)) (SS1 (NC B0 (B1 (P a b)))))) = go7 a b k l m n o
  regular (SR (SSC (NO B0 (B5 k l m n o)) (SS1 (NC (B1 (P a b)) B0)))) = go7 a b k l m n o
  regular (SR (SSC (NO B0 (B5 k l m n o)) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go13 a b c d e f g h k l m n o
  regular (SR (SSC (NO B0 (B5 k l m n o)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go13 a b c d e f g h k l m n o
  regular (SR (SSC (NO B0 (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go9 a b i j q r s t u
  regular (SR (SSC (NO B0 (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go11 a b i j k l q r s t u
  regular (SR (SSC (NO B0 (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go13 a b i j k l m n q r s t u
  regular (SR (SSC (NO B0 (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go15 a b i j k l m n o p q r s t u
  regular (SR (SSC (NO B0 (B5 q r s t u)) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go11 a b c d i j q r s t u
  regular (SR (SSC (NO B0 (B5 q r s t u)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go13 a b c d e f i j q r s t u
  regular (SR (SSC (NO B0 (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go15 a b c d e f g h i j q r s t u
  regular (SR (SSC (NO B0 (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go17 a b c d e f g h i j k l q r s t u
  regular (SR (SSC (NO B0 (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go19 a b c d e f g h i j k l m n q r s t u
  regular (SR (SSC (NO B0 (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go21 a b c d e f g h i j k l m n o p q r s t u
  regular (SR (SSC (NO B0 (B5 q r s t u)) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go17 a b c d i j k l m n o p q r s t u
  regular (SR (SSC (NO B0 (B5 q r s t u)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go19 a b c d e f i j k l m n o p q r s t u

  regular (SR (SSC (NO (B1 k) B0) (SS1 (NC B0 (B1 (P a b)))))) = go3 k a b
  regular (SR (SSC (NO (B1 k) B0) (SS1 (NC (B1 (P a b)) B0)))) = go3 k a b
  regular (SR (SSC (NO (B1 k) B0) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go9 k a b c d e f g h
  regular (SR (SSC (NO (B1 k) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go9 k a b c d e f g h
  regular (SR (SSC (NO (B1 v) B0) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go5 v a b i j
  regular (SR (SSC (NO (B1 v) B0) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go7 v a b i j k l
  regular (SR (SSC (NO (B1 v) B0) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go9 v a b i j k l m n
  regular (SR (SSC (NO (B1 v) B0) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go11 v a b i j k l m n o p
  regular (SR (SSC (NO (B1 v) B0) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go7 v a b c d i j
  regular (SR (SSC (NO (B1 v) B0) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go9 v a b c d e f i j
  regular (SR (SSC (NO (B1 v) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go11 v a b c d e f g h i j
  regular (SR (SSC (NO (B1 v) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go13 v a b c d e f g h i j k l
  regular (SR (SSC (NO (B1 v) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go15 v a b c d e f g h i j k l m n
  regular (SR (SSC (NO (B1 v) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go17 v a b c d e f g h i j k l m n o p
  regular (SR (SSC (NO (B1 v) B0) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go13 v a b c d i j k l m n o p
  regular (SR (SSC (NO (B1 v) B0) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go15 v a b c d e f i j k l m n o p

  regular (SR (SSC (NO (B2 k l) B0) (SS1 (NC B0 (B1 (P a b)))))) = go4 k l a b
  regular (SR (SSC (NO (B2 k l) B0) (SS1 (NC (B1 (P a b)) B0)))) = go4 k l a b
  regular (SR (SSC (NO (B2 k l) B0) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go10 k l a b c d e f g h
  regular (SR (SSC (NO (B2 k l) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go10 k l a b c d e f g h
  regular (SR (SSC (NO (B2 v w) B0) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go6 v w a b i j
  regular (SR (SSC (NO (B2 v w) B0) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go8 v w a b i j k l
  regular (SR (SSC (NO (B2 v w) B0) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go10 v w a b i j k l m n
  regular (SR (SSC (NO (B2 v w) B0) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go12 v w a b i j k l m n o p
  regular (SR (SSC (NO (B2 v w) B0) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go8 v w a b c d i j
  regular (SR (SSC (NO (B2 v w) B0) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go10 v w a b c d e f i j
  regular (SR (SSC (NO (B2 v w) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go12 v w a b c d e f g h i j
  regular (SR (SSC (NO (B2 v w) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go14 v w a b c d e f g h i j k l
  regular (SR (SSC (NO (B2 v w) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go16 v w a b c d e f g h i j k l m n
  regular (SR (SSC (NO (B2 v w) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go18 v w a b c d e f g h i j k l m n o p
  regular (SR (SSC (NO (B2 v w) B0) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go14 v w a b c d i j k l m n o p
  regular (SR (SSC (NO (B2 v w) B0) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go16 v w a b c d e f i j k l m n o p

  regular (SR (SSC (NO (B3 k l m) B0) (SS1 (NC B0 (B1 (P a b)))))) = go5 k l m a b
  regular (SR (SSC (NO (B3 k l m) B0) (SS1 (NC (B1 (P a b)) B0)))) = go5 k l m a b
  regular (SR (SSC (NO (B3 k l m) B0) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go11 k l m a b c d e f g h
  regular (SR (SSC (NO (B3 k l m) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go11 k l m a b c d e f g h
  regular (SR (SSC (NO (B3 v w x) B0) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go7 v w x a b i j
  regular (SR (SSC (NO (B3 v w x) B0) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go9 v w x a b i j k l
  regular (SR (SSC (NO (B3 v w x) B0) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go11 v w x a b i j k l m n
  regular (SR (SSC (NO (B3 v w x) B0) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go13 v w x a b i j k l m n o p
  regular (SR (SSC (NO (B3 v w x) B0) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go9 v w x a b c d i j
  regular (SR (SSC (NO (B3 v w x) B0) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go11 v w x a b c d e f i j
  regular (SR (SSC (NO (B3 v w x) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go13 v w x a b c d e f g h i j
  regular (SR (SSC (NO (B3 v w x) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go15 v w x a b c d e f g h i j k l
  regular (SR (SSC (NO (B3 v w x) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go17 v w x a b c d e f g h i j k l m n
  regular (SR (SSC (NO (B3 v w x) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go19 v w x a b c d e f g h i j k l m n o p
  regular (SR (SSC (NO (B3 v w x) B0) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go15 v w x a b c d i j k l m n o p
  regular (SR (SSC (NO (B3 v w x) B0) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go17 v w x a b c d e f i j k l m n o p

  regular (SR (SSC (NO (B4 k l m n) B0) (SS1 (NC B0 (B1 (P a b)))))) = go6 k l m n a b
  regular (SR (SSC (NO (B4 k l m n) B0) (SS1 (NC (B1 (P a b)) B0)))) = go6 k l m n a b
  regular (SR (SSC (NO (B4 k l m n) B0) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go12 k l m n a b c d e f g h
  regular (SR (SSC (NO (B4 k l m n) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go12 k l m n a b c d e f g h
  regular (SR (SSC (NO (B4 v w x y) B0) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go8 v w x y a b i j
  regular (SR (SSC (NO (B4 v w x y) B0) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go10 v w x y a b i j k l
  regular (SR (SSC (NO (B4 v w x y) B0) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go12 v w x y a b i j k l m n
  regular (SR (SSC (NO (B4 v w x y) B0) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go14 v w x y a b i j k l m n o p
  regular (SR (SSC (NO (B4 v w x y) B0) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go10 v w x y a b c d i j
  regular (SR (SSC (NO (B4 v w x y) B0) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go12 v w x y a b c d e f i j
  regular (SR (SSC (NO (B4 v w x y) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go14 v w x y a b c d e f g h i j
  regular (SR (SSC (NO (B4 v w x y) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go16 v w x y a b c d e f g h i j k l
  regular (SR (SSC (NO (B4 v w x y) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go18 v w x y a b c d e f g h i j k l m n
  regular (SR (SSC (NO (B4 v w x y) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go20 v w x y a b c d e f g h i j k l m n o p
  regular (SR (SSC (NO (B4 v w x y) B0) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go16 v w x y a b c d i j k l m n o p
  regular (SR (SSC (NO (B4 v w x y) B0) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go18 v w x y a b c d e f i j k l m n o p

  regular (SR (SSC (NO (B5 k l m n o) B0) (SS1 (NC B0 (B1 (P a b)))))) = go7 k l m n o a b
  regular (SR (SSC (NO (B5 k l m n o) B0) (SS1 (NC (B1 (P a b)) B0)))) = go7 k l m n o a b
  regular (SR (SSC (NO (B5 k l m n o) B0) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go13 k l m n o a b c d e f g h
  regular (SR (SSC (NO (B5 k l m n o) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go13 k l m n o a b c d e f g h
  regular (SR (SSC (NO (B5 v w x y z) B0) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go9 v w x y z a b i j
  regular (SR (SSC (NO (B5 v w x y z) B0) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go11 v w x y z a b i j k l
  regular (SR (SSC (NO (B5 v w x y z) B0) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go13 v w x y z a b i j k l m n
  regular (SR (SSC (NO (B5 v w x y z) B0) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go15 v w x y z a b i j k l m n o p
  regular (SR (SSC (NO (B5 v w x y z) B0) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go11 v w x y z a b c d i j
  regular (SR (SSC (NO (B5 v w x y z) B0) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go13 v w x y z a b c d e f i j
  regular (SR (SSC (NO (B5 v w x y z) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go15 v w x y z a b c d e f g h i j
  regular (SR (SSC (NO (B5 v w x y z) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go17 v w x y z a b c d e f g h i j k l
  regular (SR (SSC (NO (B5 v w x y z) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go19 v w x y z a b c d e f g h i j k l m n
  regular (SR (SSC (NO (B5 v w x y z) B0) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go21 v w x y z a b c d e f g h i j k l m n o p
  regular (SR (SSC (NO (B5 v w x y z) B0) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go17 v w x y z a b c d i j k l m n o p
  regular (SR (SSC (NO (B5 v w x y z) B0) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go19 v w x y z a b c d e f i j k l m n o p

  regular (SR (SSC (NO (B5 k l m n o) (B1 p)) (SS1 (NC B0 (B1 (P a b)))))) = go8 k l m n o a b p
  regular (SR (SSC (NO (B5 k l m n o) (B1 p)) (SS1 (NC (B1 (P a b)) B0)))) = go8 k l m n o a b p
  regular (SR (SSC (NO (B5 k l m n o) (B1 p)) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go14 k l m n o a b c d e f g h p
  regular (SR (SSC (NO (B5 k l m n o) (B1 p)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go14 k l m n o a b c d e f g h p
  regular (SR (SSC (NO (B5 v w x y z) (B1 q)) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go10 v w x y z a b i j q
  regular (SR (SSC (NO (B5 v w x y z) (B1 q)) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go12 v w x y z a b i j k l q
  regular (SR (SSC (NO (B5 v w x y z) (B1 q)) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go14 v w x y z a b i j k l m n q
  regular (SR (SSC (NO (B5 v w x y z) (B1 q)) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go16 v w x y z a b i j k l m n o p q
  regular (SR (SSC (NO (B5 v w x y z) (B1 q)) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go12 v w x y z a b c d i j q
  regular (SR (SSC (NO (B5 v w x y z) (B1 q)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go14 v w x y z a b c d e f i j q
  regular (SR (SSC (NO (B5 v w x y z) (B1 q)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go16 v w x y z a b c d e f g h i j q
  regular (SR (SSC (NO (B5 v w x y z) (B1 q)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go18 v w x y z a b c d e f g h i j k l q
  regular (SR (SSC (NO (B5 v w x y z) (B1 q)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go20 v w x y z a b c d e f g h i j k l m n q
  regular (SR (SSC (NO (B5 v w x y z) (B1 q)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go22 v w x y z a b c d e f g h i j k l m n o p q
  regular (SR (SSC (NO (B5 v w x y z) (B1 q)) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go18 v w x y z a b c d i j k l m n o p q
  regular (SR (SSC (NO (B5 v w x y z) (B1 q)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go20 v w x y z a b c d e f i j k l m n o p q

  regular (SR (SSC (NO (B5 k l m n o) (B2 p q)) (SS1 (NC B0 (B1 (P a b)))))) = go9 k l m n o a b p q
  regular (SR (SSC (NO (B5 k l m n o) (B2 p q)) (SS1 (NC (B1 (P a b)) B0)))) = go9 k l m n o a b p q
  regular (SR (SSC (NO (B5 k l m n o) (B2 p q)) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go15 k l m n o a b c d e f g h p q
  regular (SR (SSC (NO (B5 k l m n o) (B2 p q)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go15 k l m n o a b c d e f g h p q
  regular (SR (SSC (NO (B5 v w x y z) (B2 q r)) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go11 v w x y z a b i j q r
  regular (SR (SSC (NO (B5 v w x y z) (B2 q r)) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go13 v w x y z a b i j k l q r
  regular (SR (SSC (NO (B5 v w x y z) (B2 q r)) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go15 v w x y z a b i j k l m n q r
  regular (SR (SSC (NO (B5 v w x y z) (B2 q r)) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go17 v w x y z a b i j k l m n o p q r
  regular (SR (SSC (NO (B5 v w x y z) (B2 q r)) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go13 v w x y z a b c d i j q r
  regular (SR (SSC (NO (B5 v w x y z) (B2 q r)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go15 v w x y z a b c d e f i j q r
  regular (SR (SSC (NO (B5 v w x y z) (B2 q r)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go17 v w x y z a b c d e f g h i j q r
  regular (SR (SSC (NO (B5 v w x y z) (B2 q r)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go19 v w x y z a b c d e f g h i j k l q r
  regular (SR (SSC (NO (B5 v w x y z) (B2 q r)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go21 v w x y z a b c d e f g h i j k l m n q r
  regular (SR (SSC (NO (B5 v w x y z) (B2 q r)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go23 v w x y z a b c d e f g h i j k l m n o p q r
  regular (SR (SSC (NO (B5 v w x y z) (B2 q r)) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go19 v w x y z a b c d i j k l m n o p q r
  regular (SR (SSC (NO (B5 v w x y z) (B2 q r)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go21 v w x y z a b c d e f i j k l m n o p q r

  regular (SR (SSC (NO (B5 k l m n o) (B3 p q r)) (SS1 (NC B0 (B1 (P a b)))))) = go10 k l m n o a b p q r
  regular (SR (SSC (NO (B5 k l m n o) (B3 p q r)) (SS1 (NC (B1 (P a b)) B0)))) = go10 k l m n o a b p q r
  regular (SR (SSC (NO (B5 k l m n o) (B3 p q r)) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go16 k l m n o a b c d e f g h p q r
  regular (SR (SSC (NO (B5 k l m n o) (B3 p q r)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go16 k l m n o a b c d e f g h p q r
  regular (SR (SSC (NO (B5 v w x y z) (B3 q r s)) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go12 v w x y z a b i j q r s
  regular (SR (SSC (NO (B5 v w x y z) (B3 q r s)) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go14 v w x y z a b i j k l q r s
  regular (SR (SSC (NO (B5 v w x y z) (B3 q r s)) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go16 v w x y z a b i j k l m n q r s
  regular (SR (SSC (NO (B5 v w x y z) (B3 q r s)) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go18 v w x y z a b i j k l m n o p q r s
  regular (SR (SSC (NO (B5 v w x y z) (B3 q r s)) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go14 v w x y z a b c d i j q r s
  regular (SR (SSC (NO (B5 v w x y z) (B3 q r s)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go16 v w x y z a b c d e f i j q r s
  regular (SR (SSC (NO (B5 v w x y z) (B3 q r s)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go18 v w x y z a b c d e f g h i j q r s
  regular (SR (SSC (NO (B5 v w x y z) (B3 q r s)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go20 v w x y z a b c d e f g h i j k l q r s
  regular (SR (SSC (NO (B5 v w x y z) (B3 q r s)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go22 v w x y z a b c d e f g h i j k l m n q r s
  regular (SR (SSC (NO (B5 v w x y z) (B3 q r s)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go24 v w x y z a b c d e f g h i j k l m n o p q r s
  regular (SR (SSC (NO (B5 v w x y z) (B3 q r s)) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go20 v w x y z a b c d i j k l m n o p q r s
  regular (SR (SSC (NO (B5 v w x y z) (B3 q r s)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go22 v w x y z a b c d e f i j k l m n o p q r s

  regular (SR (SSC (NO (B5 k l m n o) (B4 p q r t)) (SS1 (NC B0 (B1 (P a b)))))) = go11 k l m n o a b p q r t
  regular (SR (SSC (NO (B5 k l m n o) (B4 p q r t)) (SS1 (NC (B1 (P a b)) B0)))) = go11 k l m n o a b p q r t
  regular (SR (SSC (NO (B5 k l m n o) (B4 p q r t)) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go17 k l m n o a b c d e f g h p q r t
  regular (SR (SSC (NO (B5 k l m n o) (B4 p q r t)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go17 k l m n o a b c d e f g h p q r t
  regular (SR (SSC (NO (B5 v w x y z) (B4 q r s t)) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go13 v w x y z a b i j q r s t
  regular (SR (SSC (NO (B5 v w x y z) (B4 q r s t)) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go15 v w x y z a b i j k l q r s t
  regular (SR (SSC (NO (B5 v w x y z) (B4 q r s t)) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go17 v w x y z a b i j k l m n q r s t
  regular (SR (SSC (NO (B5 v w x y z) (B4 q r s t)) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go19 v w x y z a b i j k l m n o p q r s t
  regular (SR (SSC (NO (B5 v w x y z) (B4 q r s t)) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go15 v w x y z a b c d i j q r s t
  regular (SR (SSC (NO (B5 v w x y z) (B4 q r s t)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go17 v w x y z a b c d e f i j q r s t
  regular (SR (SSC (NO (B5 v w x y z) (B4 q r s t)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go19 v w x y z a b c d e f g h i j q r s t
  regular (SR (SSC (NO (B5 v w x y z) (B4 q r s t)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go21 v w x y z a b c d e f g h i j k l q r s t
  regular (SR (SSC (NO (B5 v w x y z) (B4 q r s t)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go23 v w x y z a b c d e f g h i j k l m n q r s t
  regular (SR (SSC (NO (B5 v w x y z) (B4 q r s t)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go25 v w x y z a b c d e f g h i j k l m n o p q r s t
  regular (SR (SSC (NO (B5 v w x y z) (B4 q r s t)) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go21 v w x y z a b c d i j k l m n o p q r s t
  regular (SR (SSC (NO (B5 v w x y z) (B4 q r s t)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go23 v w x y z a b c d e f i j k l m n o p q r s t

  regular (SR (SSC (NO (B5 k l m n o) (B5 p q r s t)) (SS1 (NC B0 (B1 (P a b)))))) = go12 k l m n o a b p q r s t
  regular (SR (SSC (NO (B5 k l m n o) (B5 p q r s t)) (SS1 (NC (B1 (P a b)) B0)))) = go12 k l m n o a b p q r s t
  regular (SR (SSC (NO (B5 k l m n o) (B5 p q r s t)) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go18 k l m n o a b c d e f g h p q r s t
  regular (SR (SSC (NO (B5 k l m n o) (B5 p q r s t)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go18 k l m n o a b c d e f g h p q r s t
  regular (SR (SSC (NO (B5 v w x y z) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go14 v w x y z a b i j q r s t u
  regular (SR (SSC (NO (B5 v w x y z) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go16 v w x y z a b i j k l q r s t u
  regular (SR (SSC (NO (B5 v w x y z) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go18 v w x y z a b i j k l m n q r s t u
  regular (SR (SSC (NO (B5 v w x y z) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go20 v w x y z a b i j k l m n o p q r s t u
  regular (SR (SSC (NO (B5 v w x y z) (B5 q r s t u)) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go16 v w x y z a b c d i j q r s t u
  regular (SR (SSC (NO (B5 v w x y z) (B5 q r s t u)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go18 v w x y z a b c d e f i j q r s t u
  regular (SR (SSC (NO (B5 v w x y z) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go20 v w x y z a b c d e f g h i j q r s t u
  regular (SR (SSC (NO (B5 v w x y z) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go22 v w x y z a b c d e f g h i j k l q r s t u
  regular (SR (SSC (NO (B5 v w x y z) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go24 v w x y z a b c d e f g h i j k l m n q r s t u
  regular (SR (SSC (NO (B5 v w x y z) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go26 v w x y z a b c d e f g h i j k l m n o p q r s t u
  regular (SR (SSC (NO (B5 v w x y z) (B5 q r s t u)) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go22 v w x y z a b c d i j k l m n o p q r s t u
  regular (SR (SSC (NO (B5 v w x y z) (B5 q r s t u)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go24 v w x y z a b c d e f i j k l m n o p q r s t u

  regular (SR (SSC (NO (B1 p) (B5 k l m n o)) (SS1 (NC B0 (B1 (P a b)))))) = go8 p a b k l m n o
  regular (SR (SSC (NO (B1 p) (B5 k l m n o)) (SS1 (NC (B1 (P a b)) B0)))) = go8 p a b k l m n o
  regular (SR (SSC (NO (B1 p) (B5 k l m n o)) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go14 p a b c d e f g h k l m n o
  regular (SR (SSC (NO (B1 p) (B5 k l m n o)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go14 p a b c d e f g h k l m n o
  regular (SR (SSC (NO (B1 v) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go10 v a b i j q r s t u
  regular (SR (SSC (NO (B1 v) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go12 v a b i j k l q r s t u
  regular (SR (SSC (NO (B1 v) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go14 v a b i j k l m n q r s t u
  regular (SR (SSC (NO (B1 v) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go16 v a b i j k l m n o p q r s t u
  regular (SR (SSC (NO (B1 v) (B5 q r s t u)) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go12 v a b c d i j q r s t u
  regular (SR (SSC (NO (B1 v) (B5 q r s t u)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go14 v a b c d e f i j q r s t u
  regular (SR (SSC (NO (B1 v) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go16 v a b c d e f g h i j q r s t u
  regular (SR (SSC (NO (B1 v) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go18 v a b c d e f g h i j k l q r s t u
  regular (SR (SSC (NO (B1 v) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go20 v a b c d e f g h i j k l m n q r s t u
  regular (SR (SSC (NO (B1 v) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go22 v a b c d e f g h i j k l m n o p q r s t u
  regular (SR (SSC (NO (B1 v) (B5 q r s t u)) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go18 v a b c d i j k l m n o p q r s t u
  regular (SR (SSC (NO (B1 v) (B5 q r s t u)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go20 v a b c d e f i j k l m n o p q r s t u

  regular (SR (SSC (NO (B2 p q) (B5 k l m n o)) (SS1 (NC B0 (B1 (P a b)))))) = go9 p q a b k l m n o
  regular (SR (SSC (NO (B2 p q) (B5 k l m n o)) (SS1 (NC (B1 (P a b)) B0)))) = go9 p q a b k l m n o
  regular (SR (SSC (NO (B2 p q) (B5 k l m n o)) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go15 p q a b c d e f g h k l m n o
  regular (SR (SSC (NO (B2 p q) (B5 k l m n o)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go15 p q a b c d e f g h k l m n o
  regular (SR (SSC (NO (B2 v w) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go11 v w a b i j q r s t u
  regular (SR (SSC (NO (B2 v w) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go13 v w a b i j k l q r s t u
  regular (SR (SSC (NO (B2 v w) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go15 v w a b i j k l m n q r s t u
  regular (SR (SSC (NO (B2 v w) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go17 v w a b i j k l m n o p q r s t u
  regular (SR (SSC (NO (B2 v w) (B5 q r s t u)) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go13 v w a b c d i j q r s t u
  regular (SR (SSC (NO (B2 v w) (B5 q r s t u)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go15 v w a b c d e f i j q r s t u
  regular (SR (SSC (NO (B2 v w) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go17 v w a b c d e f g h i j q r s t u
  regular (SR (SSC (NO (B2 v w) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go19 v w a b c d e f g h i j k l q r s t u
  regular (SR (SSC (NO (B2 v w) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go21 v w a b c d e f g h i j k l m n q r s t u
  regular (SR (SSC (NO (B2 v w) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go23 v w a b c d e f g h i j k l m n o p q r s t u
  regular (SR (SSC (NO (B2 v w) (B5 q r s t u)) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go19 v w a b c d i j k l m n o p q r s t u
  regular (SR (SSC (NO (B2 v w) (B5 q r s t u)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go21 v w a b c d e f i j k l m n o p q r s t u

  regular (SR (SSC (NO (B3 p q r) (B5 k l m n o)) (SS1 (NC B0 (B1 (P a b)))))) = go10 p q r a b k l m n o
  regular (SR (SSC (NO (B3 p q r) (B5 k l m n o)) (SS1 (NC (B1 (P a b)) B0)))) = go10 p q r a b k l m n o
  regular (SR (SSC (NO (B3 p q r) (B5 k l m n o)) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go16 p q r a b c d e f g h k l m n o
  regular (SR (SSC (NO (B3 p q r) (B5 k l m n o)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go16 p q r a b c d e f g h k l m n o
  regular (SR (SSC (NO (B3 v w x) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go12 v w x a b i j q r s t u
  regular (SR (SSC (NO (B3 v w x) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go14 v w x a b i j k l q r s t u
  regular (SR (SSC (NO (B3 v w x) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go16 v w x a b i j k l m n q r s t u
  regular (SR (SSC (NO (B3 v w x) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go18 v w x a b i j k l m n o p q r s t u
  regular (SR (SSC (NO (B3 v w x) (B5 q r s t u)) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go14 v w x a b c d i j q r s t u
  regular (SR (SSC (NO (B3 v w x) (B5 q r s t u)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go16 v w x a b c d e f i j q r s t u
  regular (SR (SSC (NO (B3 v w x) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go18 v w x a b c d e f g h i j q r s t u
  regular (SR (SSC (NO (B3 v w x) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go20 v w x a b c d e f g h i j k l q r s t u
  regular (SR (SSC (NO (B3 v w x) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go22 v w x a b c d e f g h i j k l m n q r s t u
  regular (SR (SSC (NO (B3 v w x) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go24 v w x a b c d e f g h i j k l m n o p q r s t u
  regular (SR (SSC (NO (B3 v w x) (B5 q r s t u)) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go20 v w x a b c d i j k l m n o p q r s t u
  regular (SR (SSC (NO (B3 v w x) (B5 q r s t u)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go22 v w x a b c d e f i j k l m n o p q r s t u

  regular (SR (SSC (NO (B4 p q r s) (B5 k l m n o)) (SS1 (NC B0 (B1 (P a b)))))) = go11 p q r s a b k l m n o
  regular (SR (SSC (NO (B4 p q r s) (B5 k l m n o)) (SS1 (NC (B1 (P a b)) B0)))) = go11 p q r s a b k l m n o
  regular (SR (SSC (NO (B4 p q r s) (B5 k l m n o)) (SS1 (NC B0 (B4 (P a b) (P c d) (P e f) (P g h)))))) = go17 p q r s a b c d e f g h k l m n o
  regular (SR (SSC (NO (B4 p q r s) (B5 k l m n o)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) B0)))) = go17 p q r s a b c d e f g h k l m n o
  regular (SR (SSC (NO (B4 v w x y) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B1 (P i j)))))) = go13 v w x y a b i j q r s t u
  regular (SR (SSC (NO (B4 v w x y) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B2 (P i j) (P k l)))))) = go15 v w x y a b i j k l q r s t u
  regular (SR (SSC (NO (B4 v w x y) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B3 (P i j) (P k l) (P m n)))))) = go17 v w x y a b i j k l m n q r s t u
  regular (SR (SSC (NO (B4 v w x y) (B5 q r s t u)) (SS1 (NC (B1 (P a b)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go19 v w x y a b i j k l m n o p q r s t u
  regular (SR (SSC (NO (B4 v w x y) (B5 q r s t u)) (SS1 (NC (B2 (P a b) (P c d)) (B1 (P i j)))))) = go15 v w x y a b c d i j q r s t u
  regular (SR (SSC (NO (B4 v w x y) (B5 q r s t u)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B1 (P i j)))))) = go17 v w x y a b c d e f i j q r s t u
  regular (SR (SSC (NO (B4 v w x y) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B1 (P i j)))))) = go19 v w x y a b c d e f g h i j q r s t u
  regular (SR (SSC (NO (B4 v w x y) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B2 (P i j) (P k l)))))) = go21 v w x y a b c d e f g h i j k l q r s t u
  regular (SR (SSC (NO (B4 v w x y) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B3 (P i j) (P k l) (P m n)))))) = go23 v w x y a b c d e f g h i j k l m n q r s t u
  regular (SR (SSC (NO (B4 v w x y) (B5 q r s t u)) (SS1 (NC (B4 (P a b) (P c d) (P e f) (P g h)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go25 v w x y a b c d e f g h i j k l m n o p q r s t u
  regular (SR (SSC (NO (B4 v w x y) (B5 q r s t u)) (SS1 (NC (B2 (P a b) (P c d)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go21 v w x y a b c d i j k l m n o p q r s t u
  regular (SR (SSC (NO (B4 v w x y) (B5 q r s t u)) (SS1 (NC (B3 (P a b) (P c d) (P e f)) (B4 (P i j) (P k l) (P m n) (P o p)))))) = go23 v w x y a b c d e f i j k l m n o p q r s t u
-}
