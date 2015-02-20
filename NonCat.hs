{-# OPTIONS -Wall #-}
{-# OPTIONS -fno-spec-constr #-}
{-- OPTIONS -fdefer-type-errors #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module NonCat where

import GHC.TypeLits

data Colour = R | Y | G deriving Show

class MinClass (a :: Nat) (b :: Nat) where
  type MinO a b :: Colour
  type MinC a b :: Colour

instance MinClass 5 0 where type MinO 5 0 = R; type MinC 5 0 = R
instance MinClass 5 1 where type MinO 5 1 = R; type MinC 5 1 = R
instance MinClass 5 2 where type MinO 5 2 = R; type MinC 5 2 = R
instance MinClass 5 3 where type MinO 5 3 = R; type MinC 5 3 = R
instance MinClass 5 4 where type MinO 5 4 = R; type MinC 5 4 = R
instance MinClass 5 5 where type MinO 5 5 = R; type MinC 5 5 = R
instance MinClass 4 5 where type MinO 4 5 = R; type MinC 4 5 = R
instance MinClass 3 5 where type MinO 3 5 = R; type MinC 3 5 = R
instance MinClass 2 5 where type MinO 2 5 = R; type MinC 2 5 = R
instance MinClass 1 5 where type MinO 1 5 = R; type MinC 1 5 = R
instance MinClass 0 5 where type MinO 0 5 = R; type MinC 0 5 = R
instance MinClass 0 0 where type MinO 0 0 = R; type MinC 0 0 = G
instance MinClass 0 1 where type MinO 0 1 = R; type MinC 0 1 = Y
instance MinClass 0 2 where type MinO 0 2 = R; type MinC 0 2 = G
instance MinClass 0 3 where type MinO 0 3 = R; type MinC 0 3 = G
instance MinClass 0 4 where type MinO 0 4 = R; type MinC 0 4 = Y
instance MinClass 1 0 where type MinO 1 0 = R; type MinC 1 0 = Y
instance MinClass 2 0 where type MinO 2 0 = R; type MinC 2 0 = G
instance MinClass 3 0 where type MinO 3 0 = R; type MinC 3 0 = G
instance MinClass 4 0 where type MinO 4 0 = R; type MinC 4 0 = Y
instance MinClass 1 1 where type MinO 1 1 = Y; type MinC 1 1 = Y
instance MinClass 1 2 where type MinO 1 2 = Y; type MinC 1 2 = Y
instance MinClass 1 3 where type MinO 1 3 = Y; type MinC 1 3 = Y
instance MinClass 1 4 where type MinO 1 4 = Y; type MinC 1 4 = Y
instance MinClass 2 1 where type MinO 2 1 = Y; type MinC 2 1 = Y
instance MinClass 3 1 where type MinO 3 1 = Y; type MinC 3 1 = Y
instance MinClass 4 1 where type MinO 4 1 = Y; type MinC 4 1 = Y
instance MinClass 4 2 where type MinO 4 2 = Y; type MinC 4 2 = Y
instance MinClass 4 3 where type MinO 4 3 = Y; type MinC 4 3 = Y
instance MinClass 4 4 where type MinO 4 4 = Y; type MinC 4 4 = Y
instance MinClass 2 4 where type MinO 2 4 = Y; type MinC 2 4 = Y
instance MinClass 3 4 where type MinO 3 4 = Y; type MinC 3 4 = Y
instance MinClass 2 2 where type MinO 2 2 = G; type MinC 2 2 = G
instance MinClass 2 3 where type MinO 2 3 = G; type MinC 2 3 = G
instance MinClass 3 2 where type MinO 3 2 = G; type MinC 3 2 = G
instance MinClass 3 3 where type MinO 3 3 = G; type MinC 3 3 = G

data Buffer n r a b where
  B0 :: Buffer 0 r a a
  B1 :: r a b -> Buffer 1 r a b
  B2 :: r b c -> r a b -> Buffer 2 r a c
  B3 :: r c d -> r b c -> r a b -> Buffer 3 r a d
  B4 :: r d e -> r c d -> r b c -> r a b -> Buffer 4 r a e
  B5 :: r e f -> r d e -> r c d -> r b c -> r a b -> Buffer 5 r a f

instance Show (Buffer n r a b) where
  show B0' = "B0"
  show B1' = "B1"
  show B2' = "B2"
  show B3' = "B3"
  show B4' = "B4"
  show B5' = "B5"

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

data LBP (u :: Nat) (d :: Nat) r a b where
  LBP :: Buffer n r b c -> Buffer m (Pair r) a b -> LBP n m r a c

data RBP (u :: Nat) (d :: Nat) r a b where
  RBP :: Buffer n (Pair r) b c -> Buffer m r a b -> RBP m n r a c

data Genus a where
  Closed :: Genus a
  Open :: (a -> a -> a) -> a -> a -> Genus a

data Pair r a b where
  P :: r b c -> r a b -> Pair r a c

data Node c (t :: Genus *) r a b where
  NO :: HasColour (MinO c1 c2) => Buffer c1 r c d -> Buffer c2 r a b -> Node (MinO c1 c2) (Open (Pair r) b c) r a d
  NC :: HasColour (MinC c1 c2) => Buffer c1 r b c -> Buffer c2 r a b -> Node (MinC c1 c2) Closed r a c

toNO :: Buffer c2 r c d -> Buffer c1 r a b -> Node (MinO c1 c2) (Open (Pair r) b c) r a d
toNO a@B0' b@B0' = NO a b
toNO a@B0' b@B1' = NO a b
toNO a@B0' b@B2' = NO a b
toNO a@B0' b@B3' = NO a b
toNO a@B0' b@B4' = NO a b
toNO a@B0' b@B5' = NO a b
toNO a@B1' b@B0' = NO a b
toNO a@B1' b@B1' = NO a b
toNO a@B1' b@B2' = NO a b
toNO a@B1' b@B3' = NO a b
toNO a@B1' b@B4' = NO a b
toNO a@B1' b@B5' = NO a b
toNO a@B2' b@B0' = NO a b
toNO a@B2' b@B1' = NO a b
toNO a@B2' b@B2' = NO a b
toNO a@B2' b@B3' = NO a b
toNO a@B2' b@B4' = NO a b
toNO a@B2' b@B5' = NO a b
toNO a@B3' b@B0' = NO a b
toNO a@B3' b@B1' = NO a b
toNO a@B3' b@B2' = NO a b
toNO a@B3' b@B3' = NO a b
toNO a@B3' b@B4' = NO a b
toNO a@B3' b@B5' = NO a b
toNO a@B4' b@B0' = NO a b
toNO a@B4' b@B1' = NO a b
toNO a@B4' b@B2' = NO a b
toNO a@B4' b@B3' = NO a b
toNO a@B4' b@B4' = NO a b
toNO a@B4' b@B5' = NO a b
toNO a@B5' b@B0' = NO a b
toNO a@B5' b@B1' = NO a b
toNO a@B5' b@B2' = NO a b
toNO a@B5' b@B3' = NO a b
toNO a@B5' b@B4' = NO a b
toNO a@B5' b@B5' = NO a b

toNC :: Buffer c2 r b c -> Buffer c1 r a b -> Node (MinC c1 c2) Closed r a c
toNC a@B0' b@B0' = NC a b
toNC a@B0' b@B1' = NC a b
toNC a@B0' b@B2' = NC a b
toNC a@B0' b@B3' = NC a b
toNC a@B0' b@B4' = NC a b
toNC a@B0' b@B5' = NC a b
toNC a@B1' b@B0' = NC a b
toNC a@B1' b@B1' = NC a b
toNC a@B1' b@B2' = NC a b
toNC a@B1' b@B3' = NC a b
toNC a@B1' b@B4' = NC a b
toNC a@B1' b@B5' = NC a b
toNC a@B2' b@B0' = NC a b
toNC a@B2' b@B1' = NC a b
toNC a@B2' b@B2' = NC a b
toNC a@B2' b@B3' = NC a b
toNC a@B2' b@B4' = NC a b
toNC a@B2' b@B5' = NC a b
toNC a@B3' b@B0' = NC a b
toNC a@B3' b@B1' = NC a b
toNC a@B3' b@B2' = NC a b
toNC a@B3' b@B3' = NC a b
toNC a@B3' b@B4' = NC a b
toNC a@B3' b@B5' = NC a b
toNC a@B4' b@B0' = NC a b
toNC a@B4' b@B1' = NC a b
toNC a@B4' b@B2' = NC a b
toNC a@B4' b@B3' = NC a b
toNC a@B4' b@B4' = NC a b
toNC a@B4' b@B5' = NC a b
toNC a@B5' b@B0' = NC a b
toNC a@B5' b@B1' = NC a b
toNC a@B5' b@B2' = NC a b
toNC a@B5' b@B3' = NC a b
toNC a@B5' b@B4' = NC a b
toNC a@B5' b@B5' = NC a b

deriving instance Show (Node c t r a b)

data SubStack c (t :: Genus *) r a b where
  SS1 :: Node c1 t r a b -> SubStack c1 t r a b
  SSC :: Node c1 (Open (Pair r) a b) r c d -> SubStack Y t (Pair r) a b -> SubStack c1 t r c d

deriving instance Show (SubStack c t r a b)

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

deriving instance Show (Stack c t r a b)

class Reg reg c1 r a b where
  regular :: Stack reg c1 r a b -> Deque r a b

type family RegCol (c :: Colour) :: Colour where
  RegCol R = G
  RegCol Y = Y
  RegCol G = G

instance Reg Full G r a b where
  regular = D

instance Reg Full Y r a b where
  regular = D

instance Reg Semi Y r a b where
  regular (SYR foo bar) =
    case regular bar of
      D baz -> case stackColour baz of
        G' -> D $ SYG foo baz

go1 a = SY (SS1 (NC (B1 a) B0))
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

l0 = (B0, B0)
l1 a = (B1 a, B0)
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
r0 = (B0, B0)
r1 a = (B0, B1 a)
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

lb' :: (k ~ (n + 2 * m)) => Buffer n r b c -> Buffer m (Pair r) a b -> LBP (Up k) (Down k) r a c
lb' B0 (B1 (P f g))                                     = uncurry LBP $ l2 f g
lb' B0 (B2 (P f g) (P h i))                             = uncurry LBP $ l4 f g h i
lb' B0 (B3 (P f g) (P h i) (P j k))                     = uncurry LBP $ l6 f g h i j k
lb' B0 (B4 (P f g) (P h i) (P j k) (P l m))             = uncurry LBP $ l8 f g h i j k l m
lb' (B1 a) (B1 (P f g))                                 = uncurry LBP $ l3 a f g
lb' (B1 a) (B2 (P f g) (P h i))                         = uncurry LBP $ l5 a f g h i
lb' (B1 a) (B3 (P f g) (P h i) (P j k))                 = uncurry LBP $ l7 a f g h i j k
lb' (B1 a) (B4 (P f g) (P h i) (P j k) (P l m))         = uncurry LBP $ l9 a f g h i j k l m
lb' (B2 a b) B0                                         = uncurry LBP $ l2 a b
lb' (B2 a b) (B1 (P f g))                               = uncurry LBP $ l4 a b f g
lb' (B2 a b) (B2 (P f g) (P h i))                       = uncurry LBP $ l6 a b f g h i
lb' (B2 a b) (B3 (P f g) (P h i) (P j k))               = uncurry LBP $ l8 a b f g h i j k
lb' (B2 a b) (B4 (P f g) (P h i) (P j k) (P l m))       = uncurry LBP $ l10 a b f g h i j k l m
lb' (B3 a b c) B0                                       = uncurry LBP $ l3 a b c
lb' (B3 a b c) (B1 (P f g))                             = uncurry LBP $ l5 a b c f g
lb' (B3 a b c) (B2 (P f g) (P h i))                     = uncurry LBP $ l7 a b c f g h i
lb' (B3 a b c) (B3 (P f g) (P h i) (P j k))             = uncurry LBP $ l9 a b c f g h i j k
lb' (B3 a b c) (B4 (P f g) (P h i) (P j k) (P l m))     = uncurry LBP $ l11 a b c f g h i j k l m
lb' (B4 a b c d) B0                                     = uncurry LBP $ l4 a b c d
lb' (B4 a b c d) (B1 (P f g))                           = uncurry LBP $ l6 a b c d f g
lb' (B4 a b c d) (B2 (P f g) (P h i))                   = uncurry LBP $ l8 a b c d f g h i
lb' (B4 a b c d) (B3 (P f g) (P h i) (P j k))           = uncurry LBP $ l10 a b c d f g h i j k
lb' (B4 a b c d) (B4 (P f g) (P h i) (P j k) (P l m))   = uncurry LBP $ l12 a b c d f g h i j k l m
lb' (B5 a b c d e) B0                                   = uncurry LBP $ l5 a b c d e
lb' (B5 a b c d e) (B1 (P f g))                         = uncurry LBP $ l7 a b c d e f g
lb' (B5 a b c d e) (B2 (P f g) (P h i))                 = uncurry LBP $ l9 a b c d e f g h i
lb' (B5 a b c d e) (B3 (P f g) (P h i) (P j k))         = uncurry LBP $ l11 a b c d e f g h i j k
lb' (B5 a b c d e) (B4 (P f g) (P h i) (P j k) (P l m)) = uncurry LBP $ l13 a b c d e f g h i j k l m
lb' _ _ = undefined
{-# INLINE lb' #-}

rb' :: (k ~ (n + 2 * m)) => Buffer m (Pair r) b c -> Buffer n r a b -> RBP (Up k) (Down k) r a c
rb' (B1 (P n o)) B0                                     = uncurry RBP $ r2 n o
rb' (B2 (P n o) (P p q)) B0                             = uncurry RBP $ r4 n o p q
rb' (B3 (P n o) (P p q) (P r s)) B0                     = uncurry RBP $ r6 n o p q r s
rb' (B4 (P n o) (P p q) (P r s) (P t u)) B0             = uncurry RBP $ r8 n o p q r s t u
rb' (B1 (P n o)) (B1 v)                                 = uncurry RBP $ r3 n o v
rb' (B2 (P n o) (P p q)) (B1 v)                         = uncurry RBP $ r5 n o p q v
rb' (B3 (P n o) (P p q) (P r s)) (B1 v)                 = uncurry RBP $ r7 n o p q r s v
rb' (B4 (P n o) (P p q) (P r s) (P t u)) (B1 v)         = uncurry RBP $ r9 n o p q r s t u v
rb' (B1 (P n o)) (B2 v w)                               = uncurry RBP $ r4 n o v w
rb' (B2 (P n o) (P p q)) (B2 v w)                       = uncurry RBP $ r6 n o p q v w
rb' (B3 (P n o) (P p q) (P r s)) (B2 v w)               = uncurry RBP $ r8 n o p q r s v w
rb' (B4 (P n o) (P p q) (P r s) (P t u)) (B2 v w)       = uncurry RBP $ r10 n o p q r s t u v w
rb' (B1 (P n o)) (B3 v w x)                             = uncurry RBP $ r5 n o v w x
rb' (B2 (P n o) (P p q)) (B3 v w x)                     = uncurry RBP $ r7 n o p q v w x
rb' (B3 (P n o) (P p q) (P r s)) (B3 v w x)             = uncurry RBP $ r9 n o p q r s v w x
rb' (B4 (P n o) (P p q) (P r s) (P t u)) (B3 v w x)     = uncurry RBP $ r11 n o p q r s t u v w x
rb' (B1 (P n o)) (B4 v w x y)                           = uncurry RBP $ r6 n o v w x y
rb' (B2 (P n o) (P p q)) (B4 v w x y)                   = uncurry RBP $ r8 n o p q v w x y
rb' (B3 (P n o) (P p q) (P r s)) (B4 v w x y)           = uncurry RBP $ r10 n o p q r s v w x y
rb' (B4 (P n o) (P p q) (P r s) (P t u)) (B4 v w x y)   = uncurry RBP $ r12 n o p q r s t u v w x y
rb' (B1 (P n o)) (B5 v w x y z)                         = uncurry RBP $ r7 n o v w x y z
rb' (B2 (P n o) (P p q)) (B5 v w x y z)                 = uncurry RBP $ r9 n o p q v w x y z
rb' (B3 (P n o) (P p q) (P r s)) (B5 v w x y z)         = uncurry RBP $ r11 n o p q r s v w x y z
rb' (B4 (P n o) (P p q) (P r s) (P t u)) (B5 v w x y z) = uncurry RBP $ r13 n o p q r s t u v w x y z
rb' _ _ = undefined
{-# INLINE rb' #-}

class Combine c t rem where
  type Regularity c t rem :: Regular
  type Col c t rem :: Colour
  combine :: Node c (t (Pair r) e f) r a b -> rem (Pair r) e f-> Stack (Regularity c t rem) (Col c t rem) r a b

instance Combine G Open (Stack Full G) where
  type Regularity G Open (Stack Full G) = Full
  type Col G Open (Stack Full G) = G
  combine n1 ss = SGG (SS1 n1) ss

instance Combine Y Open (Stack Full G) where
  type Regularity Y Open (Stack Full G) = Full
  type Col Y Open (Stack Full G) = Y
  combine n1 ss = SYG (SS1 n1) ss

instance Combine R Open (Stack Full G) where
  type Regularity R Open (Stack Full G) = Semi
  type Col R Open (Stack Full G) = R
  combine n1 ss = SRG (SS1 n1) ss


class Combine2 r c2 rem where
  type Opening rem :: Genus *
  combine2 :: Node G (Open (Pair r) c d) r a b -> Node c2 (Opening rem) (Pair r) c d -> rem -> Stack Full G r a b

data Remainder r a b where
  YG :: SubStack Y (Open t c d) r a b -> Stack Full G t c d -> Remainder r a b
  YR :: SubStack Y (Open t c d) r a b -> Stack Semi R t c d -> Remainder r a b

data CL where
  CL :: CL

instance Combine2 r G (SubStack Y Closed (Pair (Pair r)) e f) where
  type Opening (SubStack Y Closed (Pair (Pair r)) e f) = Open (Pair (Pair r)) e f
  combine2 n1 n2 ss = SGG (SS1 n1) (SG (SSC n2 ss))

instance Combine2 r Y (SubStack Y Closed (Pair (Pair r)) e f) where
  type Opening (SubStack Y Closed (Pair (Pair r)) e f) = Open (Pair (Pair r)) e f
  combine2 n1 n2 ss = SG (SSC n1 (SSC n2 ss))

instance Combine2 r R (SubStack Y Closed (Pair (Pair r)) e f) where
  type Opening (SubStack Y Closed (Pair (Pair r)) e f) = Open (Pair (Pair r)) e f
  combine2 n1 n2 ss = SGR (SS1 n1) (SR (SSC n2 ss))

instance Combine2 r G (Stack Full G (Pair (Pair r)) e f) where
  type Opening (Stack Full G (Pair (Pair r)) e f) = Open (Pair (Pair r)) e f
  combine2 n1 n2 s = SGG (SS1 n1) (SGG (SS1 n2) s)

instance Combine2 r Y (Stack Full G (Pair (Pair r)) e f) where
  type Opening (Stack Full G (Pair (Pair r)) e f) = Open (Pair (Pair r)) e f
  combine2 n1 n2 s = SGG (SSC n1 (SS1 n2)) s

instance Combine2 r R (Stack Full G (Pair (Pair r)) e f) where
  type Opening (Stack Full G (Pair (Pair r)) e f) = Open (Pair (Pair r)) e f
  combine2 n1 n2 s = SGR (SS1 n1) (SRG (SS1 n2) s)

instance Combine2 r G (Stack Semi R (Pair (Pair r)) e f) where
  type Opening (Stack Semi R (Pair (Pair r)) e f) = Open (Pair (Pair r)) e f
  combine2 n1 n2 s = SGG (SS1 n1) (SGR (SS1 n2) s)

instance Combine2 r Y (Stack Semi R (Pair (Pair r)) e f) where
  type Opening (Stack Semi R (Pair (Pair r)) e f) = Open (Pair (Pair r)) e f
  combine2 n1 n2 s = SGR (SSC n1 (SS1 n2)) s

instance Combine2 r G (Remainder (Pair (Pair r)) e f) where
  type Opening (Remainder (Pair (Pair r)) e f) = Open (Pair (Pair r)) e f
  combine2 n1 n2 (YG ss s) = SGG (SS1 n1) $ SGG (SSC n2 ss) $ s
  combine2 n1 n2 (YR ss s) = SGG (SS1 n1) $ SGR (SSC n2 ss) $ s

instance Combine2 r Y (Remainder (Pair (Pair r)) e f) where
  type Opening (Remainder (Pair (Pair r)) e f) = Open (Pair (Pair r)) e f
  combine2 n1 n2 (YG ss s) = SGG (SSC n1 (SSC n2 ss)) $ s
  combine2 n1 n2 (YR ss s) = SGR (SSC n1 (SSC n2 ss)) $ s

instance Combine2 r R (Remainder (Pair (Pair r)) e f) where
  type Opening (Remainder (Pair (Pair r)) e f) = Open (Pair (Pair r)) e f
  combine2 n1 n2 (YG ss s) = SGR (SS1 n1) $ SRG (SSC n2 ss) $ s
  combine2 _ _ (YR _ _) = error "Impossible"

instance Combine2 r G CL where
  type Opening CL = Closed
  combine2 (NO a@B2' b@B2') (NC B0 B0) CL = SG (SS1 (NC a b))
  combine2 (NO a@B2' b@B3') (NC B0 B0) CL = SG (SS1 (NC a b))
  combine2 (NO a@B3' b@B2') (NC B0 B0) CL = SG (SS1 (NC a b))
  combine2 (NO a@B3' b@B3') (NC B0 B0) CL = SG (SS1 (NC a b))
  combine2 n1 n2 CL = SGG (SS1 n1) $ SG (SS1 n2)

instance Combine2 r Y CL where
  type Opening CL = Closed
  combine2 n1 n2 CL = SG (SSC n1 (SS1 n2))

instance Combine2 r R CL where
  type Opening CL = Closed
  combine2 n1 n2 CL = SGR (SS1 n1) $ SR (SS1 n2)


pattern B0' <- B0
pattern B1' <- B1 _
pattern B2' <- B2 _ _
pattern B3' <- B3 _ _ _
pattern B4' <- B4 _ _ _ _
pattern B5' <- B5 _ _ _ _ _

data GorY t r a b where
  GG2 :: Node G (Open (Pair r) c d) r a b -> Node G t (Pair r) c d -> GorY t r a b
  GY2 :: Node G (Open (Pair r) c d) r a b -> Node Y t (Pair r) c d -> GorY t r a b

data GorYorR t r a b where
  GG3 :: Node G (Open (Pair r) c d) r a b -> Node G t (Pair r) c d -> GorYorR t r a b
  GY3 :: Node G (Open (Pair r) c d) r a b -> Node Y t (Pair r) c d -> GorYorR t r a b
  GR3 :: Node G (Open (Pair r) c d) r a b -> Node R t (Pair r) c d -> GorYorR t r a b
  G3 :: Node G Closed r a b -> GorYorR Closed r a b
  Y3 :: Node Y Closed r a b -> GorYorR Closed r a b

data Deque r a b where
  D :: HasColour c => Stack Full c r a b -> Deque r a b

deriving instance Show (Deque r a b)

pre :: (n <= 4) => r b c -> Buffer n r a b -> Buffer (n + 1) r a c
pre a B0 = B1 a
pre a (B1 b) = B2 a b
pre a (B2 b c) = B3 a b c
pre a (B3 b c d) = B4 a b c d
pre a (B4 b c d e) = B5 a b c d e
{-- INLINE pre #-}

data BCons n r a c where
  BCons :: r b c -> Buffer n r a b -> BCons (n + 1) r a c
  BCEmpty :: BCons 0 r a a

data BSnoc n r a c where
  BSnoc :: Buffer n r b c -> r a b -> BSnoc (n + 1) r a c
  BSEmpty :: BSnoc 0 r a a

unpre :: Buffer n r a c -> BCons n r a c
unpre B0             = BCEmpty
unpre (B1 a)         = BCons a B0
unpre (B2 a b)       = BCons a (B1 b)
unpre (B3 a b c)     = BCons a (B2 b c)
unpre (B4 a b c d)   = BCons a (B3 b c d)
unpre (B5 a b c d e) = BCons a (B4 b c d e)
{-- INLINE unpre #-}

unpost :: Buffer n r a c -> BSnoc n r a c
unpost B0             = BSEmpty
unpost (B1 a)         = BSnoc B0 a
unpost (B2 a b)       = BSnoc (B1 a) b
unpost (B3 a b c)     = BSnoc (B2 a b) c
unpost (B4 a b c d)   = BSnoc (B3 a b c) d
unpost (B5 a b c d e) = BSnoc (B4 a b c d) e
{-- INLINE unpost #-}

data Foo a b where
  F :: Int -> Foo () ()

instance Show (Foo a b) where
  show (F n) = show n

empty :: Deque r a a
empty = D $ SG (SS1 (NC B0 B0))

cons :: r b c -> Deque r a b -> Deque r a c
cons a (D (SG (SSC (NO b@B2' e@B2') f)))    = regular $ SG $ SSC (NO (pre a b) e) f
cons a (D (SG (SSC (NO b@B2' e@B3') f)))    = regular $ SG $ SSC (NO (pre a b) e) f
cons a (D (SG (SSC (NO b@B3' e@B2') f)))    = regular $ SY $ SSC (NO (pre a b) e) f
cons a (D (SG (SSC (NO b@B3' e@B3') f)))    = regular $ SY $ SSC (NO (pre a b) e) f
cons a (D (SG (SS1 (NC b@B0' e@B0'))))      = regular $ SY $ SS1 (NC (pre a b) e)
cons a (D (SG (SS1 (NC b@B2' e@B0'))))      = regular $ SG $ SS1 (NC (pre a b) e)
cons a (D (SG (SS1 (NC b@B2' e@B2'))))      = regular $ SG $ SS1 (NC (pre a b) e)
cons a (D (SG (SS1 (NC b@B2' e@B3'))))      = regular $ SG $ SS1 (NC (pre a b) e)
cons a (D (SG (SS1 (NC b@B3' e@B0'))))      = regular $ SY $ SS1 (NC (pre a b) e)
cons a (D (SG (SS1 (NC b@B3' e@B2'))))      = regular $ SY $ SS1 (NC (pre a b) e)
cons a (D (SG (SS1 (NC b@B3' e@B3'))))      = regular $ SY $ SS1 (NC (pre a b) e)
cons a (D (SG (SS1 (NC b@B0' e@B2'))))      = regular $ SY $ SS1 (NC (pre a b) e)
cons a (D (SG (SS1 (NC b@B0' e@B3'))))      = regular $ SY $ SS1 (NC (pre a b) e)
cons a (D (SY (SSC (NO b@B1' e@B1') f)))    = regular $ SY $ SSC (NO (pre a b) e) f
cons a (D (SY (SSC (NO b@B1' e@B2') f)))    = regular $ SG $ SSC (NO (pre a b) e) f
cons a (D (SY (SSC (NO b@B1' e@B3') f)))    = regular $ SG $ SSC (NO (pre a b) e) f
cons a (D (SY (SSC (NO b@B1' e@B4') f)))    = regular $ SY $ SSC (NO (pre a b) e) f
cons a (D (SY (SSC (NO b@B2' e@B1') f)))    = regular $ SY $ SSC (NO (pre a b) e) f
cons a (D (SY (SSC (NO b@B2' e@B4') f)))    = regular $ SY $ SSC (NO (pre a b) e) f
cons a (D (SY (SSC (NO b@B3' e@B1') f)))    = regular $ SY $ SSC (NO (pre a b) e) f
cons a (D (SY (SSC (NO b@B3' e@B4') f)))    = regular $ SY $ SSC (NO (pre a b) e) f
cons a (D (SY (SSC (NO b@B4' e@B1') f)))    = regular $ SR $ SSC (NO (pre a b) e) f
cons a (D (SY (SSC (NO b@B4' e@B2') f)))    = regular $ SR $ SSC (NO (pre a b) e) f
cons a (D (SY (SSC (NO b@B4' e@B3') f)))    = regular $ SR $ SSC (NO (pre a b) e) f
cons a (D (SY (SSC (NO b@B4' e@B4') f)))    = regular $ SR $ SSC (NO (pre a b) e) f
cons a (D (SY (SS1 (NC b@B1' e@B1'))))      = regular $ SY $ SS1 (NC (pre a b) e)
cons a (D (SY (SS1 (NC b@B1' e@B2'))))      = regular $ SG $ SS1 (NC (pre a b) e)
cons a (D (SY (SS1 (NC b@B1' e@B3'))))      = regular $ SG $ SS1 (NC (pre a b) e)
cons a (D (SY (SS1 (NC b@B1' e@B4'))))      = regular $ SY $ SS1 (NC (pre a b) e)
cons a (D (SY (SS1 (NC b@B2' e@B1'))))      = regular $ SY $ SS1 (NC (pre a b) e)
cons a (D (SY (SS1 (NC b@B2' e@B4'))))      = regular $ SY $ SS1 (NC (pre a b) e)
cons a (D (SY (SS1 (NC b@B3' e@B1'))))      = regular $ SY $ SS1 (NC (pre a b) e)
cons a (D (SY (SS1 (NC b@B3' e@B4'))))      = regular $ SY $ SS1 (NC (pre a b) e)
cons a (D (SY (SS1 (NC b@B4' e@B1'))))      = regular $ SR $ SS1 (NC (pre a b) e)
cons a (D (SY (SS1 (NC b@B4' e@B2'))))      = regular $ SR $ SS1 (NC (pre a b) e)
cons a (D (SY (SS1 (NC b@B4' e@B3'))))      = regular $ SR $ SS1 (NC (pre a b) e)
cons a (D (SY (SS1 (NC b@B4' e@B4'))))      = regular $ SR $ SS1 (NC (pre a b) e)
cons a (D (SY (SS1 (NC b@B0' e@B1'))))      = regular $ SY $ SS1 (NC (pre a b) e)
cons a (D (SY (SS1 (NC b@B0' e@B4'))))      = regular $ SY $ SS1 (NC (pre a b) e)
cons a (D (SY (SS1 (NC b@B1' e@B0'))))      = regular $ SG $ SS1 (NC (pre a b) e)
cons a (D (SY (SS1 (NC b@B4' e@B0'))))      = regular $ SR $ SS1 (NC (pre a b) e)
cons a (D (SGG (SSC (NO b@B2' e@B2') f) g)) = regular $ SGG (SSC (NO (pre a b) e) f) g
cons a (D (SGG (SSC (NO b@B2' e@B3') f) g)) = regular $ SGG (SSC (NO (pre a b) e) f) g
cons a (D (SGG (SSC (NO b@B3' e@B2') f) g)) = regular $ SYG (SSC (NO (pre a b) e) f) g
cons a (D (SGG (SSC (NO b@B3' e@B3') f) g)) = regular $ SYG (SSC (NO (pre a b) e) f) g
cons a (D (SGG (SS1 (NO b@B2' e@B2')) g))   = regular $ SGG (SS1 (NO (pre a b) e)) g
cons a (D (SGG (SS1 (NO b@B2' e@B3')) g))   = regular $ SGG (SS1 (NO (pre a b) e)) g
cons a (D (SGG (SS1 (NO b@B3' e@B2')) g))   = regular $ SYG (SS1 (NO (pre a b) e)) g
cons a (D (SGG (SS1 (NO b@B3' e@B3')) g))   = regular $ SYG (SS1 (NO (pre a b) e)) g
cons a (D (SGR (SSC (NO b@B2' e@B2') f) g)) = regular $ SGR (SSC (NO (pre a b) e) f) g
cons a (D (SGR (SSC (NO b@B2' e@B3') f) g)) = regular $ SGR (SSC (NO (pre a b) e) f) g
cons a (D (SGR (SSC (NO b@B3' e@B2') f) g)) = regular $ SYR (SSC (NO (pre a b) e) f) g
cons a (D (SGR (SSC (NO b@B3' e@B3') f) g)) = regular $ SYR (SSC (NO (pre a b) e) f) g
cons a (D (SGR (SS1 (NO b@B2' e@B2')) g))   = regular $ SGR (SS1 (NO (pre a b) e)) g
cons a (D (SGR (SS1 (NO b@B2' e@B3')) g))   = regular $ SGR (SS1 (NO (pre a b) e)) g
cons a (D (SGR (SS1 (NO b@B3' e@B2')) g))   = regular $ SYR (SS1 (NO (pre a b) e)) g
cons a (D (SGR (SS1 (NO b@B3' e@B3')) g))   = regular $ SYR (SS1 (NO (pre a b) e)) g
cons a (D (SYG (SSC (NO b@B1' e@B1') f) g))    = regular $ SYG (SSC (NO (pre a b) e) f) g
cons a (D (SYG (SSC (NO b@B1' e@B2') f) g))    = regular $ SGG (SSC (NO (pre a b) e) f) g
cons a (D (SYG (SSC (NO b@B1' e@B3') f) g))    = regular $ SGG (SSC (NO (pre a b) e) f) g
cons a (D (SYG (SSC (NO b@B1' e@B4') f) g))    = regular $ SYG (SSC (NO (pre a b) e) f) g
cons a (D (SYG (SSC (NO b@B2' e@B1') f) g))    = regular $ SYG (SSC (NO (pre a b) e) f) g
cons a (D (SYG (SSC (NO b@B2' e@B4') f) g))    = regular $ SYG (SSC (NO (pre a b) e) f) g
cons a (D (SYG (SSC (NO b@B3' e@B1') f) g))    = regular $ SYG (SSC (NO (pre a b) e) f) g
cons a (D (SYG (SSC (NO b@B3' e@B4') f) g))    = regular $ SYG (SSC (NO (pre a b) e) f) g
cons a (D (SYG (SSC (NO b@B4' e@B1') f) g))    = regular $ SRG (SSC (NO (pre a b) e) f) g
cons a (D (SYG (SSC (NO b@B4' e@B2') f) g))    = regular $ SRG (SSC (NO (pre a b) e) f) g
cons a (D (SYG (SSC (NO b@B4' e@B3') f) g))    = regular $ SRG (SSC (NO (pre a b) e) f) g
cons a (D (SYG (SSC (NO b@B4' e@B4') f) g))    = regular $ SRG (SSC (NO (pre a b) e) f) g
cons a (D (SYG (SS1 (NO b@B1' e@B1')) g))      = regular $ SYG (SS1 (NO (pre a b) e)) g
cons a (D (SYG (SS1 (NO b@B1' e@B2')) g))      = regular $ SGG (SS1 (NO (pre a b) e)) g
cons a (D (SYG (SS1 (NO b@B1' e@B3')) g))      = regular $ SGG (SS1 (NO (pre a b) e)) g
cons a (D (SYG (SS1 (NO b@B1' e@B4')) g))      = regular $ SYG (SS1 (NO (pre a b) e)) g
cons a (D (SYG (SS1 (NO b@B2' e@B1')) g))      = regular $ SYG (SS1 (NO (pre a b) e)) g
cons a (D (SYG (SS1 (NO b@B2' e@B4')) g))      = regular $ SYG (SS1 (NO (pre a b) e)) g
cons a (D (SYG (SS1 (NO b@B3' e@B1')) g))      = regular $ SYG (SS1 (NO (pre a b) e)) g
cons a (D (SYG (SS1 (NO b@B3' e@B4')) g))      = regular $ SYG (SS1 (NO (pre a b) e)) g
cons a (D (SYG (SS1 (NO b@B4' e@B1')) g))      = regular $ SRG (SS1 (NO (pre a b) e)) g
cons a (D (SYG (SS1 (NO b@B4' e@B2')) g))      = regular $ SRG (SS1 (NO (pre a b) e)) g
cons a (D (SYG (SS1 (NO b@B4' e@B3')) g))      = regular $ SRG (SS1 (NO (pre a b) e)) g
cons a (D (SYG (SS1 (NO b@B4' e@B4')) g))      = regular $ SRG (SS1 (NO (pre a b) e)) g
{-- INLINE cons #-}

instance Reg Semi R r a b where
  regular (SR (SSC n1 (SS1 n2 ))) = case fixRGC n1 n2 of
    Left goryorr -> case goryorr of
      GG3 a b -> D $ combine2 a b CL
      GY3 a b -> D $ combine2 a b CL
      GR3 a b -> D $ combine2 a b CL
    Right d -> d
  regular (SR (SSC n1@(NO _ _) (SS1 n2@(NC _ _)))) =
    case fixRY n1 n2 of
      GG3 a b -> D $ combine2 a b CL
      GY3 a b -> D $ combine2 a b CL
      GR3 a b -> D $ combine2 a b CL
  regular (SRG (SS1 n1@(NO _ _)) (SG (SS1 n2@(NC _ _)))) =
    case fixRG n1 n2 of
      GG2 a b -> D $ combine2 a b CL
      GY2 a b -> D $ combine2 a b CL
  regular (SR (SSC n1 (SSC n2 ss))) =
    case fixRY n1 n2 of
      GG3 a b -> D $ combine2 a b ss
      GY3 a b -> D $ combine2 a b ss
      GR3 a b -> D $ combine2 a b ss
  regular (SRG (SS1 n1@(NO _ _)) (SG (SSC n2@(NO _ _) ss))) =
    case fixRG n1 n2 of
      GG2 a b -> D $ combine2 a b ss
      GY2 a b -> D $ combine2 a b ss
  regular (SRG (SS1 n1@(NO _ _)) (SGR (SS1 n2@(NO _ _)) s)) =
    case fixRG n1 n2 of
      GG2 a b -> D $ combine2 a b s
      GY2 a b -> D $ combine2 a b s
  regular (SRG (SS1 n1@(NO _ _)) (SGG (SS1 n2@(NO _ _)) s)) =
    case fixRG n1 n2 of
      GG2 a b -> D $ combine2 a b s
      GY2 a b -> D $ combine2 a b s
  regular (SRG (SS1 n1@(NO _ _)) (SGR (SSC n2@(NO _ _) ss) s)) =
    case fixRG n1 n2 of
      GG2 a b -> D $ combine2 a b (YR ss s)
      GY2 a b -> D $ combine2 a b (YR ss s)
  regular (SRG (SS1 n1@(NO _ _)) (SGG (SSC n2@(NO _ _) ss) s)) =
    case fixRG n1 n2 of
      GG2 a b -> D $ combine2 a b (YG ss s)
      GY2 a b -> D $ combine2 a b (YG ss s)
  regular (SRG (SSC n1@(NO _ _) (SS1 n2@(NO _ _))) s) =
    case fixRY n1 n2 of
      GG3 a b -> D $ combine2 a b s
      GY3 a b -> D $ combine2 a b s
      GR3 a b -> D $ combine2 a b s
  regular (SRG (SSC n1@(NO _ _) (SSC n2@(NO _ _) ss)) s) =
    case fixRY n1 n2 of
      GG3 a b -> D $ combine2 a b (YG ss s)
      GY3 a b -> D $ combine2 a b (YG ss s)
      GR3 a b -> D $ combine2 a b (YG ss s)

  regular (SR (SS1 (NC (B5 a b c d e) B0)))             = D $ go5 a b c d e
  regular (SR (SS1 (NC B0 (B5 a b c d e))))             = D $ go5 a b c d e
  regular (SR (SS1 (NC (B5 a b c d e) (B1 f))))         = D $ go6 a b c d e f
  regular (SR (SS1 (NC (B5 a b c d e) (B2 f g))))       = D $ SG (SSC (NO (B3 a b c) (B2 f g)) (SS1 (NC (B1 (P d e)) B0)))
  regular (SR (SS1 (NC (B5 a b c d e) (B3 f g h))))     = D $ SG (SSC (NO (B3 a b c) (B3 f g h)) (SS1 (NC (B1 (P d e)) B0)))
  regular (SR (SS1 (NC (B5 a b c d e) (B4 f g h i))))   = D $ SG (SSC (NO (B3 a b c) (B2 h i)) (SS1 (NC (B1 (P d e)) (B1 (P f g)))))
  regular (SR (SS1 (NC (B5 a b c d e) (B5 f g h i j)))) = D $ SG (SSC (NO (B3 a b c) (B3 h i j)) (SS1 (NC (B1 (P d e)) (B1 (P f g)))))
  regular (SR (SS1 (NC (B4 a b c d) (B5 f g h i j))))   = D $ SG (SSC (NO (B2 a b) (B3 h i j)) (SS1 (NC (B1 (P c d)) (B1 (P f g)))))
  regular (SR (SS1 (NC (B3 a b c) (B5 f g h i j))))     = D $ SG (SSC (NO (B3 a b c) (B3 h i j)) (SS1 (NC B0 (B1 (P f g)))))
  regular (SR (SS1 (NC (B2 a b) (B5 f g h i j))))       = D $ SG (SSC (NO (B2 a b) (B3 h i j)) (SS1 (NC B0 (B1 (P f g)))))
  regular (SR (SS1 (NC (B1 a) (B5 f g h i j))))         = D $ SG (SS1 (NC (B3 a f g) (B3 h i j)))
  {-- INLINE regular #-}


toGorYorR :: GorY t r a b -> GorYorR t r a b
toGorYorR = undefined

fixRGC :: HasColour k => Node R (Open (Pair r) c d) r a b -> Node k t (Pair r) c d -> Either (GorYorR t r a b) (Deque r a b)
fixRGC n1@(NO a b) n2@(NC c d) = case (unpost c, unpre d) of
  (BSnoc e f, BCons g h) -> Left $ case nodeColour n2 of
    G' -> toGorYorR $ fixRG n1 n2
    Y' -> fixRY n1 n2
  (BSEmpty, BCons g h@B1') -> Left $ fixRY n1 (NC (B1 g) h)
  (BSEmpty, BCons g h@B2') -> Left $ fixRY n1 (NC (B1 g) h)
  (BSEmpty, BCons g h@B3') -> Left $ fixRY n1 (NC (B1 g) h)
  (BSEmpty, BCons g h@B4') -> Left $ fixRY n1 (NC (B1 g) h)
  (BSnoc e@B1' f, BCEmpty) -> Left $ fixRY n1 (NC e (B1 f))
  (BSnoc e@B2' f, BCEmpty) -> Left $ fixRY n1 (NC e (B1 f))
  (BSnoc e@B3' f, BCEmpty) -> Left $ fixRY n1 (NC e (B1 f))
  (BSnoc e@B4' f, BCEmpty) -> Left $ fixRY n1 (NC e (B1 f))
  (BSEmpty, BCons (P g h) B0) ->
    case (a, b) of
      (B0, B0)             -> Right $ D $ go2 g h
      (B0, (B1 i))         -> Right $ D $ go3 g h i
      (B0, (B2 i j))       -> Right $ D $ go4 g h i j
      (B0, (B3 i j k))     -> Right $ D $ go5 g h i j k
      (B0, (B4 i j k l))   -> Right $ D $ go6 g h i j k l
      (B0, (B5 i j k l m)) -> Right $ D $ go7 g h i j k l m
      ((B1 a), B0)             -> Right $ D $ go3 a g h
{-      ((B1 a), (B1 i))         -> Right $ D $ go4 a g h i
      ((B1 a), (B2 i j))       -> Right $ D $ go5 a g h i j
      ((B1 a), (B3 i j k))     -> Right $ D $ go6 a g h i j k
      ((B1 a), (B4 i j k l))   -> Right $ D $ go7 a g h i j k l-}
      ((B1 a), (B5 i j k l m)) -> Right $ D $ go8 a g h i j k l m
      ((B2 a b), B0)             -> Right $ D $ go4 a b g h
{-      ((B2 a b), (B1 i))         -> Right $ D $ go5 a b g h i
      ((B2 a b), (B2 i j))       -> Right $ D $ go6 a b g h i j
      ((B2 a b), (B3 i j k))     -> Right $ D $ go7 a b g h i j k
      ((B2 a b), (B4 i j k l))   -> Right $ D $ go8 a b g h i j k l-}
      ((B2 a b), (B5 i j k l m)) -> Right $ D $ go9 a b g h i j k l m
      ((B3 a b c), B0)             -> Right $ D $ go5 a b c g h
{-      ((B3 a b c), (B1 i))         -> Right $ D $ go6 a b c g h i
      ((B3 a b c), (B2 i j))       -> Right $ D $ go7 a b c g h i j
      ((B3 a b c), (B3 i j k))     -> Right $ D $ go8 a b c g h i j k
      ((B3 a b c), (B4 i j k l))   -> Right $ D $ go9 a b c g h i j k l-}
      ((B3 a b c), (B5 i j k l m)) -> Right $ D $ go10 a b c g h i j k l m
      ((B4 a b c d), B0)             -> Right $ D $ go6 a b c d g h
{-      ((B4 a b c d), (B1 i))         -> Right $ D $ go7 a b c d g h i
      ((B4 a b c d), (B2 i j))       -> Right $ D $ go8 a b c d g h i j
      ((B4 a b c d), (B3 i j k))     -> Right $ D $ go9 a b c d g h i j k
      ((B4 a b c d), (B4 i j k l))   -> Right $ D $ go10 a b c d g h i j k l-}
      ((B4 a b c d), (B5 i j k l m)) -> Right $ D $ go11 a b c d g h i j k l m
      ((B5 a b c d e), B0)             -> Right $ D $ go7 a b c d e g h
      ((B5 a b c d e), (B1 i))         -> Right $ D $ go8 a b c d e g h i
      ((B5 a b c d e), (B2 i j))       -> Right $ D $ go9 a b c d e g h i j
      ((B5 a b c d e), (B3 i j k))     -> Right $ D $ go10 a b c d e g h i j k
      ((B5 a b c d e), (B4 i j k l))   -> Right $ D $ go11 a b c d e g h i j k l
      ((B5 a b c d e), (B5 i j k l m)) -> Right $ D $ go12 a b c d e g h i j k l m
  (BSnoc B0 (P g h), BCEmpty) ->
    case (a, b) of
      (B0, B0)             -> Right $ D $ go2 g h
      (B0, (B1 i))         -> Right $ D $ go3 g h i
      (B0, (B2 i j))       -> Right $ D $ go4 g h i j
      (B0, (B3 i j k))     -> Right $ D $ go5 g h i j k
      (B0, (B4 i j k l))   -> Right $ D $ go6 g h i j k l
      (B0, (B5 i j k l m)) -> Right $ D $ go7 g h i j k l m
      ((B1 a), B0)             -> Right $ D $ go3 a g h
{-      ((B1 a), (B1 i))         -> Right $ D $ go4 a g h i
      ((B1 a), (B2 i j))       -> Right $ D $ go5 a g h i j
      ((B1 a), (B3 i j k))     -> Right $ D $ go6 a g h i j k
      ((B1 a), (B4 i j k l))   -> Right $ D $ go7 a g h i j k l-}
      ((B1 a), (B5 i j k l m)) -> Right $ D $ go8 a g h i j k l m
      ((B2 a b), B0)             -> Right $ D $ go4 a b g h
{-      ((B2 a b), (B1 i))         -> Right $ D $ go5 a b g h i
      ((B2 a b), (B2 i j))       -> Right $ D $ go6 a b g h i j
      ((B2 a b), (B3 i j k))     -> Right $ D $ go7 a b g h i j k
      ((B2 a b), (B4 i j k l))   -> Right $ D $ go8 a b g h i j k l-}
      ((B2 a b), (B5 i j k l m)) -> Right $ D $ go9 a b g h i j k l m
      ((B3 a b c), B0)             -> Right $ D $ go5 a b c g h
{-      ((B3 a b c), (B1 i))         -> Right $ D $ go6 a b c g h i
      ((B3 a b c), (B2 i j))       -> Right $ D $ go7 a b c g h i j
      ((B3 a b c), (B3 i j k))     -> Right $ D $ go8 a b c g h i j k
      ((B3 a b c), (B4 i j k l))   -> Right $ D $ go9 a b c g h i j k l-}
      ((B3 a b c), (B5 i j k l m)) -> Right $ D $ go10 a b c g h i j k l m
      ((B4 a b c d), B0)             -> Right $ D $ go6 a b c d g h
{-      ((B4 a b c d), (B1 i))         -> Right $ D $ go7 a b c d g h i
      ((B4 a b c d), (B2 i j))       -> Right $ D $ go8 a b c d g h i j
      ((B4 a b c d), (B3 i j k))     -> Right $ D $ go9 a b c d g h i j k
      ((B4 a b c d), (B4 i j k l))   -> Right $ D $ go10 a b c d g h i j k l-}
      ((B4 a b c d), (B5 i j k l m)) -> Right $ D $ go11 a b c d g h i j k l m
      ((B5 a b c d e), B0)             -> Right $ D $ go7 a b c d e g h
      ((B5 a b c d e), (B1 i))         -> Right $ D $ go8 a b c d e g h i
      ((B5 a b c d e), (B2 i j))       -> Right $ D $ go9 a b c d e g h i j
      ((B5 a b c d e), (B3 i j k))     -> Right $ D $ go10 a b c d e g h i j k
      ((B5 a b c d e), (B4 i j k l))   -> Right $ D $ go11 a b c d e g h i j k l
      ((B5 a b c d e), (B5 i j k l m)) -> Right $ D $ go12 a b c d e g h i j k l m
  (BSEmpty, BCEmpty) ->
    case (a, b) of
      (B0, B0)             -> Right $ empty
      (B0, (B1 i))         -> Right $ D $ go1 i
      (B0, (B2 i j))       -> Right $ D $ go2 i j
      (B0, (B3 i j k))     -> Right $ D $ go3 i j k
      (B0, (B4 i j k l))   -> Right $ D $ go4 i j k l
      (B0, (B5 i j k l m)) -> Right $ D $ go5 i j k l m
      ((B1 a), B0)             -> Right $ D $ go1 a
{-      ((B1 a), (B1 i))         -> Right $ D $ go4 a i
      ((B1 a), (B2 i j))       -> Right $ D $ go5 a i j
      ((B1 a), (B3 i j k))     -> Right $ D $ go6 a i j k
      ((B1 a), (B4 i j k l))   -> Right $ D $ go7 a i j k l-}
      ((B1 a), (B5 i j k l m)) -> Right $ D $ go6 a i j k l m
      ((B2 a b), B0)             -> Right $ D $ go2 a b
{-      ((B2 a b), (B1 i))         -> Right $ D $ go5 a b i
      ((B2 a b), (B2 i j))       -> Right $ D $ go6 a b i j
      ((B2 a b), (B3 i j k))     -> Right $ D $ go7 a b i j k
      ((B2 a b), (B4 i j k l))   -> Right $ D $ go8 a b i j k l-}
      ((B2 a b), (B5 i j k l m)) -> Right $ D $ go7 a b i j k l m
      ((B3 a b c), B0)             -> Right $ D $ go3 a b c
{-      ((B3 a b c), (B1 i))         -> Right $ D $ go6 a b c i
      ((B3 a b c), (B2 i j))       -> Right $ D $ go7 a b c i j
      ((B3 a b c), (B3 i j k))     -> Right $ D $ go8 a b c i j k
      ((B3 a b c), (B4 i j k l))   -> Right $ D $ go9 a b c i j k l-}
      ((B3 a b c), (B5 i j k l m)) -> Right $ D $ go8 a b c i j k l m
      ((B4 a b c d), B0)             -> Right $ D $ go4 a b c d
{-      ((B4 a b c d), (B1 i))         -> Right $ D $ go7 a b c d i
      ((B4 a b c d), (B2 i j))       -> Right $ D $ go8 a b c d i j
      ((B4 a b c d), (B3 i j k))     -> Right $ D $ go9 a b c d i j k
      ((B4 a b c d), (B4 i j k l))   -> Right $ D $ go10 a b c d i j k l-}
      ((B4 a b c d), (B5 i j k l m)) -> Right $ D $ go9 a b c d i j k l m
      ((B5 a b c d e), B0)             -> Right $ D $ go5 a b c d e
      ((B5 a b c d e), (B1 i))         -> Right $ D $ go6 a b c d e i
      ((B5 a b c d e), (B2 i j))       -> Right $ D $ go7 a b c d e i j
      ((B5 a b c d e), (B3 i j k))     -> Right $ D $ go8 a b c d e i j k
      ((B5 a b c d e), (B4 i j k l))   -> Right $ D $ go9 a b c d e i j k l
      ((B5 a b c d e), (B5 i j k l m)) -> Right $ D $ go10 a b c d e i j k l m
{-- INLINE fixRGC #-}

class HasColour c where
  colour :: p c -> ColourType c

data ColourType a where
  R' :: ColourType R
  Y' :: ColourType Y
  G' :: ColourType G

data Proxy a where
  Proxy :: Proxy a

instance HasColour R where
  colour _ = R'

instance HasColour G where
  colour _ = G'

instance HasColour Y where
  colour _ = Y'

nodeColour :: forall c t r a b.  HasColour c => Node c t r a b -> ColourType c
nodeColour _ = colour (Proxy :: Proxy c)

stackColour :: forall c reg r a b.  HasColour c => Stack reg c r a b -> ColourType c
stackColour _ = colour (Proxy :: Proxy c)

fixRG :: Node R (Open (Pair r) c d) r a b -> Node G t (Pair r) c d -> GorY t r a b
fixRG (NO a b) (NO c d) =
  case (lb' a c, rb' d b) of
    (LBP e f, RBP g h) ->
      let n2 = toNO f g in
      let n1 = toNO e h in
      case (n1, n2) of
        (NO _ _, NO _ _) -> case (nodeColour n1, nodeColour n2) of
          (G', Y') -> GY2 n1 n2
          (G', G') -> GG2 n1 n2
fixRG (NO a b) (NC c d) =
  case (lb' a c, rb' d b) of
    (LBP e f, RBP g h) ->
      let n2 = toNC f g in
      let n1 = toNO e h in
      case (n1, n2) of
        (NO _ _, NC _ _) -> case (nodeColour n1, nodeColour n2) of
          (G', Y') -> GY2 n1 n2
          (G', G') -> GG2 n1 n2

fixRY :: Node R (Open (Pair r) c d) r a b -> Node Y t (Pair r) c d -> GorYorR t r a b
fixRY (NO a b) (NO c d) =
  case (lb' a c, rb' d b) of
    (LBP e f, RBP g h) ->
      let n2 = toNO f g in
      let n1 = toNO e h in
      case (n1, n2) of
        (NO _ _, NO _ _) -> case (nodeColour n1, nodeColour n2) of
          (G', Y') -> GY3 n1 n2
          (G', G') -> GG3 n1 n2
          (G', R') -> GR3 n1 n2
fixRY (NO a b) (NC c d) =
  case (lb' a c, rb' d b) of
    (LBP e f, RBP g h) ->
      let n2 = toNC f g in
      let n1 = toNO e h in
      case (n1, n2) of
        (NO _ _, NC _ _) -> case (nodeColour n1, nodeColour n2) of
          (G', Y') -> GY3 n1 n2
          (G', G') -> GG3 n1 n2
          (G', R') -> GR3 n1 n2
