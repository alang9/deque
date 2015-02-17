{-# OPTIONS -Wall -fdefer-type-errors #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module NonCat where

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

data Genus a where
  Closed :: Genus a
  Open :: (a -> a -> a) -> a -> a -> Genus a

data Pair r a b where
  P :: r b c -> r a b -> Pair r a c

data Node' c (t :: Genus *) r a b where
  NO :: Buffer c2 r c d -> Buffer c1 r a b -> Node' (MinO c1 c2) (Open (Pair r) b c) r a d
  NC :: Buffer c2 r b c -> Buffer c1 r a b -> Node' (MinC c1 c2) Closed r a c

data SubStack c (t :: Genus *) r a b where
  SS1 :: Node' c1 t r a b -> SubStack c1 t r a b
  SSC :: Node' c1 (Open (Pair r) a b) r c d -> SubStack Y t (Pair r) a b -> SubStack c1 t r c d

data Regular = Full | Semi


data Stack reg c1 r a b where
  SY :: SubStack Y Closed r a b -> Stack Full Y r a b
  SG :: SubStack G Closed r a b -> Stack Full G r a b
  SR :: SubStack R Closed r a b -> Stack Semi R r a b
  SYG :: SubStack Y (Open (Pair r) c d) r a b -> Stack Full G (Pair r) c d -> Stack Full Y r a b
  SRG :: SubStack R (Open (Pair r) c d) r a b -> Stack Full G (Pair r) c d -> Stack Semi R r a b
  SYR :: SubStack Y (Open (Pair r) c d) r a b -> Stack Semi R (Pair r) c d -> Stack Semi Y r a b
  SGR :: SubStack G (Open (Pair r) c d) r a b -> Stack Semi R (Pair r) c d -> Stack Full G r a b
  SGG :: SubStack G (Open (Pair r) c d) r a b -> Stack Full G (Pair r) c d -> Stack Full G r a b

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

instance Reg Semi R G r a b where
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
  regular (SR (SS1 (NC (B4 _ _ _ _) (B4 _ _ _ _)))) = undefined
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

  regular (SRG _ _) = undefined -- TODO
  regular (SR (SSC _ (SSC _ _))) = undefined -- TODO

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
{-
  regular (SR (SSC (NO B0 B0) (SSC (NO (B1 (P a b)) (B1 (P c d))) rest))) = SGR (SS1 (NO (B2 a b) (B2 c d))) (SR (SSC (NO B0 B0) rest))
  regular (SR (SSC (NO B0 B0) (SSC (NO (B1 (P a b)) (B2 c (P e f))) rest))) = SGR (SS1 (NO (B2 a b) (B2 e f))) (SR (SSC (NO B0 (B1 c)) rest))
  regular (SR (SSC (NO B0 B0) (SSC (NO (B1 (P a b)) (B3 c d (P e f))) rest))) = SGR (SS1 (NO (B2 a b) (B2 e f))) (SR (SSC (NO B0 (B2 c d)) rest))
  regular (SR (SSC (NO B0 B0) (SSC (NO (B1 (P a b)) (B4 c d e (P f g))) rest))) = SGR (SS1 (NO (B2 a b) (B2 f g))) (SR (SSC (NO B0 (B3 c d e)) rest))
  regular (SR (SSC (NO B0 B0) (SSC (NO (B2 (P a b) c) (B1 (P f g))) rest))) = SGR (SS1 (NO (B2 a b) (B2 f g))) (SR (SSC (NO (B1 c) B0) rest))
  regular (SR (SSC (NO B0 B0) (SSC (NO (B3 (P a b) c d) (B1 (P f g))) rest))) = SGR (SS1 (NO (B2 a b) (B2 f g))) (SR (SSC (NO (B2 c d) B0) rest))
  regular (SR (SSC (NO B0 B0) (SSC (NO (B4 (P a b) c d e) (B1 (P f g))) rest))) = SGR (SS1 (NO (B2 a b) (B2 f g))) (SR (SSC (NO (B3 c d e) B0) rest))
  regular (SR (SSC (NO B0 B0) (SSC (NO (B4 (P a b) c d e) (B2 h (P i j))) rest))) = SG (SSC (NO (B2 a b) (B2 i j)) (SSC (NO (B3 c d e) (B1 h)) rest))
  regular (SR (SSC (NO B0 B0) (SSC (NO (B4 (P a b) c d e) (B3 g h (P i j))) rest))) = SGG (SS1 (NO (B2 a b) (B2 i j))) (SG (SSC (NO (B3 c d e) (B2 g h)) rest))
  regular (SR (SSC (NO B0 B0) (SSC (NO (B4 (P a b) c d e) (B4 f g h (P i j))) rest))) = SGG (SS1 (NO (B2 a b) (B2 i j))) (SG (SSC (NO (B3 c d e) (B3 f g h)) rest))
-}
