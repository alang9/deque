{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Main
       ( main
       ) where

import Control.DeepSeq
import Criterion.Main
import Data.List (unfoldr)
import qualified Data.Sequence as Seq

import Data.Deque.Cat as C
import Data.Deque.NonCat as NC
-- import Data.Deque.NonCat.LessTyped as NCLT

main :: IO ()
main = defaultMain
  [ bgroup "pushThenPop"
    [ bench "Cat"    $ nf (unCDeq . mkCDeq) [0..1000]
    , bench "NonCat" $ nf (unNCDeq . mkNCDeq) [0..1000]
    -- , bench "NonCat LessTyped" $ nf (unNCLTDeq . mkNCLTDeq) [0..1000]
    , bench "Seq"    $ nf (unSeq . mkSeq) [0..1000]
    ]
  , bgroup "concatChunkThenPop"
    [ bgroup "singleton"
      [ bench "Cat"    $ nf (unCDeq . foldr C.catenate C.empty . map (C.singleton . Foo)) [0..1000]
      , bench "Seq"    $ nf (unSeq . foldr (Seq.><) Seq.empty . map (Seq.singleton . Foo)) [0..1000]
      ]
    , bgroup "5"
      [ bench "Cat"    $ nf (unCDeq . foldr C.catenate C.empty . map mkCDeq . splits 5) [0..1000]
      , bench "Seq"    $ nf (unSeq . foldr (Seq.><) Seq.empty . map mkSeq . splits 5) [0..1000]
      ]
    , bgroup "10"
      [ bench "Cat"    $ nf (unCDeq . foldr C.catenate C.empty . map mkCDeq . splits 10) [0..1000]
      , bench "Seq"    $ nf (unSeq . foldr (Seq.><) Seq.empty . map mkSeq . splits 10) [0..1000]
      ]
    , bgroup "20"
      [ bench "Cat"    $ nf (unCDeq . foldr C.catenate C.empty . map mkCDeq . splits 20) [0..1000]
      , bench "Seq"    $ nf (unSeq . foldr (Seq.><) Seq.empty . map mkSeq . splits 20) [0..1000]
      ]
    ]
  ]

data Foo a b where
  Foo :: !Int -> Foo () ()

instance NFData (Foo a b) where
  rnf !_ = ()

splits :: Int -> [a] -> [[a]]
splits n xs = case splitAt n xs of
  (xs', []) -> [xs']
  (xs', xs'') -> xs' : splits n xs''

mkCDeq :: [Int] -> C.Deque (C.Closed C.Green) (C.Closed C.Green) Foo () ()
mkCDeq xs = foldr (\a d -> C.push (Foo a) d) C.empty xs

unCDeq :: C.Deque (C.Closed C.Green) (C.Closed C.Green) Foo () () -> [Int]
unCDeq = unfoldr go
  where
    go :: C.Deque (C.Closed C.Green) (C.Closed C.Green) Foo () () -> Maybe (Int, C.Deque (C.Closed C.Green) (C.Closed C.Green) Foo () ())
    go d = case C.pop d of
      Foo a C.:| d' -> Just (a, d')
      C.Empty -> Nothing

mkNCDeq :: [Int] -> NC.Deque Foo () ()
mkNCDeq xs = foldr (\a d -> (Foo a) NC.<| d) NC.empty xs

unNCDeq :: NC.Deque Foo () () -> [Int]
unNCDeq = unfoldr go
  where
    go :: NC.Deque Foo () () -> Maybe (Int, NC.Deque Foo () ())
    go d = case NC.uncons d of
      Foo a NC.:| d' -> Just (a, d')
      NC.Empty -> Nothing

-- mkNCLTDeq :: [Int] -> NCLT.Deque Foo () ()
-- mkNCLTDeq xs = foldr (\a d -> (F a) NCLT.<| d) NCLT.empty xs

-- unNCLTDeq :: NCLT.Deque Foo () () -> [Int]
-- unNCLTDeq = unfoldr go
--   where
--     go :: NCLT.Deque Foo () () -> Maybe (Int, NCLT.Deque Foo () ())
--     go d = case NCLT.uncons d of
--       F a NCLT.:| d' -> Just (a, d')
--       NCLT.Empty -> Nothing

mkSeq :: [Int] -> Seq.Seq (Foo () ())
mkSeq xs = foldr (\a d -> (Foo a) Seq.<| d) Seq.empty xs

unSeq :: Seq.Seq (Foo () ()) -> [Int]
unSeq = unfoldr go
  where
    go :: Seq.Seq (Foo () ()) -> Maybe (Int, Seq.Seq (Foo () ()))
    go s = case Seq.viewl s of
      Foo a Seq.:< d' -> Just (a, d')
      Seq.EmptyL -> Nothing
