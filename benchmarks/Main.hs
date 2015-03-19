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

main :: IO ()
main = defaultMain
  [ bgroup "pushThenPop"
    [ bench "Cat"    $ nf (unCDeq . mkCDeq) [0..1000]
    , bench "NonCat" $ nf (unNCDeq . mkNCDeq) [0..1000]
    , bench "Seq"    $ nf (unSeq . mkSeq) [0..1000]
    ]
  , bgroup "concatChunkThenPop"
    [ bgroup "5"
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
  F :: !Int -> Foo () ()

instance NFData (Foo a b) where
  rnf !_ = ()

splits :: Int -> [a] -> [[a]]
splits n xs = case splitAt n xs of
  (xs', []) -> [xs']
  (xs', xs'') -> xs' : splits n xs''

mkCDeq :: [Int] -> C.Deque (C.Closed C.Green) (C.Closed C.Green) Foo () ()
mkCDeq xs = foldr (\a d -> C.push (F a) d) C.empty xs

unCDeq :: C.Deque (C.Closed C.Green) (C.Closed C.Green) Foo () () -> [Int]
unCDeq = unfoldr go
  where
    go :: C.Deque (C.Closed C.Green) (C.Closed C.Green) Foo () () -> Maybe (Int, C.Deque (C.Closed C.Green) (C.Closed C.Green) Foo () ())
    go d = case C.pop d of
      F a C.:| d' -> Just (a, d')
      C.Empty -> Nothing

mkNCDeq :: [Int] -> NC.Deque Foo () ()
mkNCDeq xs = foldr (\a d -> (F a) NC.<| d) NC.empty xs

unNCDeq :: NC.Deque Foo () () -> [Int]
unNCDeq = unfoldr go
  where
    go :: NC.Deque Foo () () -> Maybe (Int, NC.Deque Foo () ())
    go d = case NC.uncons d of
      F a NC.:| d' -> Just (a, d')
      NC.Empty -> Nothing

mkSeq :: [Int] -> Seq.Seq (Foo () ())
mkSeq xs = foldr (\a d -> (F a) Seq.<| d) Seq.empty xs

unSeq :: Seq.Seq (Foo () ()) -> [Int]
unSeq = unfoldr go
  where
    go :: Seq.Seq (Foo () ()) -> Maybe (Int, Seq.Seq (Foo () ()))
    go s = case Seq.viewl s of
      F a Seq.:< d' -> Just (a, d')
      Seq.EmptyL -> Nothing
