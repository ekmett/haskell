{-# language DeriveFunctor #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns -Wno-missing-export-lists #-}
module Bayes where

import Control.Monad
import Data.Functor
import Data.Void
-- import Numeric.Log
-- import Statistics.Distribution
import System.Random

data Prob s a
  = Pure a
  | Uniform (Double -> Prob s a)
  | Score (Prob s a) s
  deriving Functor

instance Applicative (Prob s) where
  pure = Pure
  (<*>) = ap

instance Monad (Prob s) where
  return = Pure
  Pure a >>= f = f a
  Uniform k >>= f = Uniform $ k >=> f
  Score r d >>= f = Score (r >>= f) d

uniform01 :: Prob s Double
uniform01 = Uniform Pure

score :: s -> Prob s ()
score = Score (Pure ())

sample :: RandomGen g => g -> Prob Void a -> (a, g)
sample g (Pure a) = (a, g)
sample g (Uniform k) = case random g of
  (x, g') -> sample g' (k x)
sample _ (Score _ s) = absurd s

data Trace s a = Trace
  { traceValue :: a
  , traceScore :: s
  , traceLength :: {-# unpack #-} !Int
  , traceElements :: [Double]
  }

-- TODO: tree form, capture continuations, applicative-do-better, 
-- free commutative monad given a commutative applicative,
-- selective, hmc, etc.

trace :: Num s => Prob s a -> Prob s' (Trace s a)
trace t0 = go t0 <&> \t -> t { traceElements = reverse (traceElements t) } where
  go (Pure a) = Pure (Trace a 1 0 [])
  go (Score m s) = go m <&> \t -> t { traceScore = traceScore t * s }
  go (Uniform k) = do
    r <- uniform01
    go (k r) <&> \t -> t
      { traceElements = r : traceElements t
      , traceLength = traceLength t + 1
      }

feed :: [Double] -> Prob s a -> Prob s a
feed (x:xs) (Uniform k) = feed xs (k x)
feed xs (Score a s) = Score (feed xs a) s
feed [] m = m
feed _ r@Pure{} = r

-- mutate a path
gibbs :: Trace Double a -> Prob s [Double]
gibbs xs
  | traceLength xs == 0 = pure []
  | otherwise = do
  i <- uniformInt 0 $ traceLength xs - 1
  uniform01 <&> \r -> replaceAt i r (traceElements xs)

uniformInt :: Int -> Int -> Prob s Int
uniformInt i j = uniform01 <&> \d -> floor $ d * fromIntegral (j+1-i)

replaceAt :: Int -> a -> [a] -> [a]
replaceAt i a ~(x:xs)
  | i == 0 = a:xs
  | otherwise = x:replaceAt (i-1) a xs

step :: Prob s (Trace Double a) -> Trace Double a -> Prob s (Trace Double a)
step r t = do
  xs <- gibbs t
  t' <- feed xs r
  let p = traceScore t' / traceScore t
  if p >= 1
  then pure $ extend t t'
  else uniform01 <&> \r' -> if r' < p then extend t t' else t

extend :: Trace r a -> Trace r b -> Trace r b
extend t t'
  | traceLength t' >= traceLength t = t'
  | otherwise = t' { traceElements = traceElements t' <> drop (traceLength t') (traceElements t) }

