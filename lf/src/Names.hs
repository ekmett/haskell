{-# Language BlockArguments #-}
{-# Language ImportQualifiedPost #-}

-- |
-- Copyright :  (c) Edward Kmett 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Names (Name, naming, metaNaming) where

import Control.Lens (review)
import Numeric.Lens (base)
import Data.Hashable
import Data.HashMap.Strict qualified as HM
import Control.Monad.Trans.State.Strict

type Name = String

names :: [Name]
names = map pure az
    ++ [ i : review (base 36) j | j <- [1 :: Int ..], i <- az ] where
  az = ['a'..'z']

metaNames :: [Name]
metaNames = map ('?':) names

-- useful for renaming metas
naming :: (Traversable f, Eq a, Hashable a) => [b] -> f a -> f b
naming ns0 xs0 = evalState (traverse f xs0) (HM.empty, ns0) where
  f a = state \ s@(hm,ns) -> case HM.lookup a hm of
    Nothing -> case ns of
      (n:ns') -> (n, (HM.insert a n hm, ns'))
      _ -> error "out of names"
    Just n -> (n, s)

metaNaming :: (Traversable f, Eq a, Hashable a) => f a -> f Name
metaNaming = naming metaNames
