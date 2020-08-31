{-# Language BlockArguments #-}
{-# Language ImportQualifiedPost #-}
{-# Language RankNTypes #-}
{-# Language DeriveAnyClass #-}
{-# Language DeriveGeneric #-}

-- |
-- Copyright :  (c) Edward Kmett 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Ergo.Names 
  ( SourceName
  , Name(..)
  , naming
  , metaNaming
  , splitName
  , sourceName
  ) where

import Control.Lens (review)
import Control.Monad.Trans.State.Strict
import Data.HashMap.Strict qualified as HM
import Data.Hashable
import Data.Text.Short as Short
import Ergo.Unique
import Numeric.Lens (base)
import Data.String
import GHC.Generics
import Numeric.Natural

data Name s
  = SourceName ShortText Natural
  | MetaName (Unique s) Natural
  deriving (Eq,Generic,Hashable)

type SourceName = ShortText

instance IsString (Name s) where
  fromString s = SourceName (Short.fromString s) 0
  {-# inline fromString #-}

splitName :: Name s -> (Name s, Name s)
splitName (SourceName s n) = (SourceName s (2*n+1), SourceName s (2*n+2))
splitName (MetaName s n) = (MetaName s (2*n+1), MetaName s (2*n+2))

sourceName :: SourceName -> Name s
sourceName s = SourceName s 0

-- todo: ShortText or interning

-- type Name = String

names :: [String]
names = map pure az
    ++ [ i : review (base 36) j | j <- [1 :: Int ..], i <- az ] where
  az = ['a'..'z']

metaNames :: [String]
metaNames = map ('?':) names

-- useful for renaming metas
naming :: (Traversable f, Eq a, Hashable a) => [b] -> f a -> f b
naming ns0 xs0 = evalState (traverse f xs0) (HM.empty, ns0) where
  f a = state \ s@(hm,ns) -> case HM.lookup a hm of
    Nothing -> case ns of
      (n:ns') -> (n, (HM.insert a n hm, ns'))
      _ -> error "out of names"
    Just n -> (n, s)

metaNaming :: (Traversable f, Eq a, Hashable a) => f a -> f String
metaNaming = naming metaNames
