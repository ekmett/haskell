module Relative
  ( Relative(..)
  , RelativeSemigroup
  , RelativeMonoid
  ) where

import Delta
import Unaligned.Internal (Rev(..))

--------------------------------------------------------------------------------
-- * Interface
--------------------------------------------------------------------------------

-- group action
class Relative a where
  rel :: Delta -> a -> a

instance Relative a => Relative (Maybe a) where
  rel = fmap . rel

-- | @rel d (a <> b) = rel d a <> rel d b@
class (Relative a, Semigroup a) => RelativeSemigroup a

-- | @rel d mempty = mempty@
class (Relative a, RelativeSemigroup a, Monoid a) => RelativeMonoid a

instance Relative (f a) => Relative (Rev f a) where
  rel d (Rev as) = Rev (rel d as)
