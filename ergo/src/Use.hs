{-# Language PolyKinds #-}
{-# Language Strict #-}
{-# Language PatternSynonyms #-}
{-# Language DeriveTraversable #-}

-- |
-- Copyright :  (c) Edward Kmett 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Use
  ( Use(..)
  , ω 
  , Scalable(..)
  , Used(..)
  ) where

--------------------------------------------------------------------------------
-- * Use
--------------------------------------------------------------------------------

data Use = Zero | One | Many
  deriving (Eq,Ord,Enum,Bounded)

instance Show Use where
  showsPrec _ Zero = showChar '0'
  showsPrec _ One  = showChar '1'
  showsPrec _ Many = showChar 'ω'

ω :: Use
ω = Many

instance Num Use where
  Zero + n = n
  n + Zero = n
  Many + _ = Many
  _ + Many = Many
  One + One = Many

  Zero * _ = Zero
  _ * Zero = Zero
  One * n = n
  n * One = n
  Many * Many = Many

  negate Zero = Zero
  negate _ = error "negate @Use: undefined"

  n   - Zero = n
  One - One = Zero
  _ - _ = error "(-) @Use: undefined"

  abs = id

  signum Zero = Zero
  signum _ = One

  fromInteger 0 = Zero
  fromInteger 1 = One
  fromInteger _ = Many

class Scalable t where
  scale :: Use -> t a -> t a

instance Scalable (Used t) where
  scale One u = u
  scale n (n' :* t) = (n*n') :* t

data Used t a = !Use :* t a
  deriving (Functor, Foldable, Show)

infixr 8 :*
