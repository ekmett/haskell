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

pattern Zero :: Use
pattern Zero = USE 0

pattern One :: Use
pattern One = USE 1

pattern Many :: Use
pattern Many = USE 2

data Use = USE Int
  deriving (Eq,Ord)

instance Enum Use where
  fromEnum (USE n) = n

  toEnum 0 = Zero
  toEnum 1 = One
  toEnum 2 = Many
  toEnum _ = error "toEnum @Use: out of bounds"

  succ Zero = One
  succ One = Many
  succ Many = error "succ @Use ω"

  pred Zero = error "pred @Use 0"
  pred One = Zero
  pred Many = One

instance Bounded Use where
  minBound = Zero
  maxBound = Many

{-# COMPLETE Zero, One, Many #-}

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

data Used t a = {-# UNPACK #-} !Use :* t a
  deriving (Functor, Foldable, Show)

infixr 8 :*
