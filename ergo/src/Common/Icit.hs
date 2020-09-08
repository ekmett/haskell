-- |
-- Copyright :  (c) Edward Kmett 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Common.Icit where

data Icit
  = Implicit
  | Explicit 
  deriving (Eq,Ord,Show,Read,Bounded,Enum)
