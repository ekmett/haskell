{-# Language StrictData #-}

-- |
-- Copyright :  (c) Edward Kmett 2020, András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Source.Term where

import Icit
import Names
import Text.Megaparsec (SourcePos)

data Term
  = Var Name
  | Lam Name (Maybe Term) Icit Term
  | App Icit Term Term
  | Pi  Name Icit Term Term
  | Let Name Term Term Term
  | U
  | Hole
  | Loc SourcePos Term
  deriving (Eq,Show)
