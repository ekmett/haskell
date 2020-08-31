{-# Language RankNTypes #-}
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
  = Var !SourceName
  | Lam !SourceName !(Maybe Term) !Icit !Term
  | App !Icit !Term !Term
  | Pi  !SourceName !Icit !Term !Term
  | Let !SourceName !Term !Term !Term
  | U
  | Hole
  | Loc !SourcePos !Term
