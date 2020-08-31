{-# Language BlockArguments #-}
{-# Language ImportQualifiedPost #-}
{-# Language ExistentialQuantification #-}
{-# Language LambdaCase #-}
{-# Language DeriveAnyClass #-}

-- |
-- Copyright :  (c) Edward Kmett and András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Ergo.Elaborate.Error where

import Control.Exception
import Control.Monad.Catch as M
import Ergo.Elaborate.Monad
import Ergo.Elaborate.Term
import Ergo.Elaborate.Value
import Ergo.Icit
import Ergo.Names
import Text.Megaparsec (SourcePos)

data SpineError
  = SpineNonVar
  | SpineProjection
  | NonLinearSpine Lvl
  deriving (Show, Exception)

data StrengtheningError
  = ScopeError Lvl
  | OccursCheck
  deriving (Show, Exception)

data UnifyError
  = forall s. UnifyError [Name s] (TM s) (TM s)
  | forall s. SpineError [Name s] (TM s) (TM s) SpineError
  | forall s. StrengtheningError [Name s] (TM s) (TM s) StrengtheningError
  deriving Exception

instance Show UnifyError where
  show _ = "UnifyError..."

-- type TM s = Tm (Meta s)

data ElabError
  = IcitMismatch Icit Icit
  | forall s. ExpectedFunction (TM s)
  | forall s. NameNotInScope (Name s)
  | forall s. UnifyErrorWhile (TM s) (TM s) UnifyError
  deriving (Exception)

instance Show ElabError where
  show _ = "ElabError..."

data Err = forall s. Err [Name s] ElabError (Maybe SourcePos)

instance Exception Err where
  -- displayException (Err ns e p) = prettyErr ns e

instance Show Err where
  show _ = "Err..."

  {- 
  showsPrec d (Err ns ee p) = showParen (d > 10) $
    showString "Err " . showsPrec 11 ns . showChar ' ' 
                      . showsPrec 11 ee . showChar ' '
                      . showsPrec 11 p
-}

addSourcePos :: SourcePos -> M s a -> M s a
addSourcePos p act = act `M.catch` \case
  Err ns e Nothing -> throwM $ Err ns e (Just p)
  e -> throwM e

reportM :: [Name s] -> ElabError -> M s a
reportM ns e = throwM $ Err ns e Nothing

report :: [Name s] -> ElabError -> a
report ns e = throw $ Err ns e Nothing

