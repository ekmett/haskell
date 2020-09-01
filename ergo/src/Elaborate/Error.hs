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

module Elaborate.Error where

import Control.Exception
import Elaborate.Term
import Elaborate.Value
import Icit
import Names
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
  = UnifyError [Name] TM TM 
  | SpineError [Name] TM TM SpineError
  | StrengtheningError [Name] TM TM StrengtheningError
  deriving Exception

instance Show UnifyError where
  show _ = "UnifyError..."

data ElabError
  = IcitMismatch Icit Icit
  | ExpectedFunction TM
  | NameNotInScope Name
  | UnifyErrorWhile TM TM UnifyError
  deriving Exception

instance Show ElabError where
  show _ = "ElabError..."

data Err = Err [Name] ElabError (Maybe SourcePos)

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

addSourcePos :: SourcePos -> IO a -> IO a
addSourcePos p act = act `catch` \case
  Err ns e Nothing -> throwIO $ Err ns e (Just p)
  e -> throwIO e

reportM :: [Name] -> ElabError -> IO a
reportM ns e = throwIO $ Err ns e Nothing

report :: [Name] -> ElabError -> a
report ns e = throw $ Err ns e Nothing
