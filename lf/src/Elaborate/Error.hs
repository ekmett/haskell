{-# Language BlockArguments #-}
{-# Language ImportQualifiedPost #-}

-- |
-- Copyright :  (c) Edward Kmett 2020, András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Elaborate.Error where

--import Text.Megaparsec (SourcePos)
-- import Control.Monad.ST
-- import Control.Monad.ST.Unsafe

-- type TM s = Tm (Meta s)

{-
data SpineError 
  = SpineNonVar 
  | SpineProjection
  | NonLinearSpine Lvl

data StrengtheningError
  = ScopeError Lvl
  | OccursCheck

data UnifyError a
  = UnifyError [Name] (Tm a) (Tm a)
  | SpineError [Name] (Tm a) (Tm a) SpineError
  | StrengtheningError [Name] (Tm a) (Tm a) StrengtheningError
  deriving (Functor, Foldable, Traversable)

data ElabError
  = IcitMismatch Icit Icit
  | ∀s. ExpectedFunction (TM s)
  | NameNotInScope Name
  | ∀s. UnifyErrorWhile (TM s) (TM s) (UnifyError (Meta s))
  deriving (Exception)

data Err = Err [Name] ElabError (Maybe SourcePos)

instance Show Err where
  showsPrec d (Err ns ee p) = showParen (d > 10) $
    showString "Err " . showsPrec 11 ns . showChar ' ' 
                      . showsPrec 11 ee . showChar ' '
                      . showsPrec 11 p

addSourcePos :: forall s. SourcePos -> IO a -> IO a
addSourcePos p act = act `catch` \case
  Err ns e Nothing -> throwIO $ Err ns e (Just p)
  e -> throwIO e

reportST :: [Name] -> ElabError -> ST s a
reportST ns e = unsafeIOtoSt throwIO $ Err ns e Nothing

report :: [Name] -> ElabError -> a
report ns e = throw $ Err ns e Nothing

instance Exception Err where
  displayException (Err ns e p) = prettyErr ns e
-}
