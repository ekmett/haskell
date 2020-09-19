{-# Language FlexibleContexts #-}

module Driver where

import Control.Applicative
import Control.Monad.Primitive
import Data.GADT.Compare
import Data.Dependent.HashMap
import Data.Hashable
import Data.Primitive.MutVar
import Make

data DriverState s q e = DriverState
  { _startedVar :: !(MutVar s (DHashMap q (MemoEntry s)))
  , _hashesVar :: !(MutVar s (DHashMap q (Const Int)))
  , _reverseDependenciesVar :: !(MutVar s (ReverseDependencies q))
  , _tracesVar :: !(MutVar s (Traces q (Const Int)))
  , _errorsVar :: !(MutVar s (DHashMap q (Const [e])))
  }

newDriverState 
  :: (PrimMonad m, GEq q, Hashable (Some q)) 
  => m (DriverState (PrimState m) q e)
newDriverState = stToPrim $ DriverState 
  <$> newMutVar mempty
  <*> newMutVar mempty
  <*> newMutVar mempty
  <*> newMutVar mempty
  <*> newMutVar mempty

