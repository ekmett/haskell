{-# Language PatternSynonyms #-}
{-# Language MonoLocalBinds #-}
{-# Language TemplateHaskell #-}
{-# Language ImplicitParams #-}

-- |
-- Copyright :  (c) Edward Kmett 2020, András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Ergo.Elaborate.Value where

import Control.Lens hiding (Context)
import Control.Monad.Primitive
import Data.Hashable
import Data.HashSet
import Data.Primitive.MutVar
import Ergo.Elaborate.Monad
import Ergo.Icit
import Ergo.Names
import Ergo.Unique
import GHC.Exception
import GHC.Stack.Types

panic :: HasCallStack => a
panic = throw (errorCallWithCallStackException "impossible" ?callStack)

data Meta s = MetaRef {-# unpack #-} !(Unique s) {-# unpack #-} !(MutVar s (MetaEntry s))

instance Eq (Meta s) where
  MetaRef _ m == MetaRef _ n = m == n

instance Hashable (Meta s) where
  hash (MetaRef h _) = hash h
  hashWithSalt d (MetaRef h _) = hashWithSalt d h

newMeta :: MonadPrim s m => MetaEntry s -> m (Meta s)
newMeta m = MetaRef <$> newUnique <*> newMutVar m
{-# inline newMeta #-}

writeMeta :: MonadPrim s m => Meta s -> MetaEntry s -> m ()
writeMeta (MetaRef _ r) s = writeMutVar r s
{-# inline writeMeta #-}

readMeta :: MonadPrim s m => Meta s -> m (MetaEntry s)
readMeta (MetaRef _ r) = readMutVar r
{-# inline readMeta #-}

modifyMeta :: MonadPrim s m => Meta s -> (MetaEntry s -> MetaEntry s) -> m ()
modifyMeta (MetaRef _ r) f = modifyMutVar' r f
{-# inline modifyMeta #-}

type Metas s = HashSet (Meta s)
type Blocking s = Metas s
type BlockedBy s = Metas s

data MetaEntry s
  = Unsolved !(Metas s) (VTy s)
  | Solved !(Val s)
  | Constancy !(Context s) !(VTy s) !(VTy s) !(BlockedBy s)
  | Dropped

data SlotType = Def | Bound
  deriving (Eq,Ord,Show,Read,Bounded,Enum)

data Vals s
  = VNil
  | VSkip !(Vals s)
  | VDef !(Vals s) (Val s)

data Types s
  = TyNil
  | TySnoc !(Types s) !SlotType (VTy s)

data Context s 
  = Context
   { _vals :: Vals s
   , _types :: Types s
   , _names :: [Name]
   , _nameOrigin :: [NameOrigin]
   , _len :: Int
   }

data NameOrigin = NOSource | NOInserted
  deriving (Eq,Ord,Show,Read,Bounded,Enum)

type Lvl = Int

data Head s
  = HVar {-# unpack #-} !Lvl
  | HMeta {-# unpack #-} !(Meta s)
  deriving Eq

data Spine s
  = SNil
  | SApp !Icit !(Spine s) (Val s)
  | SAppTel (Val s) !(Spine s) (Val s)
  | SProj1 !(Spine s)
  | SProj2 !(Spine s)

type VTy = Val

data Val s
  = VNe !(Head s) !(Spine s)
  | VPi !Name !Icit (VTy s) (EVTy s)
  | VLam !Name !Icit (VTy s) (EVal s)
  | VU
  | VTel
  | VRec (Val s)
  | VTNil
  | VTCons !Name (Val s) (EVal s)
  | VTnil
  | VTcons (Val s) (Val s)
  | VPiTel !Name (Val s) (EVal s)
  | VLamTel !Name (Val s) (EVal s)

type EVal s = Val s -> M s (Val s)
type EVTy s = VTy s -> M s (VTy s)

pattern VVar :: Lvl -> Val s
pattern VVar x = VNe (HVar x) SNil

pattern VMeta :: Meta s -> Val s
pattern VMeta m = VNe (HMeta m) SNil

makeLenses ''Context
