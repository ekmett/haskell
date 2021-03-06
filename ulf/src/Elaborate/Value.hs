{-# Language CPP #-}
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

module Elaborate.Value where

import Common.Icit
import Common.Names
import Common.Unique
import Control.Lens hiding (Context)
import Data.Hashable
import Data.HashSet
import Data.IORef
import GHC.Exception
import GHC.Stack.Types

panic :: HasCallStack => a
panic = throw (errorCallWithCallStackException "impossible" ?callStack)

data Meta = MetaRef {-# unpack #-} !Unique {-# unpack #-} !(IORef MetaEntry)

instance Eq Meta where
  MetaRef _ m == MetaRef _ n = m == n

instance Hashable Meta where
  hash (MetaRef h _) = hash h
  hashWithSalt d (MetaRef h _) = hashWithSalt d h

newMeta :: MetaEntry -> IO Meta
newMeta m = MetaRef <$> newUnique <*> newIORef m
{-# inline newMeta #-}

writeMeta :: Meta -> MetaEntry -> IO ()
writeMeta (MetaRef _ r) s = writeIORef r s
{-# inline writeMeta #-}

readMeta :: Meta -> IO MetaEntry
readMeta (MetaRef _ r) = readIORef r
{-# inline readMeta #-}

modifyMeta :: Meta -> (MetaEntry -> MetaEntry) -> IO ()
modifyMeta (MetaRef _ r) f = modifyIORef' r f
{-# inline modifyMeta #-}

type Metas = HashSet Meta
type Blocking = Metas
type BlockedBy = Metas

data MetaEntry
  = Unsolved !Metas VTy
  | Solved !Val
#ifdef FCIF
  | Constancy !Context !VTy !VTy !BlockedBy
  | Dropped
#endif

data SlotType = Def | Bound
  deriving (Eq,Ord,Show,Read,Bounded,Enum)

data Vals
  = VNil
  | VSkip !Vals
  | VDef !Vals Val

data Types
  = TyNil
  | TySnoc !Types !SlotType VTy

data Context
  = Context
   { _vals :: Vals
   , _types :: Types
   , _names :: [Name]
   , _nameOrigin :: [NameOrigin]
   , _len :: Int
   }

data NameOrigin = NOSource | NOInserted
  deriving (Eq,Ord,Show,Read,Bounded,Enum)

type Lvl = Int

data Head
  = HVar {-# unpack #-} !Lvl
  | HMeta {-# unpack #-} !Meta
  deriving Eq

data Spine
  = SNil
  | SApp !Icit !Spine Val
#ifdef FCIF
  | SAppTel Val !Spine Val
  | SCar !Spine
  | SCdr !Spine
#endif

type VTy = Val

data Val
  = VNe !Head !Spine
  | VPi !Name !Icit VTy EVTy
  | VLam !Name !Icit VTy EVal
  | VU
#ifdef FCIF
  | VTel
  | VRec Val
  | VTNil
  | VTCons !Name Val EVal
  | VTnil
  | VTcons Val Val
  | VPiTel !Name Val EVal
  | VLamTel !Name Val EVal
#endif

type EVal = Val -> IO Val
type EVTy = VTy -> IO VTy

pattern VVar :: Lvl -> Val
pattern VVar x = VNe (HVar x) SNil

pattern VMeta :: Meta -> Val
pattern VMeta m = VNe (HMeta m) SNil

makeLenses ''Context
