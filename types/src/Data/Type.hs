{-# language PatternSynonyms #-}
{-# language ExplicitNamespaces #-}
{-# language TemplateHaskell #-}
{-# language StandaloneKindSignatures #-}
{-# language DataKinds #-}
{-# language PolyKinds #-}
{-# language RoleAnnotations #-}
{-# language ViewPatterns #-}
{-# language GADTs #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- |
-- Copyright :  (c) Edward Kmett 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Data.Type
  ( 
  -- * Singleton types and reflection from singletons
    Sing
    ( Sing
    , fromSing
    )
  -- * Reifying terms and constraints into singletons
  , SingI(..)
  , Reifies, ify , reify
  -- * Lowering kinds to types
  , reflect
  -- ** 'Type'
  , type Type
  , pattern Type
  , pattern SType
  -- ** 'Nat'
  , Nat
  , toNat, fromNat
  , pattern Nat
  , pattern Z
  , pattern S
  , type Z
  , type S
  , pattern SS
  , pattern SZ
  -- ** 'Symbol'
  , Symbol
  , pattern Symbol
  , toSymbol
  , fromSymbol
  -- * Lifting types to kinds
  -- ** 'Int'
  , MkInt
  , pattern SIntS, pattern SIntZ, pattern SMkInt -- Int
  -- ** 'Char'
  , MkChar
  -- ** @'Ptr' a@
  , MkPtr
  , pattern SMkPtr
  -- ** @'StablePtr' a@
  , MkStablePtr
  , pattern SMkStablePtr
  -- * Singletons
  -- ** '(,)'
  , pattern SPair -- (,)
  -- ** 'Either'
  , pattern SLeft, pattern SRight -- Either
  -- ** 'Maybe'
  , pattern SJust, pattern SNothing -- Maybe
  -- ** 'List'
  , pattern SNil, pattern SCons -- List
  -- ** 'Bool'
  , pattern STrue, pattern SFalse -- Bool
  -- ** 'Ordering'
  , pattern SLT, pattern SEQ, pattern SGT -- Ordering
  -- ** 'Const'
  , pattern SConst
  -- ** 'Identity'
  , pattern SIdentity
  -- ** 'Compose'
  , pattern SCompose
  ) where

import Control.Applicative
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Type.Internal
import Data.Type.Internal.TH
import Data.Kind (Type)
import GHC.TypeLits (Nat, Symbol)

makeSing ''Either
makeSing ''Maybe
makeSing ''Bool
makeSing ''Ordering
makeSing ''Const
makeSing ''Compose
makeSing ''Identity
