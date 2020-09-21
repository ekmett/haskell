{-# language PatternSynonyms #-}
{-# language ExplicitNamespaces #-}
{-# language TemplateHaskell #-}
{-# language StandaloneKindSignatures #-}
{-# language FlexibleInstances #-}
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
  , makeSing
  -- * Reifying terms and constraints into singletons
  , SingI(..)
  , ify , reify
  -- * Lowering kinds to types
  , reflect
  , Singular
  , me
  , Me
  -- ** 'Type'
  , type Type
  , pattern Type
  , pattern SType
  -- ** 'Constraint'
  , type Constraint
  , pattern Constraint
  , pattern SConstraint
  -- ** 'Nat'
  , Nat
  , toNat, fromNat
  , pattern Nat
  -- ** 'Symbol'
  , Symbol
  , pattern Symbol
  , toSymbol
  , fromSymbol
  -- * Lifting numerics
  , Nice(..)
  , pattern Z
  , pattern S
  , type S
  , type Z
  , pattern SS
  , pattern SZ
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
  , pattern SUnit
  , pattern STuple2 -- (,)
  , pattern STuple3 -- (,,)
  , pattern STuple4 -- (,,,)
  , pattern STuple5 -- (,,,,)
  , pattern STuple6 -- (,,,,,)
  , pattern STuple7 -- (,,,,,,)
  , pattern STuple8 -- (,,,,,,,)
  , pattern STuple9 -- (,,,,,,,,)
  -- ** 'Either'
  , pattern SLeft, pattern SRight -- Either
  -- ** 'Maybe'
  , pattern SJust, pattern SNothing -- Maybe
  -- ** 'List'
  , pattern SNil, pattern (:#) -- List
  -- ** 'NonEmpty'
  , pattern (:|#) -- NonEmpty
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
  -- ** 'Proxy'
  , pattern SProxy
  -- ** '(:~:)'
  , pattern SRefl
  -- ** '(:~~:)'
  , pattern SHRefl
  ) where

import Data.Type.Internal
import Data.Type.Internal.Instances
import Data.Type.Internal.TH
import GHC.Types (Constraint, Type, Nat, Symbol)
