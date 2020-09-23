{-# language PatternSynonyms #-}
{-# language ExplicitNamespaces #-}
{-# language TemplateHaskell #-}
{-# language StandaloneKindSignatures #-}
{-# language FlexibleInstances #-}
{-# language DataKinds #-}
{-# language TypeApplications #-}
{-# language PolyKinds #-}
{-# language RoleAnnotations #-}
{-# language ViewPatterns #-}
{-# language GADTs #-}
{-# language MagicHash #-}
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
    type Sing
  , SingT(Sing, fromSing)
  , SingI(..)
  , makeSing
  , withSing
  -- * Reflection
  , reify
  , reflect
  -- * Singular types
  , Singular
  , me
  , Me
  -- makeMe
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
  , type Z
  , type S
  , pattern SZ
  , pattern SS, pattern SS'
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
  -- ** Dict p
  , type MkDict
  , pattern SDict
  -- ** p :- q
  , type MkImpl
  , pattern SImpl
  --, MkSubDict
  ) where

import Data.Type.Internal
import Data.Type.Internal.Instances
import Data.Type.Internal.TH
import GHC.Types (Constraint, Type, Nat, Symbol)
