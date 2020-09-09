{-# Language ScopedTypeVariables #-}
{-# Language PatternSynonyms #-}
{-# Language DerivingStrategies #-}
{-# Language DataKinds #-}
{-# Language TypeOperators #-}
{-# Language StandaloneKindSignatures #-}
{-# Language ViewPatterns #-}
{-# Language RoleAnnotations #-}
{-# Language GADTs #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language RankNTypes #-}

module Common.Internal.Nat
  ( Index(..)
  , type Z
  , type S
  , wk
  , N(UnsafeN,NZ,NS)
  , ViewN(..)
  , Fin(UnsafeFin,Z,S)
  ) where

import Data.Kind
import Data.Type.Equality
import GHC.TypeNats
import Unsafe.Coerce

class Index t where
  index :: t -> Int

instance Index Int where
  index = id

type Z = 0    
type S n = 1 + n    
    
wk :: forall i r proxy. proxy i -> (i <= S i => r) -> r    
wk _ r = case unsafeCoerce Refl of    
  (Refl :: (i <=? S i) :~: 'True) -> r    
    
type N :: Nat -> Type    
type role N nominal    
newtype N i = UnsafeN Int    
  deriving newtype (Index, Show)    
    
type ViewN :: Nat -> Type    
type role ViewN nominal    
data ViewN n where    
  ViewNZ :: ViewN Z    
  ViewNS :: N n -> ViewN (S n)    
    
viewNat :: N n -> ViewN n    
viewNat (UnsafeN 0) = unsafeCoerce ViewNZ    
viewNat (UnsafeN n) = unsafeCoerce (ViewNS $ UnsafeN (n-1))    
    
pattern NZ :: () => (n ~ Z) => N n    
pattern NZ <- (viewNat -> ViewNZ) where    
  NZ = UnsafeN 0    
    
pattern NS :: () => (n ~ S n') => N n' -> N n    
pattern NS n <- (viewNat -> ViewNS n) where    
  NS n = UnsafeN (index n + 1)    

{-# complete NZ, NS #-}
    
-------------------------------------------------------------------------------    
-- * Fin n    
-------------------------------------------------------------------------------    
    
type ViewFin :: Nat -> Type    
type role ViewFin nominal
data ViewFin j where
  ViewZ :: ViewFin (S j)
  ViewS :: Fin j -> ViewFin (S j)

type Fin :: Nat -> Type
type role Fin nominal
newtype Fin j = UnsafeFin Int
instance Index (Fin j) where index (UnsafeFin n) = n

instance Show (Fin j) where
  showsPrec d = showsPrec d . index

viewFin :: Fin i -> ViewFin i
viewFin (UnsafeFin 0) = unsafeCoerce ViewZ
viewFin (UnsafeFin n) = unsafeCoerce (ViewS $ UnsafeFin (n-1))

pattern Z :: Fin (S j)
pattern Z <- (viewFin -> ViewZ) where
  Z = UnsafeFin 0

pattern S :: () => (j ~ S i) => Fin i -> Fin j
pattern S n <- (viewFin -> ViewS n) where
  S n = UnsafeFin (index n + 1)

{-# complete Z, S #-}
