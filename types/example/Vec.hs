{-# Language StandaloneKindSignatures #-}
{-# Language RoleAnnotations #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language PolyKinds #-}
{-# Language DataKinds #-}
{-# Language TypeOperators #-}
{-# Language GADTs #-}
{-# Language PatternSynonyms #-}
{-# Language ViewPatterns #-}
{-# Language TemplateHaskell #-}

import Data.Type
import GHC.Types
import GHC.TypeNats
import Data.Type.Equality
import Data.Type.Unsafe
import Data.Type.TH
import Unsafe.Coerce

type Vec :: Type -> Nat -> Type
type role Vec representational nominal
data Vec a n where
  VNil  :: Vec a Z
  VCons :: a -> Vec a n -> Vec a (S n)

makeSing ''Vec
-- generates

{-
type SVec' :: forall a n. Vec a n -> Type
type role SVec' nominal
data SVec' a where
  SVNil' :: SVec' 'VNil
  SVCons' :: Sing a -> Sing b -> SVec' ('VCons a b)

upSVec :: Sing a -> SVec' a
upSVec (Sing VNil) = unsafeCoerce SVNil'
upSVec (Sing (VCons a as)) = unsafeCoerce (SVCons' (UnsafeSing a) (UnsafeSing as))

pattern SVNil :: () => r ~ 'VNil => Sing r
pattern SVNil <- (upSVec -> SVNil') where
  SVNil = UnsafeSing VNil

-- works with an injective Succ
pattern SVCons :: () => r ~ 'VCons x xs => Sing x -> Sing xs -> Sing r
pattern SVCons y ys <- (upSVec -> SVCons' y ys) where
  SVCons (Sing y) (Sing ys) = UnsafeSing (VCons y ys)
-}
