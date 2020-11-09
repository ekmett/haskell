{-# language PolyKinds #-}
{-# language BlockArguments #-}
{-# language AllowAmbiguousTypes #-}
{-# language StrictData #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language TypeApplications #-}
{-# language BangPatterns #-}
{-# language NPlusKPatterns #-}
{-# language TypeFamilies #-}
{-# language RoleAnnotations #-}
{-# language ViewPatterns #-}
{-# language StandaloneKindSignatures #-}
{-# language OverloadedStrings #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language DataKinds #-}
{-# language GADTs #-}
{-# language TypeOperators #-}
{-# language PatternSynonyms #-}
{-# language TypeApplications #-}
{-# language TemplateHaskell #-}
{-# language LambdaCase #-}
{-# language ImportQualifiedPost #-}

-- idea:
-- levels are unindexed
-- but metas ARE marked with their depth in terms of max level
-- this means vals are unindexed, but metas are

module LF where

import Control.Category
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import Data.Bits
import Data.Coerce
import Data.Functor
import Data.Hashable
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.IORef
import Data.Type hiding (SNil, SCons)
import Data.Type.Unsafe
import Data.Type.Equality hiding (apply)
import Data.Kind
import Data.Maybe
import Data.Proxy
import Data.Text.Short (ShortText)
import Data.Text.Short qualified as Short
import Text.Show.Deriving
import Unsafe.Coerce
import Numeric.Natural
import System.IO.Unsafe
import Prelude hiding (id, (.))

data Icit = I | E
  deriving (Eq,Ord,Show,Read,Enum,Bounded)

makeSing ''Icit

--------------------------------------------------------------------------------
-- * De Bruijn Indices
--------------------------------------------------------------------------------

newtype Ix i = Ix Int
  deriving newtype Show

type Ix :: Int -> Type
data Ix' i where
  IZ' :: Ix' (S n)
  IS' :: Ix n -> Ix' (S n)

ix' :: Ix i -> Ix' i
ix' (Ix 0) = unsafeCoerce IZ'
ix' (Ix n) = unsafeCoerce (IS' (Ix (n-1)))

pattern IZ :: () => n ~ (S n') => Ix n
pattern IZ <- (ix' -> IZ') where
  IZ = Ix 0

pattern IS :: () => n ~ S n' => Ix n' -> Ix n
pattern IS n <- (ix' -> IS' n) where
  IS (Ix n) = Ix (n+1)

--------------------------------------------------------------------------------
-- * De Bruijn Levels
--------------------------------------------------------------------------------

type Lvl :: Type
newtype Lvl = Lvl Int
  deriving newtype (Eq,Ord,Show,Read,Num,Enum,Real,Integral,Hashable)

lvlIx :: forall i. Sing i => Lvl -> Ix i
lvlIx (Lvl l) = Ix (reflect @_ @i - l - 1)

ixLvl :: forall i. Sing i => Ix i -> Lvl
ixLvl (Ix l) = Lvl (reflect @_ @i - l - 1)

--------------------------------------------------------------------------------
-- * Environments
--------------------------------------------------------------------------------

type Tree :: Int -> Int -> Type -> Type
type role Tree nominal nominal representational
data Tree i j a where
  TTip :: ~a -> Tree (S j) j a
  TBin :: ~a -> Tree j k a -> Tree k l a -> Tree (S j) l a

instance Functor (Tree i j) where
  fmap f (TTip a) = TTip (f a)
  fmap f (TBin a l r) = TBin (f a) (fmap f l) (fmap f r)

instance Foldable (Tree i j) where
  foldMap f (TTip a) = f a
  foldMap f (TBin a l r) = f a <> foldMap f l <> foldMap f r

instance Traversable (Tree i j) where
  traverse f (TTip a) = TTip <$> f a
  traverse f (TBin a l r) = TBin <$> f a <*> traverse f l <*> traverse f r

type Vec :: Int -> Type -> Type
type role Vec nominal representational
data Vec n a where
  TCons :: Int -> Int -> Tree n m a -> Vec m a -> Vec n a
  Nil   :: Vec Z a

instance Functor (Vec n) where
  fmap _ Nil = Nil
  fmap f (TCons s n t xs) = TCons s n (fmap f t) (fmap f xs)

instance Foldable (Vec n) where
  foldMap _ Nil = mempty
  foldMap f (TCons s n t xs) = foldMap f t <> foldMap f xs
  null Nil = True
  null _ = False
  length Nil = 0
  length (TCons s _ _ _) = s

-- TODO: functor, foldable, traversable, applicative, monad

type Vec' :: Int -> Type -> Type
type role Vec' nominal representational
data Vec' n a where
  Nil'  :: Vec' Z i
  Cons' :: ~a -> Vec n a -> Vec' (S n) a

vcons :: a -> Vec n a -> Vec (S n) a
vcons a (TCons s n l (TCons _ m r xs))
  | n == m = TCons (s+1) (2*n+1) (TBin a l r) xs
vcons a xs = TCons (1 + length xs) 1 (TTip a) xs

upVec :: Vec n a -> Vec' n a
upVec Nil = Nil'
upVec (TCons _ _ (TTip a) xs)     = Cons' a xs
upVec (TCons s n (TBin a l r) xs) = Cons' a $ TCons (s-1) n' l $ TCons (s-1-n') n' r xs
  where n' = unsafeShiftR n 1

vlength :: Vec n a -> Sing n
vlength Nil = SING 0
vlength (TCons s _ _ _) = SING s

pattern (:*) :: () => n ~ S m => a -> Vec m a -> Vec n a
pattern v :* e <- (upVec -> Cons' v e) where
  v :* e = vcons v e

infixr 5 :*

{-# complete Nil, (:*) #-}

index :: Vec n a -> Ix n -> a
index = go where
  go :: Vec n a -> Ix n -> a
  go (TCons _ n t xs) !m@(Ix im)
    | n <= im = go xs (Ix (im-n))
    | otherwise = goTree n t m
  go Nil _ = panic

  goTree :: Int -> Tree i j a -> Ix i -> a
  goTree _ (TTip a) IZ = a
  goTree _ (TTip _) _ = panic
  goTree _ (TBin a _ _) IZ = a
  goTree n (TBin _ l r) m@(Ix im)
    | im <= n' = goTree n' l $ Ix (im - 1)
    | otherwise = goTree n' r $ Ix (im - n' - 1)
    where n' = unsafeShiftR n 1

-------------------------------------------------------------------------------
-- * Expressions
-------------------------------------------------------------------------------

type Name = ShortText

type Meta :: Type
newtype Meta = MetaRef { metaRef :: IORef MetaEntry } deriving Eq

data MetaEntry
  = Unsolved ~VTy
  | Solved ~Val

fromSolved :: MetaEntry -> Val
fromSolved (Solved v) = v
fromSolved _ = panic

instance Show Meta where
  showsPrec d MetaRef{} = showParen (d > 10) $ showString "Meta{}"

newMeta :: MonadIO m => VTy -> m Meta
newMeta d = liftIO $ MetaRef <$> newIORef (Unsolved d)
{-# inline newMeta #-}

readMeta :: MonadIO m => Meta -> m MetaEntry
readMeta m = liftIO $ readIORef (metaRef m)
{-# inline readMeta #-}

writeMeta :: MonadIO m => Meta -> Val -> m ()
writeMeta m v = liftIO $ writeIORef (metaRef m) (Solved v)
{-# inline writeMeta #-}

{-
-- find the root meta, and union by rank
findMeta :: MonadIO m => Meta j -> m (Weakened Meta j)
findMeta m0 = liftIO $ go m0 where
  go :: Meta j -> IO (Weakened Meta j)
  go m = readMeta m >>= \case
    Just (VMeta d m' SNil) -> do
      Weakened d' m'' <- go m'
      let d'' = d.d'
      Weakened d'' m'' <$ case testEquality m m' of
        Nothing -> writeMeta m' $ _ $ VMeta d'' m'' SNil
        _ -> pure ()
     -- Weakened d'' m'' <$ when (not $ geq m' m'') do
     --   writeMeta m' $ VMeta _ m'' SNil
    _ -> pure $ Weakened id m
-}

type Ty = Tm
data Tm i where
  Var  :: Ix i -> Tm i
--  Top  :: Name -> Tm i
  App  :: Icit -> Tm i -> Tm i -> Tm i
  Lam  :: Name -> Icit -> Ty i -> Tm (S i) -> Tm i
  Let  :: Name -> Ty i -> Tm i -> Tm (S i) -> Tm i
  Pi   :: Name -> Icit -> Ty i -> Ty (S i) -> Tm i
  U    :: Tm i
  Meta :: Meta -> Tm i
  Skip :: Tm (S i) -> Tm i

-------------------------------------------------------------------------------
-- * Semantic Domain
-------------------------------------------------------------------------------

type Val :: Type
data Val where
  VLam  :: Name -> Icit -> ~VTy -> EVal -> Val -- type is lazy
  VPi   :: Name -> Icit -> ~VTy -> EVTy -> Val -- type is lazy
  VVar  :: Lvl  -> Sp -> Val
--  VTop  :: Name -> Sp -> ~Val -> Val
  VMeta :: Meta -> Sp -> Val
  VU    :: Val

type VTy  = Val
type EVal = Val -> IO Val
type EVTy = EVal

lvlVar :: Sing i => Lvl -> Tm i
lvlVar h = Var (lvlIx h)

topLvl :: forall (i::Int). SingI i => Lvl
topLvl = Lvl (reflect @Int @i)

topVal :: forall (i::Int). SingI i => Val
topVal = VVar (topLvl @i) SNil

data Sp where
  SNil :: Sp
  SApp :: Icit -> Sp -> ~Val -> Sp

{-# complete SNil, SApp #-}

forceMetas :: Val -> IO Val
forceMetas = \case
  v@(VMeta m sp) -> readMeta m >>= \case
    Unsolved{} -> pure v
    Solved v' -> applySp v' sp >>= forceMetas
  v -> pure v

panic :: a
panic = error "panic"

type Str :: Int -> Int -> Type
data Str i j where
  Str :: (Sing i, Sing j) =>
    { strMap :: HashMap Lvl Lvl
    , strOcc :: Maybe Meta
    } -> Str i j

strDom :: Str i j -> Sing i
strDom Str{} = sing

strCod :: Str i j -> Sing j
strCod Str{} = sing

emptyStr :: Str Z Z
emptyStr = Str HM.empty Nothing

liftStr :: forall i j. Str i j -> Str (S i) (S j)
liftStr (Str r occ) = Str (HM.insert (topLvl @j) (topLvl @i) r) occ

skipStr :: Str i j -> Str i (S j)
skipStr (Str r occ) = Str r occ

lookupStr :: Lvl -> Str i j -> Maybe Lvl
lookupStr l (Str r _) = HM.lookup l r

strengthen :: forall i j. Str i j -> Val -> IO (Tm i)
strengthen str@Str{} = go where
  go :: Val -> IO (Tm i)
  go = forceMetas >=> \case
    VVar x sp -> case lookupStr x str of
      Just l -> goSp (lvlVar l) sp
      Nothing -> throwIO $ ScopeError x
    VMeta m sp
      | Just m' <- strOcc str, m == m' -> throwIO OccursCheck
      | otherwise -> do
      prune m sp
      forceMetas (VMeta m sp) >>= \case
        VMeta m' sp -> goSp (Meta m) sp
        _ -> panic
    VPi n i t b -> Pi n i <$> go t <*> goB b
    VLam n i t b -> Lam n i <$> go t <*> goB b
    VU -> pure U

  goB t = do
    v <- t (topVal @j)
    strengthen (liftStr str) v

  goSp :: Tm i -> Sp -> IO (Tm i)
  goSp h = \case
    SNil           -> pure h
    SApp i sp u    -> App i <$> goSp h sp <*> go u

  prune :: Meta -> Sp -> IO ()
  prune m sp0 = case mpruning [] sp0 of
    Nothing -> pure()
    Just pr -> unless (and pr) do
      metaTy <- fromSolved <$> readMeta m
      prunedTy <- pruneTy pr emptyStr metaTy
      panic
   where
    mpruning :: [Bool] -> Sp -> Maybe [Bool]
    mpruning acc SNil                    = pure acc
    mpruning acc (SApp i sp (VVar x SNil))
      = mpruning (isJust (HM.lookup x (strMap str)) : acc) sp
    mpruning _   _                       = Nothing

    pruneTy :: forall i j. [Bool] -> Str i j -> VTy -> IO (Ty i)
    pruneTy [] str' = strengthen str'
    pruneTy (True:pr') str'@Str{} = forceMetas >=> \case
      VPi n i t b -> do
        t' <- strengthen str' t
        v' <- b (topVal @j)
        Pi n i t' <$> pruneTy pr' (liftStr str') v'
      _ -> panic
    pruneTy (False:pr') str'@Str{} = forceMetas >=> \case
      VPi n i t b -> do
        v' <- b (topVal @j)
        pruneTy pr' (skipStr str') v' -- crap

data ScopeError = ScopeError Lvl deriving Show
instance Exception ScopeError

data OccursCheck = OccursCheck deriving Show
instance Exception OccursCheck

-------------------------------------------------------------------------------
-- * Utilities
-------------------------------------------------------------------------------

lazily :: IO a -> IO a
lazily = unsafeInterleaveIO

type Vals :: Int -> Type
type Vals i = Vec i Val

vskip :: Vals i -> Vals (S i)
vskip vs = VVar (Lvl $ length vs) SNil :* vs

-------------------------------------------------------------------------------
-- * Evaluation
-------------------------------------------------------------------------------

lazilyEval :: Vals i -> Tm i -> IO Val
lazilyEval e t = lazily (eval e t)

eval :: Vals i -> Tm i -> IO Val
eval e (Var n) = pure $ index e n
eval e (App i f x) = do
  fv <- eval e f
  xv <- lazilyEval e x
  apply i fv xv
eval e (Lam n i t b) = do
  tv <- lazilyEval e t
  pure $ VLam n i tv \v -> eval (v :* e) b
eval e (Let _ _ d b) = do
  v <- lazilyEval e d
  eval (v :* e) b
eval e (Pi n i t b) = do
  tv <- lazilyEval e t
  pure $ VPi n i tv \v -> eval (v :* e) b
eval _ U = pure VU
eval _ (Meta m) = forceMetas (VMeta m SNil)

apply :: Icit -> Val -> Val -> IO Val
apply _ (VLam _ _ _ f) v = f v
apply i (VVar h s)     v = pure $ VVar h (SApp i s v)
apply i (VMeta m s)    v = pure $ VMeta m (SApp i s v)
apply _ _              _ = panic

applySp :: Val -> Sp -> IO Val
applySp h SNil = pure h
applySp h (SApp i sp u) = do
  sp' <- applySp h sp
  apply i sp' u

quote :: forall n. Sing n => Val -> IO (Tm n)
quote (VLam n i t b) = do
  t' <- quote t
  Lam n i t' <$> do
    v' <- b (topVal @n)
    quote v'
quote (VPi n i t b) = do
  t' <- quote t
  Pi n i t' <$> do
    v' <- b (topVal @n)
    quote v'
quote (VVar h s) = quoteSp s (lvlVar h)
quote (VMeta m s) = readMeta m >>= \case
  Solved v   -> applySp v s >>= quote
  Unsolved{} -> quoteSp s $ Meta m
quote VU = pure U

quoteSp :: Sing i => Sp -> Tm i -> IO (Tm i)
quoteSp SNil e = pure e
quoteSp (SApp i s x) e = App i <$> quoteSp s e <*> quote x

nf :: Sing j => Vals i -> Tm i -> IO (Tm j)
nf e t = eval e t >>= quote

deriveShow ''Tm

-- "Zonk was named for the sound it makes" -- Simon Marlow
zonk :: Sing i => Vals i -> Tm i -> IO (Tm i)
zonk _ U = pure U
zonk e (Var n) = pure $ Var n
zonk e (Let n t d b) = Let n <$> zonk e t <*> zonk e d <*> zonk (vskip e) b
zonk e (Lam n i t b) = Lam n i <$> zonk e t <*> zonk (vskip e) b
zonk e (Pi n i t b) = Pi n i <$> zonk e t <*> zonk (vskip e) b
zonk e (App i t u) = zonkSp e t >>= \case
  Left v -> do
    uv <- lazilyEval e u
    r <- apply i v uv
    quote r
  Right t' -> App i t <$> zonk e u
zonk e t@(Meta m) = readMeta m >>= \case
  Solved v -> quote v
  Unsolved{} -> pure t

zonkSp :: Sing i => Vals i -> Tm i -> IO (Either Val (Tm i))
zonkSp e (App i t u) = zonkSp e t >>= \case
  Left v -> Left <$> do
    u' <- lazilyEval e u
    apply i v u'
  Right t' -> Right . App i t' <$> zonk e u
zonkSp e t@(Meta m) = readMeta m <&> \case
  Solved v -> Left v
  Unsolved _ -> Right t
zonkSp e t = Right <$> zonk e t

-------------------------------------------------------------------------------
-- * Tests
-------------------------------------------------------------------------------

ki :: IO Val
ki = do
  i <- lazilyEval Nil $ Lam "x" E U $ Var IZ
  k <- lazilyEval Nil $ Lam "x" E U $ Lam "y" E U $ Var (IS IZ)
  eval (i :* k :* Nil) $ App E (Var (IS IZ)) (Var IZ) where

main :: IO ()
main = do
  test <- ki
  test' <- quote @Z test
  print test'
