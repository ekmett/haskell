{-# Language LambdaCase #-}
{-# Language BlockArguments #-}
{-# Language ImportQualifiedPost #-}
{-# Language ViewPatterns #-}
{-# Language TemplateHaskell #-}
{-# Language BangPatterns #-}
{-# Language DeriveAnyClass #-}
{-# Language DerivingVia #-}
{-# Language GADTs #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
module Elaborate.Unification where

import Control.Exception
import Control.Lens hiding (Context)
import Control.Monad.Catch as M
import Data.Foldable (forM_)
import Data.HashSet qualified as HS
import Data.HashMap.Strict qualified as HM
import Data.Maybe (isJust)
import Elaborate.Evaluation
import Elaborate.Term
import Elaborate.Value
import Elaborate.Monad
import Elaborate.Occurrence
import Icit
import Names

type TM s = Tm (Meta s)
type TY s = Ty (Meta s)

lvlName :: [Name] -> Lvl -> Name
lvlName ns x = ns !! (length ns - x - 1)

type Renaming = HM.HashMap Lvl Lvl

data SpineError
  = SpineNonVar
  | SpineProjection
  | NonLinearSpine Lvl
  deriving (Show, Exception)

data StrengtheningError
  = ScopeError Lvl
  | OccursCheck
  deriving (Show, Exception)

data UnifyError
  = forall s. UnifyError [Name] (TM s) (TM s)
  | forall s. SpineError [Name] (TM s) (TM s) SpineError
  | forall s. StrengtheningError [Name] (TM s) (TM s) StrengtheningError
  deriving Exception

instance Show UnifyError where
  show _ = "_ {- UnifyError -}"

-- | Add a bound variable.
bind :: Name -> NameOrigin -> VTy s -> Context s -> Context s
bind x o a (Context vs tys ns no d) = Context (VSkip vs) (TySnoc tys Bound a) (x:ns) (o:no) (d + 1)

bindSrc :: Name -> VTy s -> Context s -> Context s
bindSrc x = bind x NOSource

-- | Lift ("skolemize") a value in an extended context to a function in a
--   non-extended context.
liftVal :: Context s -> Val s -> EVal s
liftVal cxt t = \ ~x -> do
  tm <- uneval (cxt^.len+1) t
  eval (VDef (cxt^.vals) x) tm


-- | Explicit strengthening. We use this for pruning and checking meta solution
--   candidates.
data Str s = Str {
  _dom :: {-# UNPACK #-} !Lvl, -- ^ size of renaming domain
  _cod :: {-# UNPACK #-} !Lvl, -- ^ size of renaming codomain
  _ren :: !Renaming,           -- ^ partial renaming
  _occ :: Maybe (Meta s)       -- ^ meta for occurs checking
  }

makeLenses ''Str

-- | Strengthens a value, returns a quoted normal result. This performs scope
--   checking, meta occurs checking and (recursive) pruning at the same time.
--   May throw `StrengtheningError`.
strengthen :: forall s. Str s -> Val s -> M s (TM s)
strengthen str0 = go where

  -- we only prune all-variable spines with illegal var occurrences,
  -- we don't prune illegal cyclic meta occurrences.
  prune :: Meta s -> Spine s -> M s ()
  prune m sp0 = do

    let prune' :: [Bool] -> Spine s -> M s (Maybe [Bool])
        prune' acc SNil                    = pure (Just acc)
        prune' acc (SApp _ sp (VVar x))    = prune' (isJust (HM.lookup x (str0^.ren)) : acc) sp
        prune' acc (SAppTel _ sp (VVar x)) = prune' (isJust (HM.lookup x (str0^.ren)) : acc) sp
        prune' _   _                       = pure Nothing

    prune' [] sp0 >>= \case
      Nothing -> pure ()  -- spine is not a var substitution
      Just pruning 
        | and pruning -> pure ()  -- no pruneable vars
        | otherwise -> do

        metaTy <- readMeta m >>= \case
          Unsolved _ a -> pure a
          _ -> panic

        -- note: this can cause recursive pruning of metas in types
        prunedTy <- do
          let go' :: [Bool] -> Str s -> VTy s -> M s (TY s)

              go' [] str z = strengthen str z

              go' (True:pr) str z = force z >>= \case
                VPi x i a b -> do
                  r <- b $ VVar (str^.cod)
                  Pi x i <$> strengthen str a <*> go' pr (liftStr str) r
                VPiTel x a b ->do
                  r <- b $ VVar (str^.cod)
                  PiTel x <$> strengthen str a <*> go' pr (liftStr str) r
                _ -> panic

              go' (False:pr) str z = force z >>= \case
                VPi _ _ _ b -> do
                  r <- b $ VVar (str^.cod)
                  go' pr (skipStr str) r
                VPiTel _ _ b -> do
                  r <- b $ VVar (str^.cod)
                  go' pr (skipStr str) r
                _ -> panic

          go' pruning (Str 0 0 mempty Nothing) metaTy

        pty <- eval VNil prunedTy
        m' <- newMeta $ Unsolved mempty pty

        let argNum = length pruning
            body = go' pruning metaTy (Meta m') 0 where
              go' [] _ acc _ = pure acc
              go' (True:pr) z acc d = do
                force z >>= \case 
                  VPi _ i _ b -> do
                    a' <- b (VVar d)
                    go' pr a' (App i acc (Var (argNum - d - 1))) (d + 1)
                  VPiTel _ a b -> do
                    a' <- b (VVar d)
                    u <- uneval argNum a
                    go' pr a' (AppTel u acc (Var (argNum - d - 1))) (d + 1)
                  _ -> panic 
              go' (False:pr) z acc d = do
                force z >>= \case
                  VPi _ _ _ b -> do
                    a' <- b (VVar d)
                    go' pr a' acc (d + 1)
                  VPiTel _ _ b -> do
                    a' <- b (VVar d)
                    go' pr a' acc (d + 1)
                  _ -> panic

        b <- body
        rhs <- closingTm metaTy argNum [] b
        erhs <- eval VNil rhs 
        writeMeta m $ Solved erhs

  go :: Val s -> M s (TM s)
  go t = force t >>= \case
    VNe (HVar x) sp  -> case HM.lookup x (str0^.ren) of
                          Nothing -> throwM $ ScopeError x
                          Just x' -> forceSp sp >>= goSp (Var (str0^.dom - x' - 1))
    VNe (HMeta m0) sp -> if Just m0 == str0^.occ then
                          throwM OccursCheck
                        else do
                          prune m0 sp
                          force (VNe (HMeta m0) sp) >>= \case
                            VNe (HMeta m') sp' -> goSp (Meta m') sp'
                            _                -> panic

    VPi x i a b      -> Pi x i <$> go a <*> goBind b
    VLam x i a t'     -> Lam x i <$> go a <*> goBind t'
    VU               -> pure U
    VTel             -> pure Tel
    VRec a           -> Rec <$> go a
    VTNil            -> pure TNil
    VTCons x a b     -> TCons x <$> go a <*> goBind b
    VTnil            -> pure Tnil
    VTcons t' u      -> Tcons <$> go t' <*> go u
    VPiTel x a b     -> PiTel x <$> go a <*> goBind b
    VLamTel x a t'   -> LamTel x <$> go a <*> goBind t'

  goBind :: EVal s -> M s (TM s)
  goBind t = t (VVar (str0^.cod)) >>= strengthen (liftStr str0) 

  goSp h = \case
    SNil           -> pure h
    SApp i sp u    -> App i <$> goSp h sp <*> go u
    SAppTel a sp u -> AppTel <$> go a <*> goSp h sp <*> go u
    SProj1 sp      -> Proj1 <$> goSp h sp
    SProj2 sp      -> Proj2 <$> goSp h sp


-- | Lift a `Str` over a bound variable.
liftStr :: Str s -> Str s
liftStr (Str c d r o) = Str (c + 1) (d + 1) (HM.insert d c r) o

-- | Skip a bound variable.
skipStr :: Str s -> Str s
skipStr (Str c d r o) = Str c (d + 1) r o


closingTy :: Context s -> Ty (Meta s) -> M s (Ty (Meta s))
closingTy cxt = go (cxt^.types) (cxt^.names) (cxt^.len) where
  go TyNil [] _ b = pure b
  go (TySnoc tys Def _) (_:ns) d b = go tys ns (d-1) (Skip b)
  go (TySnoc tys Bound (VRec a)) (x:ns) d b = do
    a' <- uneval (d-1) a
    go tys ns (d-1) (PiTel x a' b)
  go (TySnoc tys Bound a) (x:ns) d b = do
    a' <- uneval (d-1) a
    go tys ns (d-1) (Pi x Explicit a' b)
  go _ _ _ _ = panic

-- | Close a term by wrapping it in `Int` number of lambdas, while taking the domain
--   types from the `VTy`, and the binder names from a list. If we run out of provided
--   binder names, we pick the names from the Pi domains.
closingTm :: VTy s -> Int -> [Name] -> TM s -> M s (TM s)
closingTm = go 0 where
  getName []     x = x
  getName (x:_)  _ = x

  go !_ !_ 0 !_ rhs = pure rhs
  go d a l xs rhs = force a >>= \case
    VPi (getName xs -> x) i _ b  -> do
      a' <- b (VVar d) 
      bd <- uneval d a 
      Lam x i bd <$> go (d + 1) a' (l-1) (drop 1 xs) rhs
    VPiTel (getName xs -> x) _ b -> do
      a' <- b (VVar d)
      bd <- uneval d a
      LamTel x bd <$> go (d + 1) a' (l-1) (drop 1 xs) rhs
    _ -> panic


newConstancy :: Context s -> VTy s -> EVal s -> M s ()
newConstancy cxt d c = do
  v <- c (VVar (cxt^.len))
  m <- newMeta $ Constancy cxt d v mempty
  tryConstancy m

tryConstancy :: Meta s -> M s ()
tryConstancy constM = readMeta constM >>= \case
  Constancy cxt d c blockers -> do

    -- clear blockers
    forM_ blockers \m ->
      modifyMeta m \case
        Unsolved ms a -> Unsolved (HS.delete constM ms) a
        Solved t -> Solved t
        _ -> panic

    let dropConstancy = writeMeta constM Dropped

    let n = cxt^.len

    occurs (n + 1) n c >>= \case
      None    -> unify cxt d VTNil >> dropConstancy
      Rigid   -> dropConstancy
      Flex ms -> do
        -- set new blockers
        forM_ ms \m ->
          modifyMeta m $ \case
            Unsolved ms' a -> Unsolved (HS.insert constM ms') a
            _ -> panic

        writeMeta constM $ Constancy cxt d c ms

  _ -> panic

data SP s = SP (Spine s) {-# UNPACK #-} !Lvl

freshMeta :: Context s -> VTy s -> M s (TM s)
freshMeta cxt v = do
  a <- uneval (cxt^.len) v
  metaTy <- closingTy cxt a
  t <- eval VNil metaTy
  m <- newMeta $ Unsolved mempty t

  let vars :: Types s -> SP s
      vars TyNil                                      = SP SNil 0
      vars (TySnoc (vars -> SP sp d) Def _)           = SP sp (d + 1)
      vars (TySnoc (vars -> SP sp d) Bound (VRec a')) = SP (SAppTel a' sp (VVar d)) (d + 1)
      vars (TySnoc (vars -> SP sp d) Bound _)         = SP (SApp Explicit sp (VVar d)) (d + 1)

  case vars (cxt^.types) of
    SP sp _ -> uneval (cxt^.len) $ VNe (HMeta m) sp

-- | Wrap the inner `UnifyError` arising from unification in an `UnifyErrorWhile`.
--   This decorates an error with one additional piece of context.
unifyWhile :: Context s -> Val s -> Val s -> M s ()
unifyWhile = undefined
{-
unifyWhile cxt l r =
  unify cxt l r
  `catch`
  (report (cxt^.names) . UnifyErrorWhile (quote (cxt^.len) l) (quote (cxt^.len) r))
-}

checkSp :: Spine s -> M s (Renaming, Lvl, [Lvl])
checkSp s0 = do
  s1 <- forceSp s0
  go s1 <&> over _3 reverse

  where
  go :: Spine s -> M s (Renaming, Lvl, [Lvl])
  go = \case
    SNil        -> pure (mempty, 0, [])
    SApp _ sp u -> do
      (!r, !d, !xs) <- go sp
      force u >>= \case
        VVar x | HM.member x r -> throwM $ NonLinearSpine x
               | otherwise     -> pure (HM.insert x d r, d + 1, x:xs)
        _      -> throwM SpineNonVar
    SAppTel _ sp u -> do
      (!r, !d, !xs) <- go sp
      force u >>= \case
        VVar x | HM.member x r -> throwM $ NonLinearSpine x
               | otherwise     -> pure (HM.insert x d r, d + 1, x:xs)
        _    -> throwM SpineNonVar
    SProj1 _ -> throwM SpineProjection
    SProj2 _ -> throwM SpineProjection

-- | May throw `UnifyError`.
solveMeta :: Context s -> Meta s -> Spine s -> Val s -> M s ()
solveMeta cxt m sp rhs = do

  -- these normal forms are only used in error reporting
  let topLhs = uneval (cxt^.len) (VNe (HMeta m) sp)
      topRhs = uneval (cxt^.len) rhs

  -- check spine
  (r, spLen, spVars) <- checkSp sp
         `M.catch` \e -> do
            tlhs <- topLhs 
            trhs <- topRhs
            throwM $ SpineError (cxt^.names) tlhs trhs e

  --  strengthen right hand side
  srhs <- strengthen (Str spLen (cxt^.len) r (Just m)) rhs
         `M.catch` \e -> do
            tlhs <- topLhs 
            trhs <- topRhs
            throwM $ StrengtheningError (cxt^.names) tlhs trhs e

  (blocked, metaTy) <- readMeta m >>= \case
    Unsolved blocked a -> pure (blocked, a)
    _ -> panic

  let spVarNames = map (lvlName (cxt^.names)) spVars
  closedRhs <- closingTm metaTy spLen spVarNames srhs
  erhs <- eval VNil closedRhs 
  writeMeta m $ Solved erhs

  -- try solving unblocked constraints
  forM_ blocked tryConstancy

-- | May throw `UnifyError`.
unify :: forall s. Context s -> Val s -> Val s -> M s ()
--unify = undefined
unify cxt l r = go l r where

  unifyError = undefined

   -- throwIO $ UnifyError (cxt^.names) (quote (cxt^.len) l) (quote (cxt^.len) r)

  -- if both sides are meta-headed, we simply try to check both spines
  flexFlex m sp m' sp' = do
    M.try @(M s) @SpineError (checkSp sp) >>= \case
      Left{}  -> solveMeta cxt m' sp' (VNe (HMeta m) sp)
      Right{} -> solveMeta cxt m sp (VNe (HMeta m') sp')

  implArity :: Context s -> EVal s -> M s Int
  implArity cxt' b = b (VVar (cxt'^.len)) >>= go' 0 (cxt'^.len + 1) where
        go' :: Int -> Int -> Val s -> M s Int
        go' !acc ln a = force a >>= \case
          VPi _ Implicit _ b' -> b' (VVar ln) >>= go' (acc + 1) (ln + 1)
          _ -> pure acc

  go t0 t0' = ((,) <$> force t0 <*> force t0') >>= \case
    (VLam x _ a t, VLam _ _ _ t')            -> goBind x a t t'
    (VLam x i a t, t')                       -> goBind x a t \ v -> evalApp i t' v
    (t, VLam x' i' a' t')                    -> goBind x' a' (\ v -> evalApp i' t v) t'
    (VPi x i a b, VPi _ i' a' b') | i == i'  -> go a a' >> goBind x a b b'
    (VU, VU)                                 -> pure ()
    (VTel, VTel)                             -> pure ()
    (VRec a, VRec a')                        -> go a a'
    (VTNil, VTNil)                           -> pure ()
    (VTCons x a b, VTCons _ a' b')           -> go a a' >> goBind x a b b'
    (VTnil, VTnil)                           -> pure ()
    (VTcons t u, VTcons t' u')               -> go t t' >> go u u'
    (VPiTel x a b, VPiTel _ a' b')           -> go a a' >> goBind x (VRec a) b b'
    (VLamTel x a t, VLamTel _  _ t')         -> goBind x (VRec a) t t'
    (VLamTel x a t, t')                      -> goBind x (VRec a) t (evalAppTel a t')
    (t, VLamTel x' a' t')                    -> goBind x' (VRec a') (evalAppTel a' t) t'
    (VNe h sp, VNe h' sp') | h == h'         -> do
      fsp <- forceSp sp 
      fsp' <- forceSp sp'
      goSp fsp fsp'
    (VNe (HMeta m) sp, VNe (HMeta m') sp')   -> flexFlex m sp m' sp'
    (VNe (HMeta m) sp, t')                   -> solveMeta cxt m sp t'
    (t, VNe (HMeta m') sp')                  -> solveMeta cxt m' sp' t

    (VPiTel x a b, t@(VPi x' Implicit a' b')) -> do
      ia <- implArity cxt b
      ib <- implArity cxt b'
      if ia <= ib then do
        let cxt' = bindSrc x' a' cxt
        m <- freshMeta cxt' VTel
        vm <- eval (cxt'^.vals) m -- interleave?
        go a $ VTCons x' a' $ liftVal cxt vm
        let b2 ~x1 ~x2 = b (VTcons x1 x2)
        newConstancy cxt' vm $ b2 $ VVar (cxt^.len)
        goBind x' a' 
          (\ ~x1 -> liftVal cxt vm x1 <&> \t' -> VPiTel x t' (b2 x1)) b'
      else do
        go a VTNil
        r' <- b VTnil
        go r' t

    (t@(VPi x' Implicit a' b'), VPiTel x a b) -> do
      ia <- implArity cxt b
      ib <- implArity cxt b'
      if ia <= ib then do
        let cxt' = bindSrc x' a' cxt
        m <- freshMeta cxt' VTel
        vm <- eval (cxt'^.vals) m -- interleave?
        go a $ VTCons x' a' $ liftVal cxt vm
        let b2 ~x1 ~x2 = b (VTcons x1 x2)
        newConstancy cxt' vm $ b2 $ VVar (cxt^.len)
        goBind x' a' b' \ ~x1 -> liftVal cxt vm x1 <&> \t' -> VPiTel x t' (b2 x1)
      else do
        go a VTNil
        r' <- b VTnil
        go t r'
    (VPiTel _ a b, t) -> do
      go a VTNil
      r' <- b VTnil
      go r' t
    (t, VPiTel _ a b) -> do
      go a VTNil
      r' <- b VTnil
      go t r'
    _ -> unifyError

  goBind x a t t' = do
    let v = VVar (cxt^.len)
    u <- t v
    u' <- t' v
    unify (bindSrc x a cxt) u u'

  goSp sp0 sp0' = case (sp0, sp0') of
    (SNil, SNil) -> pure ()
    (SApp i sp u, SApp i' sp' u') | i == i' -> goSp sp sp' >> go u u'
    (SAppTel _ sp u, SAppTel _ sp' u')      -> goSp sp sp' >> go u u'
    _ -> panic


