{-# Language LambdaCase #-}
{-# Language TemplateHaskellQuotes #-}
{-# Language RecordWildCards #-}
{-# Language ViewPatterns #-}
{-# Language BlockArguments #-}
{-# Language ParallelListComp #-}
{-# Language ImportQualifiedPost #-}
{-# Language Unsafe #-}
-- {-# OPTIONS_GHC -Wno-unused-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_HADDOCK not-home #-}

-- |
-- Copyright :  (c) Edward Kmett 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Data.Type.Internal.TH
  ( SingRules(..)
  , makeSing
  , makeSingWith
  , defaultSingRules
  ) where

import Control.Monad (unless)
import Data.Functor ((<&>))
import Data.List (intercalate)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Type.Internal
import Data.Traversable (for)
import Language.Haskell.TH as TH
import Unsafe.Coerce

data SingRules = SingRules
  { singTyCon    :: Name -> Name
  , singDataCon  :: Name -> Name
  , singDataCon' :: Name -> Name
  , singUp       :: Name -> Name
  }

defaultSingRules :: SingRules
defaultSingRules = SingRules{..} where
  singTyCon    =  mkName . (++"'") . ('S':) . nameBase
  singDataCon  =  mkName  . ('S':) . nameBase
  singDataCon' =  mkName . (++"'") . ('S':) . nameBase
  singUp       =  mkName . ("upS"++) . nameBase

makeSingWith :: SingRules -> Name -> Q [Dec]
makeSingWith opts n = TH.reify n >>= \case
  TyConI d -> case d of
    DataD    [] name tyvars mkind cons _ -> makeSing' opts name tyvars mkind cons
    NewtypeD [] name tyvars mkind con _ -> makeSing' opts name tyvars mkind [con]
    _ -> fail "makeSing: can only handle data and newtype declarations"
  d -> fail $ "makeSing: unsupported type\n\n" ++ pprint d

makeSing :: Name -> Q [Dec]
makeSing = makeSingWith defaultSingRules

csingi :: Q Type
csingi = conT ''SingI

csing :: Q Type
csing = conT ''Sing

tyVarBndrName :: TyVarBndr -> Name
tyVarBndrName (PlainTV n) = n
tyVarBndrName (KindedTV n _) = n

arrT :: Q Type -> Q Type -> Q Type
arrT x y = arrowT `appT` x `appT` y

_3 :: Functor f => (a -> f b) -> (x,y,a) -> f (x,y,b)
_3 f (x,y,a) = (,,) x y <$> f a

fvs :: Type -> Set Name
fvs (AppT l r) = fvs l <> fvs r
fvs (AppKindT l r) = fvs l <> fvs r
fvs (SigT l r) = fvs l <> fvs r
fvs (VarT n) = Set.singleton n
fvs (InfixT l n r) = fvs l <> Set.singleton n <> fvs r
fvs (UInfixT l n r) = fvs l <> Set.singleton n <> fvs r
fvs ArrowT = mempty
fvs StarT = mempty
fvs EqualityT = mempty
fvs UnboxedSumT{} = mempty
fvs UnboxedTupleT{} = mempty
fvs TupleT{} = mempty
fvs (ParensT t) = fvs t
fvs ListT = mempty
fvs ConstraintT = mempty
fvs (PromotedTupleT _) = mempty
fvs PromotedNilT = mempty
fvs PromotedConsT = mempty
fvs LitT{} = mempty
fvs WildCardT = mempty
fvs (ImplicitParamT _ r) = fvs r
fvs (ForallT bndrs c t) = (foldMap fvs c <> fvs t) Set.\\ Set.fromList (tyVarBndrName <$> bndrs)
fvs (ForallVisT bndrs t) = fvs t Set.\\ Set.fromList (tyVarBndrName <$> bndrs)
fvs ConT{} = mempty
fvs PromotedT{} = mempty

makeSing' :: SingRules -> Name -> [TyVarBndr] -> Maybe Kind -> [Con] -> Q [Dec]
makeSing' SingRules{..} name bndrs _mkind cons = do
-- this is buggy for some reason in the repl, enabling the extensions doesn't cause this to pass
{-
  let exts = [StandaloneKindSignatures, GADTs, RoleAnnotations, DataKinds, PolyKinds, PatternSynonyms]
  enabled <- for exts isExtEnabled
  unless (and enabled) do
    fail $ "makeSing: Required language extensions are missing: " ++ intercalate ", " [ show e | e <- exts | False <- enabled ]
-}

  concat <$> sequence
    [ pure <$> makeKiSig
    , pure <$> makeRole
    , pure <$> makeData
    , makeUp
    , concat <$> traverse makePattern cons
    , pure <$> makeComplete
    , concat <$> traverse makeSingI cons
    ] where
    sname = singTyCon name

    fvbs (PlainTV _) = mempty
    fvbs (KindedTV _ k) = fvs k

    prebndrs = PlainTV <$> Set.toList (foldMap fvbs bndrs)

    -- type SEither' :: forall a b. Either a b -> Type
    makeKiSig :: Q Dec
    makeKiSig
      = kiSigD sname  -- type SEither'
      $ forallT (prebndrs ++ bndrs) (pure []) -- :: forall a b.
      $ foldl (\l r -> l `appT` varT (tyVarBndrName r)) (conT name) bndrs `arrT` pure starK -- Either a b -> Type

    -- type role SEither' nominal
    makeRole :: Q Dec
    makeRole = roleAnnotD sname [nominalR]

    -- data SEither' t where
    --   SLeft'  :: Sing a -> SEither' ('Left a)
    --   SRight' :: Sing b -> SEither' ('Right b)
    makeData :: Q Dec
    makeData = dataD (pure []) sname [plainTV (mkName "n")] Nothing (cons >>= go) [] where
      go = \case
        NormalC cname cbtys -> pure $ makeDataCon cname $ fst <$> cbtys
        RecC cname cvbtys -> pure $ makeDataCon cname $ cvbtys <&> \(_,b,_) -> b
        GadtC cnames cbtys _ -> cnames <&> \cname -> makeDataCon cname $ fst <$> cbtys
        RecGadtC cnames cvbtys _ -> cnames <&> \cname -> makeDataCon cname $ cvbtys <&> \(_,b,_) -> b
        ForallC _ _ con -> go con
        InfixC (b,_) cname (b',_) -> pure $ makeDataCon cname [b,b']
        -- d -> fail $ "makeSing: unsupported data constructor type\n\n" ++ pprint d

    makeDataCon :: Name -> [Bang] -> Q Con
    makeDataCon cname bangs = do
      bns <- for (zipWith (,) bangs (cycle ['a'..'z'])) \case
        (b,c) -> (,) b <$> (newName (pure c) >>= varT)
      gadtC [singDataCon' cname] (traverse (appT csing . pure) <$> bns) $
        conT sname `appT` foldl (\l (_,n) -> appT l (pure n)) (promotedT cname) bns

    thd (_,_,x) = x

    -- this seems misimplemented
    -- instance SingI a => SingI ('Left a) where sing = SLeft sing
    makeSingI :: Con -> Q [Dec]
    makeSingI = \case
        NormalC n ts -> pure <$> makeSingI' n (snd <$> ts)
        RecC n ts    -> pure <$> makeSingI' n (thd <$> ts)
        d -> fail $ "makeSing.makeSingI: unsupported data constructor type\n\n" ++ pprint d

    makeSingI' :: Name -> [Type] -> Q Dec
    makeSingI' n tys = instanceD cxt' typeQ
      [ valD (varP 'sing) (normalB $ foldl (\l _ -> appE l (varE 'sing)) (conE $ singDataCon n) tys) []
      ] where
      qtys = pure <$> tys
      cxt' = for qtys $ appT (conT ''SingI)
      typeQ = appT csingi $ foldl appT (promotedT n) qtys

{-
    conName :: Con -> Name
    conName (NormalC n _) = n
    conName (RecC n _) = n
    conName (InfixC _ n _) = n
    conName _ = error "unsupported constructor type"
-}

    fresh :: Int -> Q [Name]
    fresh n = traverse (newName . pure) $ take n $ cycle ['a'..'z']

    -- upSEither :: Sing a -> SEither' a
    -- upSEither (Sing (Left a))  = unsafeCoerce (SLeft' (UnsafeSing a))
    -- upSEither (Sing (Right b)) = unsafeCoerce (SRight' (UnsafeSing b))
    makeUp :: Q [Dec]
    makeUp = sequence $
      [ sigD (singUp name) $ appT csing (varT (mkName "a")) `arrT` appT (conT sname) (varT (mkName "a"))
      , funD (singUp name) (cons >>= go)
      ] where
      go = \case
        NormalC n (length -> d) -> [makeUpClause d n]
        RecC n (length -> d) -> [makeUpClause d n]
        GadtC ns (length -> d) _ -> makeUpClause d <$> ns
        RecGadtC ns (length -> d) _ -> makeUpClause d <$> ns
        ForallC _ _ con -> go con
        InfixC _ n _ -> [makeUpClause 2 n]
        -- d -> fail $ "makeSing.makeUp: unsupported data constructor type\n\n" ++ pprint d

    makeUpClause :: Int -> Name -> Q Clause
    makeUpClause d n = do
      args <- fresh d
      clause
        [conP 'Sing [conP n (varP <$> args)]]
        do normalB $ varE 'unsafeCoerce `appE`
             foldl (\l r -> l `appE` (conE 'UnsafeSing `appE` varE r)) (conE (singDataCon' n)) args
        []

    eqT :: Q Type -> Q Type -> Q Type
    eqT x y = equalityT `appT` x `appT` y

    -- we can't mimic the original record type, because they could have multiple field accessors of
    -- the same name, and record pattern synonyms can't share names
    makePattern :: Con -> Q [Dec]
    makePattern = \case
      NormalC n (length -> d) -> makePattern' d n
      RecC n (length -> d) -> makePattern' d n
      GadtC ns (length -> d) _ -> concat <$> traverse (makePattern' d) ns
      RecGadtC ns (length -> d) _ -> concat <$> traverse (makePattern' d) ns
      ForallC _ _ con -> makePattern con
      InfixC _ n _ -> makePattern' 2 n
      -- d -> fail $ "makeSing.makePattern: unsupported data constructor type\n\n" ++ pprint d

    -- pattern SLeft :: () => (ma ~ 'Left a) => Sing a -> Sing ma
    -- pattern SLeft a <- (upSEither -> SLeft' a) where
    --   SLeft (Sing a) = UnsafeSing (Left a)
    makePattern' :: Int -> Name -> Q [Dec]
    makePattern' d cname = do
        args <- fresh d
        res <- newName "r"
        let patSynType = forallT [] (pure []) $ forallT [] lessons $
              foldr (\l r -> (csing `appT` varT l) `arrT` r) (csing `appT` varT res) args
            lessons = sequence
              [eqT (varT res) (foldl (\l r -> l `appT` varT r) (promotedT cname) args)]
              -- :[] -- : [ eqT (varT v) (pure t) | v <- args | t <- tys ]
            clauses = pure $ clause pats body [] where
               pats = [ conP 'Sing [varP a] |  a <- args ]
               body = normalB $ conE 'UnsafeSing `appE` do
                 foldl (\l r -> l `appE` varE r) (conE cname) args
            pat = viewP (varE (singUp name)) $ conP (singDataCon' cname) (varP <$> args)
            dir = explBidir clauses
        sequence
          [ patSynSigD (singDataCon cname) patSynType
          , patSynD (singDataCon cname) (prefixPatSyn args) dir pat
          ]

    -- {-# complete SLeft, SRight #-}
    makeComplete :: Q Dec
    makeComplete = pure $ PragmaD $ CompleteP (cons >>= fmap singDataCon . go) Nothing where
      go = \case
        NormalC n _ -> [n]
        RecC n _    -> [n]
        GadtC ns _ _ -> ns
        RecGadtC ns _ _ -> ns
        ForallC _ _ c -> go c
        InfixC _ n _ -> [n]

