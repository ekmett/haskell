{-# Language LambdaCase #-}
{-# Language TemplateHaskellQuotes #-}
{-# Language RecordWildCards #-}
{-# Language ViewPatterns #-}
{-# Language BlockArguments #-}
{-# Language ParallelListComp #-}
{-# Language ImportQualifiedPost #-}
{-# Language Unsafe #-}
{-# OPTIONS_GHC -Wno-unused-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Data.Type.TH 
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
  , singField    :: Name -> Name
  , singField'   :: Name -> Name
  , singUp       :: Name -> Name
  }

defaultSingRules :: SingRules
defaultSingRules = SingRules{..} where
  singTyCon    =  mkName . (++"'") . ('S':) . nameBase
  singDataCon  =  mkName  . ('S':) . nameBase
  singDataCon' =  mkName . (++"'") . ('S':) . nameBase
  singField    =  mkName  . ('s':) . nameBase
  singField'   =  mkName  . (++"'") . ('s':) . nameBase
  singUp       =  mkName . ("upS"++) . nameBase

makeSingWith :: SingRules -> Name -> Q [Dec]
makeSingWith opts n = TH.reify n >>= \case
  TyConI d -> case d of
    DataD    [] name tyvars mkind cons _ -> makeSing' opts name tyvars mkind cons
    NewtypeD [] name tyvars mkind con _ -> makeSing' opts name tyvars mkind [con]
    _ -> fail "makeSing: can only handle data and newtype declarations"
  _ -> fail "mkSing: unsupported type"

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
    , traverse makeSingI cons
    -- , makeComplete
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
    makeData = dataD (pure []) sname [plainTV (mkName "n")] Nothing scons [] where
      scons = cons <&> \case
        --NormalC cname cbtys -> normalC (singDataCon' cname) $ cbtys <&> \case
        --  (b,t) -> (,) b <$> appT csing (pure t)
        --RecC cname cvbtys -> recC (singDataCon' cname) $ cvbtys <&> \case
        --  (field,b,t) -> (,,) (singField field) b <$> appT csing (pure t)
        NormalC cname cbtys -> do
          bns <- for (zipWith (,) (cycle ['a'..'z']) cbtys) \case
              (c,(b,_)) -> (,) b <$> (newName (pure c) >>= varT)
          gadtC [singDataCon' cname] (traverse (appT csing . pure) <$> bns) $
            conT sname `appT` foldl (\l (_,n) -> appT l (pure n)) (promotedT cname) bns
        RecC cname cvbtys -> do
          bns <- for (zipWith (,) (cycle ['a'..'z']) cvbtys) \case
              (c,(f,b,_)) -> (,,) (singField' f) b <$> (newName (pure c) >>= varT)
          recGadtC [singDataCon' cname] (_3 (appT csing . pure) <$> bns) $
            conT sname `appT` foldl (\l (_,_,n) -> appT l (pure n)) (promotedT cname) bns
        _ -> fail "makeSing: unsupported data constructor type"

    -- instance SingI a => SingI ('Left a) where sing = SLeft sing
    makeSingI :: Con -> Q Dec
    makeSingI = \case
        NormalC n btys -> makeSingI' n (snd <$> btys)
        RecC n vbtys   -> makeSingI' n $ vbtys <&> \(_,_,x) -> x
        _ -> fail "makeSing: unsupported data constructor type"

    makeSingI' :: Name -> [Type] -> Q Dec
    makeSingI' n tys = instanceD cxt' typeQ
      [ valD (varP 'sing) (normalB $ foldl (\l _ -> appE l (varE 'sing)) (conE $ singDataCon n) tys) []
      ] where
      qtys = pure <$> tys
      cxt' = for qtys $ appT (conT ''SingI)
      typeQ = appT csingi $ foldl appT (promotedT n) qtys

    conName :: Con -> Name
    conName (NormalC n _) = n
    conName (RecC n _) = n
    conName (InfixC _ n _) = n
    conName _ = error "unsupported constructor type"

    fresh :: [a] -> Q [Name]
    fresh tys = sequence [ newName [c] | c <- cycle ['a'..'z'] | _ <- tys ]

    makeUp :: Q [Dec]
    makeUp = sequence $
        -- upSEither :: Sing a -> SEither' a
      [ sigD (singUp name) $ appT csing (varT (mkName "a")) `arrT` appT (conT sname) (varT (mkName "a"))
        -- upSEither (Sing (Left a))  = unsafeCoerce (SLeft' (UnsafeSing a))
        -- upSEither (Sing (Right b)) = unsafeCoerce (SRight' (UnsafeSing b))

      , funD (singUp name) clauses
      ] where
      clauses = cons <&> \case
        NormalC n btys -> do
          args <- fresh btys
          clause
            [conP 'Sing [conP n (varP <$> args)]]
            do normalB $ varE 'unsafeCoerce `appE`
                 foldl (\l r -> l `appE` (conE 'UnsafeSing `appE` varE r)) (conE (singDataCon' n)) args
            []
        RecC n vbtys -> do
          args <- fresh vbtys
          clause
            [conP 'Sing [conP n (varP <$> args)]]
            do normalB $ varE 'unsafeCoerce `appE`
                 foldl (\l r -> l `appE` (conE 'UnsafeSing `appE` varE r)) (conE (singDataCon' n)) args
            []
        _ -> fail "makeSing.makeUp: unsupported data constructor type"
         
    -- we can't mimic the original record type, because they could have multiple field accessors of
    -- the same name, and record pattern synonyms can't share names
    makePattern :: Con -> Q [Dec]
    makePattern = \case
      NormalC cname btys -> makePattern' cname (snd <$> btys)
      RecC cname vbtys -> makePattern' cname (vbtys <&> \(_,_,x) -> x)
      _ -> fail "makeSing.makePattern: unsupported data constructor type"

    eqT :: Q Type -> Q Type -> Q Type
    eqT x y = equalityT `appT` x `appT` y

    -- pattern SLeft :: () => (ma ~ 'Left a) => Sing a -> Sing ma
    -- pattern SLeft a <- (upSEither -> SLeft' a) where
    --   SLeft (Sing a) = UnsafeSing (Left a)
    makePattern' :: Name -> [Type] -> Q [Dec]
    makePattern' cname tys = do
        args <- fresh tys
        res <- newName "res"
        let patSynType = forallT [] (pure []) $ forallT [] lessons $ 
              foldr (\l r -> (csing `appT` varT l) `arrT` r) (csing `appT` varT res) args
            lessons = sequence
              $ eqT (varT res) (foldl (\l r -> l `appT` varT r) (promotedT cname) args)
              : [ eqT (varT v) (pure t) | v <- args | t <- tys ] 
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
    makeComplete :: Q [Dec]
    makeComplete = pure []
