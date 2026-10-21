module Piko.Infer where

import Piko.Ast (X(..), Scheme(..), pattern (:->))
import Control.Lens hiding (Context, (<.>))
import Effectful.Writer.Static.Local
import Effectful.State.Static.Local
import qualified Piko.Ast as Ast
import qualified Data.Map as Map
import qualified Data.Set as Set
import Effectful.Reader.Static
import Data.Text (Text, pack)
import Effectful.Error.Static
import Piko.Reduce (reduce)
import Data.Map (Map)
import Data.Set (Set)
import Piko.Convert
import Piko.Counter
import Effectful
import Data.Void

data Local = Local
  { types :: !(Map Text Ast.Kind)
  , tcons :: !(Map Text Ast.Kind)
  , subst :: !(Map Text Ast.Kind)
  }

kinds :: Map Text Ast.Kind
kinds = Map.fromList
  [ ("num",    Ast.KindType)
  , ("dec",    Ast.KindType)
  , ("bin",    Ast.KindType)
  , ("nil",    Ast.KindType)
  , ("lst",    Ast.KindArr Ast.KindType Ast.KindType)
  , ("IO",     Ast.KindArr Ast.KindType Ast.KindType)
  , ("->",     Ast.KindArr Ast.KindType (Ast.KindArr Ast.KindType Ast.KindType))
  ]

emptyLocal :: Local
emptyLocal = Local
  { types = mempty
  , tcons = kinds
  , subst = mempty
  }

freshKind :: ( State Local :> es
             , Counter :> es
             ) => Eff es Ast.Kind
freshKind = Ast.KindVar . pack . show <$> freshInt

resolve :: State Local :> es => Ast.Kind -> Eff es Ast.Kind
resolve = \case
  Ast.KindType    -> pure Ast.KindType
  Ast.KindVar v   -> do
    s <- subst <$> get @Local

    case Map.lookup v s of
      Just k  -> resolve k
      Nothing -> pure $ Ast.KindVar v

  Ast.KindArr x y -> Ast.KindArr <$> resolve x <*> resolve y

occurs :: Text -> Ast.Kind -> Bool
occurs v = \case
  Ast.KindType    -> False
  Ast.KindVar v'  -> v == v'
  Ast.KindArr x y -> occurs v x || occurs v y

bindKind :: ( Error Ast.InferError :> es
            , State Local :> es
            ) => Text -> Ast.Kind -> Eff es ()

bindKind v k
  | occurs v k = throwError $ Ast.InfiniteKind v k
  | otherwise  = modify @Local $ \x ->
                                   x { subst = Map.insert v k (subst x) }

unifyKind :: ( Error Ast.InferError :> es
             , State Local :> es
             ) => Ast.Kind -> Ast.Kind -> Eff es ()
unifyKind x y = do
  x' <- resolve x
  y' <- resolve y

  if x' == y'
    then pure ()
    else case (x', y') of
           (Ast.KindVar v, k)                   -> bindKind v k
           (k, Ast.KindVar v)                   -> bindKind v k

           (Ast.KindArr x y, Ast.KindArr x' y') -> do
             unifyKind x x'
             unifyKind y y'
           _                                    -> throwError $ Ast.KindMismatch x' y'

inferKind :: ( Error Ast.InferError :> es
             , State Local :> es
             , Counter :> es
             ) => Ast.Ty -> Eff es Ast.Kind

inferKind = \case
  Ast.TyCon n -> gets (Map.lookup n . tcons) >>= \case
    Just k  -> pure k
    Nothing -> throwError $ Ast.UnknownTypeConstructor n

  Ast.TyVar v -> do
    x <- get @Local

    case Map.lookup v (types x) of
      Just k  -> resolve k
      Nothing -> do
        k <- freshKind

        modify @Local $ \x ->
          x { types = Map.insert v k (types x) }

        pure k

  Ast.TyApp f x -> do
    fk <- inferKind f
    xk <- inferKind x
    rk <- freshKind

    unifyKind fk (Ast.KindArr xk rk)

    resolve rk

check :: ( Error Ast.InferError :> es
         , State Local :> es
         , Counter :> es
         ) => Ast.Ty -> Eff es ()
check t = do
  k <- inferKind t
  unifyKind k Ast.KindType

compatible :: ( Error Ast.InferError :> es
              , State Local :> es
              , Counter :> es
              ) => Ast.Ty -> Ast.Ty -> Eff es ()

compatible x y = do
  xk <- inferKind x
  yk <- inferKind y

  unifyKind xk yk

data Constraint  = Constraint Ast.Ty Ast.Ty
type Constraints = [Constraint]

type Context     = [Ast.Scheme]

type Subst       = Map Text Ast.Ty

type Scope       = Map Text Ast.Scheme

type Builtins    = Map Text Ast.Scheme

type Inference es
  = ( Error Ast.InferError :> es
    , Writer Constraints :> es
    , Reader Builtins :> es
    , Reader Context :> es
    , State Local :> es
    , State Scope :> es
    , Counter :> es
    )

infixr 8 <=>

(<=>) :: Inference es => Ast.Ty -> Ast.Ty -> Eff es ()
(<=>) x y = do
  check x
  check y

  tell (Constraint x y:[])

freshTy :: Inference es => Eff es Ast.Ty
freshTy = Ast.TyVar . pack . show <$> freshInt

(<.>) :: Subst -> Subst -> Subst
(<.>) a b = (a .$) <$> (b `Map.union` a)

class Substitutable a where
  vars :: a -> Set Text
  (.$) :: Subst -> a -> a

instance Substitutable Ast.Ty where
  vars (Ast.TyVar t)   = Set.singleton t
  vars (Ast.TyCon _)   = mempty
  vars (Ast.TyApp x y) = vars x `Set.union` vars y

  s .$ t@(Ast.TyVar t') = Map.findWithDefault t t' s
  s .$ x                = x & plate %~ (s .$)

instance Substitutable Ast.Scheme where
  vars (v :&: t) = vars t `Set.difference` v
  s .$ (v :&: t) = v :&: foldr Map.delete s v .$ t

instantiate :: Inference es => Ast.Scheme -> Eff es Ast.Ty
instantiate (v :&: t) = do
  let vars = Set.toList v
  vs <- traverse (const freshTy) vars
  let subst = Map.fromList (zip vars vs)
      t'    = subst .$ t

  check t'

  pure t'

generalize :: Context -> Ast.Ty -> Ast.Scheme
generalize ctx t = vars t `Set.difference` vars ctx :&: t

instance Substitutable Constraint where
  vars (Constraint t t') = vars t `Set.union` vars t'
  s .$ (Constraint t t') = Constraint (s .$ t) (s .$ t')

instance Substitutable a => Substitutable [a] where
  vars   = foldr (Set.union . vars) mempty
  (.$) s = fmap (s .$)

instance Substitutable (Ast.Exp Typed) where
  vars = \case
    Ast.ExpApp (_, t) f a    -> vars t `Set.union` vars f `Set.union` vars a
    Ast.ExpLet (_, t) p x y  -> vars t `Set.union` vars x `Set.union` vars y
    Ast.ExpAbs (_, t) p body -> vars t `Set.union` vars t
    Ast.ExpLit (_, t) _      -> vars t
    Ast.ExpVar (_, t)        -> vars t
    Ast.ExpExt (_, t)        -> vars t

  s .$ expr = case expr of
    Ast.ExpApp (c, t) f a    -> Ast.ExpApp (c, s .$ t) (s .$ f) (s .$ a)
    Ast.ExpLet (c, t) p x y  -> Ast.ExpLet (c, s .$ t) p (s .$ x) (s .$ y)
    Ast.ExpAbs (c, t) p body -> Ast.ExpAbs (c, s .$ t) p (s .$ body)
    Ast.ExpLit (c, t) lit    -> Ast.ExpLit (c, s .$ t) lit
    Ast.ExpVar (c, t)        -> Ast.ExpVar (c, s .$ t)
    Ast.ExpExt (c, t)        -> Ast.ExpExt (c, s .$ t)


class Inferable a where
  type Resolved a

  infer :: Inference es => a -> Eff es (Resolved a)

bind :: Inference es => Text -> Ast.Ty -> Eff es Subst
bind v t
  | v `Set.member` vars t = throwError $ Ast.Infinite v t
  | otherwise             = pure $ Map.singleton v t

unify :: Inference es => Ast.Ty -> Ast.Ty -> Eff es Subst
unify a b = do
  compatible a b

  f a b
  where
    f a b | a == b    = pure mempty
    f (Ast.TyVar v) t = bind v t
    f t (Ast.TyVar v) = bind v t

    f (Ast.TyApp x y) (Ast.TyApp x' y') = do
      s  <- unify x x'
      s' <- unify (s .$ y) (s .$ y')

      pure $ s' <.> s

    f a b = throwError $ Ast.Mismatch a b

solve :: Inference es => [Constraint] -> Eff es Subst
solve = f mempty
  where
    f s []                     = pure s
    f s ((Constraint t t'):cs) = do
      s' <- unify t t'
      f (s' <.> s) (s' .$ cs)

ty :: ( Substitutable (Resolved a)
      , Error Ast.InferError :> es
      , Inferable a
      ) => a -> Eff es (Resolved a)
ty = tyWithKinds Ast.builtinSchemes emptyLocal

tyWithKinds :: ( Substitutable (Resolved a)
               , Error Ast.InferError :> es
               , Inferable a
               ) => Builtins -> Local -> a -> Eff es (Resolved a)

tyWithKinds builtins kindLocal = tyWithEnv builtins kindLocal mempty

tyWithEnv :: ( Substitutable (Resolved a)
             , Error Ast.InferError :> es
             , Inferable a
             ) => Builtins -> Local -> Scope -> a -> Eff es (Resolved a)

tyWithEnv builtins kindLocal valueLocal inf = fst <$> m
  where
    m      = f inf & runCounter
             . runWriter @Constraints
             . runReader @Context []
             . evalState @Scope valueLocal
             . evalState @Local kindLocal
             . runReader @Builtins builtins

    f inf = do
      (t, cs) <- inject $ infer inf & runWriter @Constraints
      s       <- solve cs
      pure $ s .$ t

instance Inferable (Ast.Exp Infer) where
  type Resolved (Ast.Exp Infer) = Ast.Exp Typed

  infer = \case
    Ast.ExpLit s l@(Ast.LitDec s' l') -> pure $ Ast.ExpLit (s, Ast.TyDec) (Ast.LitDec (s', Ast.TyDec) l')
    Ast.ExpLit s l@(Ast.LitNum s' l') -> pure $ Ast.ExpLit (s, Ast.TyNum) (Ast.LitNum (s', Ast.TyNum) l')
    Ast.ExpLit s l@(Ast.LitBin s' l') -> pure $ Ast.ExpLit (s, Ast.TyBin) (Ast.LitBin (s', Ast.TyBin) l')
    Ast.ExpLit s l@(Ast.LitStr s' l') -> pure $ Ast.ExpLit (s, Ast.TyStr) (Ast.LitStr (s', Ast.TyStr) l')
    Ast.ExpLit s l@(Ast.LitChr s' l') -> pure $ Ast.ExpLit (s, Ast.TyChr) (Ast.LitChr (s', Ast.TyChr) l')
    Ast.ExpLit s   (Ast.LitExt void)  -> pure $ absurd void
    Ast.ExpExt (s, t)                 -> throwError $ Ast.Unbound s t

    Ast.ExpLet s p x y                -> do
      (et, cs) <- listen  (infer x)
      let t = Ast.tyOf et
      subst    <- solve cs
      let et' = subst .$ t
      ctx      <- ask @Context
      scope    <- get @Scope
      let ctx'   = subst .$ ctx
          scope' = Map.map (subst .$) scope
          es     = generalize (ctx' ++ Map.elems scope') et'

      put @Scope scope'

      y' <- local (const (es : ctx')) (infer y)
      let yt = Ast.tyOf y'

      let p' = convert @Ast.Pat @Infer @Typed p & runPureEff

      pure $ Ast.ExpLet (s, yt) p' (subst .$ et) y'

    Ast.ExpApp s f a                  -> do
      f' <- infer f
      a' <- infer a

      let ft = Ast.tyOf f'
          at = Ast.tyOf a'

      rt <- freshTy

      ft <=> at :-> rt

      pure $ Ast.ExpApp (s, rt) f' a'

    Ast.ExpVar (s, b, (x, y))         -> do
      ctx <- ask @Context
      case drop x ctx of
        (t:_) -> do
          v <- instantiate t
          pure $ Ast.ExpVar ((s, b, (x, y)), v)
        []    -> throwError (Ast.Undefined s b)

    Ast.ExpAbs s p x                  -> do
      pt <- freshTy
      let ps = mempty :&: pt
      x' <- local (ps:) (infer x)
      let xt = Ast.tyOf x'

      check (pt :-> xt)

      let p' = convert @Ast.Pat @Infer @Typed p & runPureEff

      pure $ Ast.ExpAbs (s, (pt :-> xt)) p' x'

instance Convert Ast.Exp Infer Typed where
  type Es Ast.Exp Infer Typed = '[Error Ast.InferError]

  convert exp = do
    _ <- ty exp
    ty (reduce exp)
