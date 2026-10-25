module Piko.Infer where

import Piko.Ast (X(..), Scheme(..), pattern (:->))
import qualified Control.Monad.State.Lazy as Lazy
import qualified Text.Megaparsec as Megaparsec
import Data.Graph (SCC(..), stronglyConnComp)
import Control.Lens hiding (Context, (<.>))
import Piko.Reduce (reduce, Reduce(..))
import Data.Text (Text, pack, unpack)
import Effectful.Writer.Static.Local
import qualified Piko.Parse as Parse
import Effectful.State.Static.Local
import qualified Data.Text as Text
import qualified Piko.Ast as Ast
import qualified Data.Map as Map
import qualified Data.Set as Set
import Effectful.Reader.Static
import Effectful.Error.Static
import Text.Show.Pretty
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad
import Piko.Convert
import Piko.Counter
import Piko.Diag
import Effectful
import Data.Void

data Local = Local
  { types :: !(Map Text Ast.Kind)
  , tcons :: !(Map Text Ast.Kind)
  , subst :: !(Map Text Ast.Kind)
  }

kinds :: Map Text Ast.Kind
kinds = Map.fromList
  [ ("Num",    Ast.KindType)
  , ("Dec",    Ast.KindType)
  , ("Bin",    Ast.KindType)
  , ("Nil",    Ast.KindType)
  , ("Str",    Ast.KindType)
  , ("Chr",    Ast.KindType)
  , ("Sym",    Ast.KindType)
  , ("Lst",    Ast.KindArr Ast.KindType Ast.KindType)
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
  Ast.TyCon s n -> gets (Map.lookup n . tcons) >>= \case
    Just k  -> pure k
    Nothing -> throwError $ Ast.UnknownTypeConstructor s n

  Ast.TyTup ts -> do
    mapM_ check ts
    pure Ast.KindType

  Ast.TyVar _ v -> do
    x <- get @Local

    case Map.lookup v (types x) of
      Just k  -> resolve k
      Nothing -> do
        k <- freshKind

        modify @Local $ \x ->
          x { types = Map.insert v k (types x) }

        pure k

  Ast.TyApp _ f x -> do
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

data Constraint  = Constraint Ast.Span Ast.Ty Ast.Ty
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

constrain :: Inference es => Ast.Span -> Ast.Ty -> Ast.Ty -> Eff es ()
constrain s x y = do
  check x
  check y

  tell [Constraint s x y]

alphabetize :: Int -> Text
alphabetize n
  | n < 0     = "t" <> Text.pack (show n)
  | otherwise = Text.singleton letter <> suffix
  where
    letter = toEnum (fromEnum 'a' + n `mod` 26)
    suffix
      | n < 26    = ""
      | otherwise = Text.pack (show (n `div` 26))

freshTy :: Inference es => Eff es Ast.Ty
freshTy = Ast.TyVar mempty . alphabetize <$> freshInt

(<.>) :: Subst -> Subst -> Subst
(<.>) a b = (a .$) <$> (b `Map.union` a)

class Substitutable a where
  vars :: a -> Set Text
  (.$) :: Subst -> a -> a

instance Substitutable Ast.Ty where
  vars (Ast.TyVar _ t)   = Set.singleton t
  vars (Ast.TyCon _ _)   = mempty
  vars (Ast.TyApp _ x y) = vars x `Set.union` vars y

  s .$ t@(Ast.TyVar _ t') = Map.findWithDefault t t' s
  s .$ x                  = x & plate %~ (s .$)

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
  vars (Constraint s t t') = vars t `Set.union` vars t'
  s .$ (Constraint p t t') = Constraint p (s .$ t) (s .$ t')

instance Substitutable a => Substitutable [a] where
  vars   = foldr (Set.union . vars) mempty
  (.$) s = fmap (s .$)

instance Substitutable (Ast.Fn Typed) where
  vars (Ast.Fn _ mt _ expr)  = vars expr `Set.union` maybe mempty (vars . snd) mt 
  s .$ (Ast.Fn sp mt n expr) = Ast.Fn sp (fmap (\(sp', t) -> (sp', s .$ t)) mt) n (s .$ expr)

instance Substitutable (Ast.Item Typed) where
  vars (Ast.ItemMain expr) = vars expr
  vars (Ast.ItemFn fn)     = vars fn

  s .$ (Ast.ItemMain expr) = Ast.ItemMain (s .$ expr)
  s .$ (Ast.ItemFn   fn)   = Ast.ItemFn   (s .$ fn)

instance Substitutable (Ast.Exp Typed) where
  vars = \case
    Ast.ExpApp (_, t) f a    -> vars t `Set.union` vars f `Set.union` vars a
    Ast.ExpLet (_, t) p x y  -> vars t `Set.union` vars x `Set.union` vars y
    Ast.ExpAbs (_, t) p body -> vars t `Set.union` vars body
    Ast.ExpLit (_, t) _      -> vars t
    Ast.ExpVar (_, t)        -> vars t
    Ast.ExpExt (_, t)        -> vars t
    Ast.ExpLst (_, t) _      -> vars t
    Ast.ExpTup (_, t) _      -> vars t
    Ast.ExpCnd (_, t) _ _ _  -> vars t

  s .$ expr = case expr of
    Ast.ExpApp (c, t) f a    -> Ast.ExpApp (c, s .$ t) (s .$ f) (s .$ a)
    Ast.ExpLet (c, t) p x y  -> Ast.ExpLet (c, s .$ t) p (s .$ x) (s .$ y)
    Ast.ExpAbs (c, t) p body -> Ast.ExpAbs (c, s .$ t) p (s .$ body)
    Ast.ExpLit (c, t) lit    -> Ast.ExpLit (c, s .$ t) lit
    Ast.ExpVar (c, t)        -> Ast.ExpVar (c, s .$ t)
    Ast.ExpExt (c, t)        -> Ast.ExpExt (c, s .$ t)
    Ast.ExpLst (c, t) a      -> Ast.ExpLst (c, s .$ t) ((s .$) <$> a)
    Ast.ExpTup (c, t) b      -> Ast.ExpTup (c, s .$ t) ((s .$) <$> b)
    Ast.ExpCnd (c, t) x y z  -> Ast.ExpCnd (c, s .$ t) (s .$ x) (s .$ y) (s .$ z)

class Inferable a where
  type Resolved a

  infer :: Inference es => a -> Eff es (Resolved a)

bind :: Inference es => Ast.Span -> Text -> Ast.Ty -> Eff es Subst
bind s v t
  | v `Set.member` vars t = throwError $ Ast.Infinite s v t
  | otherwise             = pure $ Map.singleton v t

unify :: Inference es => Ast.Span -> Ast.Ty -> Ast.Ty -> Eff es Subst
unify sp a b = do
  compatible a b
  f a b
  where
    f a b | a == b    = pure mempty
    f (Ast.TyVar _ v) t = bind sp v t
    f t (Ast.TyVar _ v) = bind sp v t

    f (Ast.TyApp sp' x y) (Ast.TyApp sp'' x' y') = do
      let thisspan = sp' <> sp''
      s  <- unify thisspan x x'
      s' <- unify thisspan (s .$ y) (s .$ y')

      pure $ s' <.> s

    
    f (Ast.TyTup xs) (Ast.TyTup ys)
      | length xs == length ys = do
          foldM
            (\s (x, y) -> do
                s' <- unify sp (s .$ x) (s .$ y)
                pure (s' <.> s))
            mempty
            (zip xs ys)

    f a b = throwError $ Ast.Mismatch sp a b

solve :: Inference es => [Constraint] -> Eff es Subst
solve = f mempty
  where
    f s []                        = pure s
    f s ((Constraint sp t t'):cs) = do
      s' <- unify sp t t'
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

instance Inferable (Ast.Pat Infer) where
  type Resolved (Ast.Pat Infer) = (Ast.Ty, [Ast.Scheme])

  infer = \case
    Ast.PatVar (_, _, _) -> do
      t <- freshTy
      pure (t, [mempty :&: t])

    Ast.PatTup _ ps -> do
      inferred <- traverse infer ps

      let ts       = map fst inferred
          bindings = concatMap snd inferred
          t        = Ast.TyTup ts

      pure (t, bindings)

    Ast.PatLst s ps -> do
      eTy <- freshTy
      i <- traverse infer ps

      mapM_ (\(t, _) -> constrain s t eTy) i

      pure ( Ast.TyApp mempty (Ast.TyCon mempty "Lst") eTy
           , concatMap snd i
           )

    Ast.PatLit s lit -> do
      e <- infer (Ast.ExpLit s lit)
      pure (Ast.tyOf e, [])


instance Inferable (Ast.Exp Infer) where
  type Resolved (Ast.Exp Infer) = Ast.Exp Typed

  infer = \case
    Ast.ExpLit s l@(Ast.LitDec s' l') -> pure $ Ast.ExpLit (s, Ast.TyDec) (Ast.LitDec (s', Ast.TyDec) l')
    Ast.ExpLit s l@(Ast.LitNum s' l') -> pure $ Ast.ExpLit (s, Ast.TyNum) (Ast.LitNum (s', Ast.TyNum) l')
    Ast.ExpLit s l@(Ast.LitBin s' l') -> pure $ Ast.ExpLit (s, Ast.TyBin) (Ast.LitBin (s', Ast.TyBin) l')
    Ast.ExpLit s l@(Ast.LitStr s' l') -> pure $ Ast.ExpLit (s, Ast.TyStr) (Ast.LitStr (s', Ast.TyStr) l')
    Ast.ExpLit s l@(Ast.LitChr s' l') -> pure $ Ast.ExpLit (s, Ast.TyChr) (Ast.LitChr (s', Ast.TyChr) l')
    Ast.ExpLit s l@(Ast.LitNil s')    -> pure $ Ast.ExpLit (s, Ast.TyNil) (Ast.LitNil (s', Ast.TyNil))
    Ast.ExpLit s   (Ast.LitExt void)  -> pure $ absurd void

    Ast.ExpExt (s, t)                 -> do
      scoped <- get @Scope

      case Map.lookup t scoped of
        Just sc -> do
          x <- instantiate sc
          pure $ Ast.ExpExt ((s, t), x)
        Nothing -> do
          builtins <- ask @Builtins
          case Map.lookup t builtins of
            Just sc -> do
              x <- instantiate sc
              pure $ Ast.ExpExt ((s, t), x)
            Nothing -> throwError $ Ast.Unbound s t

    Ast.ExpCnd s x y z                -> do
      xt <- infer x
      yt <- infer y
      zt <- infer z

      constrain (Ast.spanOf xt) (Ast.tyOf xt) Ast.TyBin

      constrain s (Ast.tyOf yt) (Ast.tyOf zt)

      pure $ Ast.ExpCnd (s, Ast.tyOf yt) xt yt zt

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

      constrain s ft (at :-> rt)

      pure $ Ast.ExpApp (s, rt) f' a'

    Ast.ExpVar (s, b, (x, y))         -> do
      ctx <- ask @Context
      case drop x ctx of
        (t:_) -> do
          v <- instantiate t
          pure $ Ast.ExpVar ((s, b, (x, y)), v)
        []    -> throwError (Ast.Undefined s b)

    Ast.ExpLst s xs -> do
      xs' <- traverse infer xs
      t   <- freshTy

      traverse (\x -> constrain (Ast.spanOf x) (Ast.tyOf x) t) xs'

      pure $ Ast.ExpLst (s, Ast.TyLst t) xs'

    Ast.ExpTup s xs -> do
      xs' <- traverse infer xs

      let t = Ast.TyTup (map Ast.tyOf xs')

      pure $ Ast.ExpTup (s, t) xs'

    Ast.ExpAbs s p x -> do
      (pt, bindings) <- infer p
      x' <- local @Context (bindings ++) (infer x)

      let xt = Ast.tyOf x'

      check (pt :-> xt)

      let p' = convert @Ast.Pat @Infer @Typed p & runPureEff

      pure $ Ast.ExpAbs (s, pt :-> xt) p' x'

instance Inferable (Ast.Fn Infer) where
  type Resolved (Ast.Fn Infer) = Ast.Fn Typed

  infer (Ast.Fn s (Just (s', t)) n expr) = do
    exprt <- infer expr

    constrain s' t (Ast.tyOf exprt)

    pure $ Ast.Fn s (Just (s', t)) n exprt

  infer (Ast.Fn s Nothing n expr) = do
    exprt <- infer expr
    pure $ Ast.Fn s Nothing n exprt

instance Inferable (Ast.Item Infer) where
  type Resolved (Ast.Item Infer) = Ast.Item Typed

  infer (Ast.ItemMain expr) = do
    exprt <- infer expr

    constrain (Ast.spanOf exprt) (Ast.TyIO Ast.TyNil) (Ast.tyOf exprt)

    pure $ Ast.ItemMain exprt

  infer (Ast.ItemFn fn) = Ast.ItemFn <$> infer fn

instance Inferable (Ast.Module Infer) where
  type Resolved (Ast.Module Infer) = Ast.Module Typed

  infer x = do
    (mainItem, fns) <- Ast.splitMain x

    main            <- case mainItem of
                         Ast.ItemMain expr -> pure expr

    let groups = stronglyConnComp
          [ (fn, name, Set.toList (Ast.refs expr))
          | Ast.ItemFn fn@(Ast.Fn _ _ name expr) <- fns
          ]

    xs <- concat <$> mapM f groups

    let resolved = Map.fromList
          [ (name, fn)
          | fn@(Ast.Fn _ _ name _) <- xs
          ]

    main' <- infer main
    constrain (Ast.spanOf main') (Ast.tyOf main') (Ast.TyIO Ast.TyNil)

    fns' <- mapM (\item -> case item of
                     Ast.ItemFn (Ast.Fn sp _ name _) ->
                       case Map.lookup name resolved of
                         Just fn -> pure (Ast.ItemFn fn)
                         Nothing -> throwError $ Ast.Unbound sp name
                     Ast.ItemMain _ -> throwError Ast.UndefinedMain)
            fns
    pure (Ast.ItemMain main' : fns')
      where
        f group = do
          let xs = case group of
                     AcyclicSCC x -> [x]
                     CyclicSCC xs -> xs

          tys <- mapM (\(Ast.Fn _ _ name _) -> (name,) <$> freshTy) xs

          ctx    <- ask @Context
          locals <- get @Scope

          let inner = Map.fromList
                [ (name, mempty :&: t)
                | (name, t) <- tys
                ]

          put @Scope (inner `Map.union` locals)

          (ys, cs) <- listen $
            mapM (\(Ast.Fn sp sig name expr) -> do
                     expr' <- infer expr
                     let et = Ast.tyOf expr'

                     case Map.lookup name inner of
                       Just (_ :&: t) -> constrain sp t et
                       Nothing        -> throwError $ Ast.Unbound sp name

                     pure $ Ast.Fn sp sig name expr')
            xs

          subst <- solve cs

          let ctx'    = subst .$ ctx
              locals' = Map.map (subst .$) locals
              schemes = Map.fromList
                        [ (name, generalize (ctx' ++ Map.elems locals') (subst .$ t))
                        | (name, t) <- tys
                        ]

          put @Scope (schemes `Map.union` locals')

          pure $ subst .$ ys

instance Convert Ast.Fn Infer Typed where
  type Es Ast.Fn Infer Typed = '[Error Ast.InferError]

  convert fn = do
    fn' <- ty fn
    pure (reduce fn')

instance Convert Ast.Item Infer Typed where
  type Es Ast.Item Infer Typed = '[Error Ast.InferError]

  convert item = do
    item' <- ty item
    pure (reduce item')

  convertMany items = do
    items <- ty items
    pure (reduce <$> items)

instance Convert Ast.Exp Infer Typed where
  type Es Ast.Exp Infer Typed = '[Error Ast.InferError]

  convert expr = do
    expr' <- ty expr
    pure (reduce expr')

test :: Text -> IO ()
test t = case Lazy.evalState (Megaparsec.runParserT (Parse.module' <* Megaparsec.eof) "test.piko" t) Parse.emptyCtx of
           Left  x -> putStr (Megaparsec.errorBundlePretty x) 
           Right y -> let x = convertMany @_ @Parse @Typed y
                            & runPureEff
                            . runErrorNoCallStack
                            . runReader []
                      in case x of
                           Left e  -> putStrLn $ unpack $ (diag e t)
                           Right y -> pPrint y
