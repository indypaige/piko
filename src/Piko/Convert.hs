module Piko.Convert where

import Effectful.Internal.Effect (type (++))
import Effectful.State.Static.Local
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Piko.Ast as Ast
import Effectful.Reader.Static
import Effectful.Error.Static
import Data.Text (Text)
import Data.Traversable
import Piko.Ast (X(..))
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad
import Data.Foldable
import Control.Lens
import GHC.TypeLits
import Piko.Reduce
import Data.Maybe
import Data.List
import Effectful
import Data.Kind
import Data.Void
import Data.Int

type family (!~) (a :: k) (b :: k) :: Constraint where
  (!~) a a = TypeError ('Text "ne")
  (!~) a b = ()

class b !~ c => Convert (a :: X -> Type) b c where
  type Es a b c :: [Effect]

  convert     :: a b -> Eff (Es a b c) (a c)

  convertMany :: [a b] -> Eff (Es a b c) [a c]
  convertMany = traverse convert

instance ( Convert a Parse Typed
         , Convert a Typed Build
         , Subset (Es a Parse Typed) (Es a Parse Build)
         , Subset (Es a Typed Build) (Es a Parse Build)
         ) => Convert a Parse Build where
  type Es a Parse Build = Es a Parse Typed ++ Es a Typed Build

  convert = (inject . convert @a @Typed @Build)
        <=< (inject . convert @a @Parse @Typed)

  convertMany = (inject . convertMany @a @Typed @Build)
        <=< (inject . convertMany @a @Parse @Typed)

instance ( Convert a Parse Infer
         , Convert a Infer Typed
         , Subset (Es a Parse Infer) (Es a Parse Typed)
         , Subset (Es a Infer Typed) (Es a Parse Typed)
         ) => Convert a Parse Typed where
  type Es a Parse Typed = Es a Parse Infer ++ Es a Infer Typed

  convert = (inject . convert @a @Infer @Typed)
        <=< (inject . convert @a @Parse @Infer)

  convertMany = (inject . convertMany @a @Infer @Typed)
        <=< (inject . convertMany @a @Parse @Infer)

instance Convert Ast.Lit Infer Typed where
  type Es Ast.Lit Infer Typed = '[]

  convert (Ast.LitNum x n) = pure $ Ast.LitNum (x, Ast.TyNum) n
  convert (Ast.LitDec x d) = pure $ Ast.LitDec (x, Ast.TyDec) d
  convert (Ast.LitStr x s) = pure $ Ast.LitStr (x, Ast.TyStr) s
  convert (Ast.LitChr x c) = pure $ Ast.LitChr (x, Ast.TyChr) c
  convert (Ast.LitBin x b) = pure $ Ast.LitBin (x, Ast.TyBin) b
  convert (Ast.LitNil x)   = pure $ Ast.LitNil (x, Ast.TyNil)
  convert (Ast.LitExt x)   = pure $ absurd x

instance Convert Ast.Lit Parse Infer where
  type Es Ast.Lit Parse Infer = '[]

  convert (Ast.LitNum x n) = pure $ Ast.LitNum x n
  convert (Ast.LitDec x d) = pure $ Ast.LitDec x d
  convert (Ast.LitStr x s) = pure $ Ast.LitStr x s
  convert (Ast.LitChr x c) = pure $ Ast.LitChr x c
  convert (Ast.LitBin x b) = pure $ Ast.LitBin x b
  convert (Ast.LitNil x)   = pure $ Ast.LitNil x
  convert (Ast.LitExt x)   = pure $ absurd x

instance Convert Ast.Lit Typed Build where
  type Es Ast.Lit Typed Build = '[]

  convert (Ast.LitNum x n) = pure $ Ast.LitNum x n
  convert (Ast.LitDec x d) = pure $ Ast.LitDec x d
  convert (Ast.LitStr x s) = pure $ Ast.LitStr x s
  convert (Ast.LitChr x c) = pure $ Ast.LitChr x c
  convert (Ast.LitBin x b) = pure $ Ast.LitBin x b
  convert (Ast.LitNil x)   = pure $ Ast.LitNil x
  convert (Ast.LitExt x)   = pure $ absurd x

instance Convert Ast.Pat Parse Infer where
  type Es Ast.Pat Parse Infer = '[Reader Int]

  convert (Ast.PatVar (a, b)) = Ast.PatVar . (a,b,) <$> ask

  convert (Ast.PatLit x a)    = Ast.PatLit x <$> inject (convert a)

  convert (Ast.PatExt x)      = pure $ absurd x

  convert pat
    | Ast.PatLst x a <- pat   = Ast.PatLst x <$> conv a
    | Ast.PatTup x a <- pat   = Ast.PatTup x <$> conv a
        where
          cont t f s = snd <$> mapAccumM f s t

          conv a = ask >>= cont a f
            where
              f s = fmap (s+1,) . local (const (s :: Int)) . convert


instance Convert Ast.Pat Infer Typed where
  type Es Ast.Pat Infer Typed = '[]

  convert (Ast.PatLst x a) = Ast.PatLst x <$> traverse convert a
  convert (Ast.PatTup x a) = Ast.PatTup x <$> traverse convert a
  convert (Ast.PatLit x a) = Ast.PatLit x <$> convert a

  convert (Ast.PatVar x)   = pure $ Ast.PatVar x
  convert (Ast.PatExt x)   = pure $ absurd x

instance Convert Ast.Pat Typed Build where
  type Es Ast.Pat Typed Build = '[]

  convert (Ast.PatLst x a) = Ast.PatLst x <$> traverse convert a
  convert (Ast.PatTup x a) = Ast.PatTup x <$> traverse convert a
  convert (Ast.PatLit x a) = Ast.PatLit x <$> convert a

  convert (Ast.PatVar x)   = pure $ Ast.PatVar x
  convert (Ast.PatExt x)   = pure $ absurd x

instance Convert Ast.Fn Parse Infer where
  type Es Ast.Fn Parse Infer = Es Ast.Exp Parse Infer

  convert (Ast.Fn s sig n expr) = Ast.Fn s sig n <$> convert expr

instance Convert Ast.Exp Parse Infer where
  type Es Ast.Exp Parse Infer = '[Reader [(Text, Int)]]

  convert (Ast.ExpCnd s x y z) = Ast.ExpCnd s <$> convert x <*> convert y <*> convert z

  convert (Ast.ExpLst s x)     = Ast.ExpLst s <$> traverse convert x

  convert (Ast.ExpTup s x)     = Ast.ExpTup s <$> traverse convert x

  convert (Ast.ExpLit s l)     = Ast.ExpLit s <$> inject (convert l)

  convert (Ast.ExpLet s p x y) = do
    p' <- inject $ convert p & runReader 0
    x' <- convert x
    y' <- local (Ast.offset p' ++) (convert y)
    pure $ Ast.ExpLet s p' x' y'

  convert (Ast.ExpApp s f x)   = Ast.ExpApp s <$> inject (convert f)
                                              <*> inject (convert x)

  convert (Ast.ExpAbs s p x)    = do

    p' <- inject $ convert p & runReader 0
    x' <- local (Ast.offset p' ++) (convert x)
    pure $ Ast.ExpAbs s p' x'

  convert (Ast.ExpVar (s, b))   = g . l <$> ask
    where
      f (x, _)   = x == b

      l m        = do
        idx  <- findIndex f m
        idx' <- lookup b m
        pure (idx, idx')

      g Nothing  = Ast.ExpExt (s, b)
      g (Just x) = Ast.ExpVar (s, b, x)
