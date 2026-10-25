module Piko.Reduce where

import qualified Piko.Ast as Ast
import Piko.Ast (X(..))
import Data.Int

shift :: Int -> Int -> Ast.Exp Typed -> Ast.Exp Typed
shift d c var@(Ast.ExpVar ((s, b, (n, k)), t))
  | n >= c                     = Ast.ExpVar ((s, b, (n + d, k)), t)
  | otherwise                  = var

shift d c (Ast.ExpLet a p x y) = Ast.ExpLet a p (shift d (c + l) x) (shift d (c + l) y)
  where
    l = Ast.arity p

shift d c (Ast.ExpCnd s x y z) = Ast.ExpCnd s (shift d c x) (shift d c y) (shift d c z)

shift d c (Ast.ExpAbs x p a)   = Ast.ExpAbs x p (shift d (c + l) a)
  where
    l = Ast.arity p

shift d c (Ast.ExpApp s f x)   = Ast.ExpApp s (shift d c f) (shift d c x)

shift d c (Ast.ExpLst x items) = Ast.ExpLst x $ shift d c <$> items

shift d c (Ast.ExpTup x items) = Ast.ExpTup x $ shift d c <$> items

shift d c x                    = x

subst :: Int
      -> Ast.Exp Typed
      -> Ast.Exp Typed
      -> Ast.Exp Typed

subst j s = f 0
  where
    f d e = g e
      where
        g (Ast.ExpLet a p x y)           = Ast.ExpLet a p (f d x) (f (d + l) y)
          where
            l = Ast.arity p

        g (Ast.ExpApp s' f' x)           = Ast.ExpApp s' (f d f') (f d x)

        g (Ast.ExpCnd s x y z)           = Ast.ExpCnd s (f d x) (f d y) (f d z)

        g (Ast.ExpAbs a p x)             = Ast.ExpAbs a p (f (d + l) x)
          where
            l = Ast.arity p

        g (Ast.ExpLst x items)           = Ast.ExpLst x $ f d <$> items

        g var@(Ast.ExpVar ((x, y, (k, o)), t))
          | k >= j + d  && k < j + d + o =
              let rel = o - 1 - (k - (j + d))
                  flt = Ast.flatten (shift d 0 s)
              in flt !! rel

          | k >= j + d + o               = Ast.ExpVar ((x, y, (k - o, o)), t)
          | otherwise                    = var

        g x                              = x

beta :: Ast.Pat Typed
     -> Ast.Exp Typed
     -> Ast.Exp Typed
     -> Ast.Exp Typed

beta p x y = shift (-l) 0 $ subst 0 (shift l 0 x) y
  where
    l = Ast.arity p

class Reduce a where
  reduce :: a Ast.Typed -> a Ast.Typed

instance Reduce Ast.Exp where
  reduce (Ast.ExpLet _ p x y) = reduce $ beta p (reduce x) y

  reduce (Ast.ExpApp a f x)   = case (reduce f, reduce x) of
                                (Ast.ExpAbs _ p f', x') -> reduce (beta p x' f')
                                (f', x')               -> Ast.ExpApp a f' x'

  reduce (Ast.ExpCnd s x y z) = case reduce x of
                                (Ast.ExpLit _ (Ast.LitBin _ True))  -> reduce y
                                (Ast.ExpLit _ (Ast.LitBin _ False)) -> reduce z
                                _                                   -> Ast.ExpCnd s (reduce x) (reduce y) (reduce z)

  reduce (Ast.ExpAbs a p x)   = Ast.ExpAbs a p $ reduce x

  reduce (Ast.ExpTup a items) = Ast.ExpTup a $ reduce <$> items

  reduce (Ast.ExpLst a items) = Ast.ExpLst a $ reduce <$> items

  reduce x                    = x

instance Reduce Ast.Fn where
  reduce = Ast.mapExp reduce

instance Reduce Ast.Item where
  reduce (Ast.ItemMain ex) = Ast.ItemMain (reduce ex)
  reduce (Ast.ItemFn   fn) = Ast.ItemFn (reduce fn)
