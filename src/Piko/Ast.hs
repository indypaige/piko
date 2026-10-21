module Piko.Ast where

import Effectful.Internal.Effect (type (++))
import Effectful.State.Static.Local
import qualified Data.Map as Map
import qualified Data.Set as Set
import Effectful.Reader.Static
import Data.Text (Text)
import Data.Traversable
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad
import Data.Foldable
import Control.Lens
import GHC.TypeLits
import Data.Maybe
import Data.List
import Effectful
import Data.Kind
import Data.Void
import Data.Int

data Span = Span Int Int
  deriving ( Show
           , Ord
           , Eq
           )

instance Semigroup Span where
  Span l _ <> Span _ r = Span l r

instance Monoid Span where
  mempty = Span (-1) (-1)

data X = Parse | Infer | Typed | Inter

type family XLitStr (x :: X)
type family XLitDec (x :: X)
type family XLitNum (x :: X)
type family XLitBin (x :: X)
type family XLitChr (x :: X)
type family XLitExt (x :: X)

type family XPatLst (x :: X)
type family XPatTup (x :: X)
type family XPatVar (x :: X)
type family XPatLit (x :: X)
type family XPatExt (x :: X)

type family XExpLet (x :: X)
type family XExpLst (x :: X)
type family XExpTup (x :: X)
type family XExpVar (x :: X)
type family XExpLit (x :: X)
type family XExpAbs (x :: X)
type family XExpApp (x :: X)
type family XExpExt (x :: X)

data Lit (x :: X)
  = LitStr (XLitStr x) String
  | LitDec (XLitDec x) Double
  | LitNum (XLitNum x) Int64
  | LitBin (XLitBin x) Bool
  | LitChr (XLitChr x) Char
  | LitExt (XLitExt x)

data Pat (x :: X)
  = PatLst (XPatLst x) [Pat x]
  | PatTup (XPatTup x) [Pat x]
  | PatLit (XPatLit x) (Lit x)
  | PatVar (XPatVar x)
  | PatExt (XPatExt x)

offset :: Pat Infer -> [(Text, Int)]
offset (PatTup _ l)                  = l >>= offset
offset (PatLst _ l)                  = l >>= offset
offset (PatVar (_, b', x))           = [(b', x)]
offset (PatLit _ _)                  = mempty

flatten :: Exp Infer -> [Exp Infer]
flatten (ExpTup _ items) = items >>= flatten
flatten (ExpLst _ items) = items >>= flatten
flatten other                = [other]

arity :: Pat Infer -> Int
arity (PatTup _ l) = sum $ arity <$> l
arity (PatLst _ l) = sum $ arity <$> l
arity (PatVar _)   = 1
arity _            = 0

data Exp (x :: X)
  = ExpLet (XExpLet x) (Pat x) (Exp x) (Exp x)
  | ExpApp (XExpApp x) (Exp x) (Exp x)
  | ExpAbs (XExpAbs x) (Pat x) (Exp x)
  | ExpLst (XExpLst x) [Exp x]
  | ExpTup (XExpTup x) [Exp x]
  | ExpLit (XExpLit x) (Lit x)
  | ExpVar (XExpVar x)
  | ExpExt (XExpExt x)

data Ty
  = TyApp Ty Ty
  | TyCon Text
  | TyVar Text
  deriving ( Show
           , Ord
           , Eq
           )

pattern (:->) a b = TyApp (TyApp (TyCon "->") a) b

pattern TyTup ts <- (tupleArgs -> Just ts)
  where
    TyTup ts = foldl TyApp (TyCon "tup") ts

tupleArgs = f []
  where
    f args (TyApp f' x)   = f (x : args) f'
    f args (TyCon "tup") = Just args
    f _    _             = Nothing

pattern TyBin     = TyCon "bin"
pattern TyStr     = TyCon "str"
pattern TyDec     = TyCon "dec"
pattern TyChr     = TyCon "chr"
pattern TyNum     = TyCon "num"

pattern TyLst a   = TyApp (TyCon "lst") a

instance Plated Ty where
  plate f (TyApp x y) = TyApp <$> f x <*> f y
  plate _ x          = pure x

type instance XExpVar Infer = (Span, Text, (Int, Int))

type instance XLitStr Typed = (XLitStr Infer, Ty)
type instance XLitDec Typed = (XLitDec Infer, Ty)
type instance XLitNum Typed = (XLitNum Infer, Ty)
type instance XLitBin Typed = (XLitBin Infer, Ty)
type instance XLitChr Typed = (XLitChr Infer, Ty)

type instance XExpVar Typed = (XExpVar Infer, Ty)
type instance XExpLst Typed = (XExpLst Infer, Ty)
type instance XExpTup Typed = (XExpTup Infer, Ty)
type instance XExpLit Typed = (XExpLit Infer, Ty)
type instance XExpAbs Typed = (XExpAbs Infer, Ty)
type instance XExpApp Typed = (XExpApp Infer, Ty)
type instance XExpLet Typed = (Span, Ty)
type instance XExpExt Typed = (XExpExt Infer, Ty)

type instance XPatVar Infer = (Span, Text, Int)

type instance XLitExt Typed = XLitExt Infer
type instance XPatLst Typed = XPatLst Infer
type instance XPatTup Typed = XPatTup Infer
type instance XPatVar Typed = XPatVar Infer
type instance XPatLit Typed = XPatLit Infer
type instance XPatExt Typed = XPatExt Infer

type instance XLitStr Inter = XLitStr Typed
type instance XLitDec Inter = XLitDec Typed
type instance XLitNum Inter = XLitNum Typed
type instance XLitBin Inter = XLitBin Typed
type instance XLitChr Inter = XLitChr Typed
type instance XLitExt Inter = XLitExt Typed

type instance XPatLst Inter = XPatLst Typed
type instance XPatTup Inter = XPatTup Typed
type instance XPatVar Inter = XPatVar Typed
type instance XPatLit Inter = XPatLit Typed
type instance XPatExt Inter = XPatExt Typed

type instance XExpLst Inter = XExpLst Typed
type instance XExpTup Inter = XExpTup Typed
type instance XExpVar Inter = XExpVar Typed
type instance XExpLit Inter = XExpLit Typed
type instance XExpAbs Inter = XExpAbs Typed
type instance XExpApp Inter = XExpApp Typed
type instance XExpExt Inter = XExpExt Typed
type instance XExpLet Inter = XExpLet Typed

type instance XLitStr Infer = XLitStr Parse
type instance XLitDec Infer = XLitDec Parse
type instance XLitNum Infer = XLitNum Parse
type instance XLitBin Infer = XLitBin Parse
type instance XLitChr Infer = XLitChr Parse
type instance XLitExt Infer = XLitExt Parse

type instance XPatLst Infer = XPatLst Parse
type instance XPatTup Infer = XPatTup Parse
type instance XPatLit Infer = XPatLit Parse
type instance XPatExt Infer = XPatExt Parse
 
type instance XExpLst Infer = XExpLst Parse
type instance XExpTup Infer = XExpTup Parse
type instance XExpLit Infer = XExpLit Parse
type instance XExpApp Infer = XExpApp Parse

type instance XExpExt Infer = (Span, Text)
type instance XPatVar Parse = (Span, Text)
type instance XExpVar Parse = (Span, Text)

type instance XLitStr Parse = Span
type instance XLitDec Parse = Span
type instance XLitNum Parse = Span
type instance XLitBin Parse = Span
type instance XLitChr Parse = Span
type instance XLitExt Parse = Void

type instance XPatLst Parse = Span
type instance XPatTup Parse = Span
type instance XPatLit Parse = Span
type instance XPatExt Parse = Void

type instance XExpLst Parse = Span
type instance XExpTup Parse = Span
type instance XExpApp Parse = Span
type instance XExpLit Parse = Span
type instance XExpAbs Parse = Span
type instance XExpLet Parse = Span
type instance XExpExt Parse = Void

type instance XExpLet Infer = Span
type instance XExpAbs Infer = Span

deriving instance Show (Pat Parse)
deriving instance Show (Lit Parse)
deriving instance Show (Exp Parse)

deriving instance Ord (Pat Parse)
deriving instance Ord (Lit Parse)
deriving instance Ord (Exp Parse)

deriving instance Eq (Pat Parse)
deriving instance Eq (Lit Parse)
deriving instance Eq (Exp Parse)

deriving instance Show (Pat Infer)
deriving instance Show (Lit Infer)
deriving instance Show (Exp Infer)

deriving instance Ord (Pat Infer)
deriving instance Ord (Lit Infer)
deriving instance Ord (Exp Infer)

deriving instance Eq (Pat Infer)
deriving instance Eq (Lit Infer)
deriving instance Eq (Exp Infer)

deriving instance Show (Pat Typed)
deriving instance Show (Lit Typed)
deriving instance Show (Exp Typed)

deriving instance Ord (Pat Typed)
deriving instance Ord (Lit Typed)
deriving instance Ord (Exp Typed)

deriving instance Eq (Pat Typed)
deriving instance Eq (Lit Typed)
deriving instance Eq (Exp Typed)

deriving instance Show (Pat Inter)
deriving instance Show (Lit Inter)
deriving instance Show (Exp Inter)

deriving instance Ord (Pat Inter)
deriving instance Ord (Lit Inter)
deriving instance Ord (Exp Inter)

deriving instance Eq (Pat Inter)
deriving instance Eq (Lit Inter)
deriving instance Eq (Exp Inter)

infixl 8 :&:

data Scheme = Set Text :&: Ty

data Kind
  = KindType
  | KindVar Text
  | KindArr Kind Kind
  deriving ( Show
           , Ord
           , Eq
           )

class SpanOf a where
  spanOf :: a -> Span

instance SpanOf (Exp Parse) where
  spanOf (ExpVar (s, _))  = s
  spanOf (ExpApp s _ _)   = s
  spanOf (ExpAbs s _ _)   = s
  spanOf (ExpLet s _ _ _) = s
  spanOf (ExpLit s _)     = s
  spanOf (ExpExt s)       = absurd s

class TyOf a where
  tyOf :: a -> Ty

instance TyOf (Exp Typed) where
  tyOf = \case
    ExpVar (_, t)       -> t
    ExpApp (_, t) _ _   -> t
    ExpAbs (_, t) _ _   -> t
    ExpLet (_, t) _ _ _ -> t
    ExpLit (_, t) _     -> t
    ExpExt (_, t)       -> t

data InferError
  = UnknownTypeConstructor Text
  | KindMismatch Kind Kind
  | InfiniteKind Text Kind
  | Undefined Span Text
  | Unbound Span Text
  | Infinite Text Ty
  | Mismatch Ty Ty
  deriving Show

data Fn x = Fn
  { sig :: Maybe Ty
  , fun :: Exp x
  }
