module Piko.Ast where

import Effectful.Internal.Effect (type (++))
import Effectful.State.Static.Local
import qualified Data.Map as Map
import qualified Data.Set as Set
import Effectful.Reader.Static
import Effectful.Error.Static
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

data X = Parse | Infer | Typed

type family XLitStr (x :: X)
type family XLitDec (x :: X)
type family XLitNum (x :: X)
type family XLitBin (x :: X)
type family XLitChr (x :: X)
type family XLitExt (x :: X)
type family XLitNil (x :: X)

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
type family XExpCnd (x :: X)
type family XLitSym (x :: X)

data Lit (x :: X)
  = LitStr (XLitStr x) String
  | LitDec (XLitDec x) Double
  | LitNum (XLitNum x) Int64
  | LitBin (XLitBin x) Bool
  | LitChr (XLitChr x) Char
  | LitSym (XLitSym x) Text
  | LitNil (XLitNil x)
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

flatten :: Exp x -> [Exp x]
flatten (ExpTup _ items) = items >>= flatten
flatten (ExpLst _ items) = items >>= flatten
flatten other                = [other]

arity :: Pat x -> Int
arity (PatTup _ l) = sum $ arity <$> l
arity (PatLst _ l) = sum $ arity <$> l
arity (PatVar _)   = 1
arity _            = 0

data Exp (x :: X)
  = ExpLet (XExpLet x) (Pat x) (Exp x) (Exp x)
  | ExpCnd (XExpCnd x) (Exp x) (Exp x) (Exp x)
  | ExpApp (XExpApp x) (Exp x) (Exp x)
  | ExpAbs (XExpAbs x) (Pat x) (Exp x)
  | ExpLst (XExpLst x) [Exp x]
  | ExpTup (XExpTup x) [Exp x]
  | ExpLit (XExpLit x) (Lit x)
  | ExpVar (XExpVar x)
  | ExpExt (XExpExt x)

data Ty
  = TyApp Span Ty Ty
  | TyCon Span Text
  | TyVar Span Text
  deriving ( Show
           , Ord
           )

instance Eq Ty where
  TyVar _ a == TyVar _ b = a == b
  TyCon _ a == TyCon _ b = a == b
  TyApp _ f x == TyApp _ f' x' = f == f' && x == x'
  _ == _ = False

spanOfTy :: Ty -> Span
spanOfTy (TyApp s _ _) = s
spanOfTy (TyCon s _)   = s
spanOfTy (TyVar s _)   = s

infixr 9 :->

pattern (:->) :: Ty -> Ty -> Ty
pattern a :-> b <- TyApp _ (TyApp _ (TyCon _ "->") a) b
  where
    a :-> b = TyApp mempty (TyApp mempty (TyCon mempty "->") a) b

pattern TyTup ts <- (tupleArgs -> Just ts)
  where
    TyTup ts = foldl (TyApp mempty) (TyCon mempty "Tup") ts

tupleArgs :: Ty -> Maybe [Ty]
tupleArgs = go []
  where
    go args (TyApp _ f x)  = go (x : args) f
    go args (TyCon _ "Tup") = Just args
    go _ _                  = Nothing

pattern TyBin <- TyCon _ "Bin" where TyBin = TyCon mempty "Bin"
pattern TyStr <- TyCon _ "Str" where TyStr = TyCon mempty "Str"
pattern TyDec <- TyCon _ "Dec" where TyDec = TyCon mempty "Dec"
pattern TyChr <- TyCon _ "Chr" where TyChr = TyCon mempty "Chr"
pattern TyNum <- TyCon _ "Num" where TyNum = TyCon mempty "Num"
pattern TyNil <- TyCon _ "Nil" where TyNil = TyCon mempty "Nil"
pattern TySym <- TyCon _ "Sym" where TySym = TyCon mempty "Sym"

pattern TyIO a <- TyApp _ (TyCon _ "IO") a
  where
    TyIO a = TyApp mempty (TyCon mempty "IO") a

pattern TyLst a <- TyApp _ (TyCon _ "Lst") a
  where
    TyLst a = TyApp mempty (TyCon mempty "Lst") a

instance Plated Ty where
  plate f (TyApp s x y) = TyApp s <$> f x <*> f y
  plate _ x             = pure x

type instance XExpVar Infer = (Span, Text, (Int, Int))

type instance XLitStr Typed = (XLitStr Infer, Ty)
type instance XLitDec Typed = (XLitDec Infer, Ty)
type instance XLitNum Typed = (XLitNum Infer, Ty)
type instance XLitBin Typed = (XLitBin Infer, Ty)
type instance XLitChr Typed = (XLitChr Infer, Ty)
type instance XLitNil Typed = (XLitNil Infer, Ty)
type instance XLitSym Typed = (XLitSym Infer, Ty)

type instance XExpVar Typed = (XExpVar Infer, Ty)
type instance XExpLst Typed = (XExpLst Infer, Ty)
type instance XExpTup Typed = (XExpTup Infer, Ty)
type instance XExpLit Typed = (XExpLit Infer, Ty)
type instance XExpAbs Typed = (XExpAbs Infer, Ty)
type instance XExpApp Typed = (XExpApp Infer, Ty)
type instance XExpExt Typed = (XExpExt Infer, Ty)
type instance XExpCnd Typed = (XExpCnd Infer, Ty)
type instance XPatVar Infer = (Span, Text, Int)
type instance XExpLet Typed = (Span, Ty)

type instance XLitExt Typed = XLitExt Infer
type instance XPatLst Typed = XPatLst Infer
type instance XPatTup Typed = XPatTup Infer
type instance XPatVar Typed = XPatVar Infer
type instance XPatLit Typed = XPatLit Infer
type instance XPatExt Typed = XPatExt Infer

type instance XLitStr Infer = XLitStr Parse
type instance XLitDec Infer = XLitDec Parse
type instance XLitNum Infer = XLitNum Parse
type instance XLitBin Infer = XLitBin Parse
type instance XLitChr Infer = XLitChr Parse
type instance XLitExt Infer = XLitExt Parse
type instance XLitNil Infer = XLitNil Parse
type instance XLitSym Infer = XLitSym Parse

type instance XPatLst Infer = XPatLst Parse
type instance XPatTup Infer = XPatTup Parse
type instance XPatLit Infer = XPatLit Parse
type instance XPatExt Infer = XPatExt Parse
 
type instance XExpLst Infer = XExpLst Parse
type instance XExpTup Infer = XExpTup Parse
type instance XExpLit Infer = XExpLit Parse
type instance XExpApp Infer = XExpApp Parse
type instance XExpCnd Infer = XExpCnd Parse

type instance XExpExt Infer = (Span, Text)
type instance XPatVar Parse = (Span, Text)
type instance XExpVar Parse = (Span, Text)

type instance XLitStr Parse = Span
type instance XLitDec Parse = Span
type instance XLitNum Parse = Span
type instance XLitBin Parse = Span
type instance XLitChr Parse = Span
type instance XLitNil Parse = Span
type instance XLitSym Parse = Span
type instance XLitExt Parse = Void

type instance XPatLst Parse = Span
type instance XPatTup Parse = Span
type instance XPatLit Parse = Span
type instance XPatExt Parse = Void

type instance XExpCnd Parse = Span
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
  spanOf (ExpLst s _)     = s
  spanOf (ExpTup s _)     = s
  spanOf (ExpExt s)       = absurd s

instance SpanOf (Exp Typed) where
  spanOf (ExpVar ((s, _, _), _)) = s
  spanOf (ExpApp (s, _) _ _)     = s
  spanOf (ExpAbs (s, _) _ _)     = s
  spanOf (ExpLet (s, _) _ _ _)   = s
  spanOf (ExpLit (s, _) _)       = s
  spanOf (ExpLst (s, _) _)       = s
  spanOf (ExpTup (s, _) _)       = s
  spanOf (ExpCnd (s, _) _ _ _)   = s
  spanOf (ExpExt ((s, _), _))    = s

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
    ExpCnd (_, t) _ _ _ -> t
    ExpLst (_, t) _     -> t
    ExpTup (_, t) _     -> t

data InferError
  = UnknownTypeConstructor Span Text
  | KindMismatch Kind Kind
  | InfiniteKind Text Kind
  | Infinite Span Text Ty
  | Undefined Span Text
  | Mismatch Span Ty Ty
  | Unbound Span Text
  | UndefinedMain
  | DuplicateMain
  deriving Show

data Fn x = Fn Span (Maybe (Span, Ty)) Text (Exp x)

instance SpanOf (Fn x) where
  spanOf (Fn s _ _ _) = s

mapExp :: (Exp x -> Exp y) -> Fn x -> Fn y
mapExp f (Fn s sig n e) = Fn s sig n (f e)

deriving instance Show (Fn Parse)
deriving instance Show (Fn Typed)
deriving instance Show (Fn Infer)

builtinInfix :: [(Text, (Int, Int))]
builtinInfix = concat [ bp ["+", "-", ".+", ".-"] 05 06
                      , bp ["*", "/", ".*", "./"] 07 08
                      , bp [">>=", ">>"]          14 13
                      , bp ["."]                  10 09
                      ]
  where
    bp xs l r = (, (l, r)) <$> xs

builtinPrefix :: [(Text, ((), Int))]
builtinPrefix = concat [ ]
  where
    bp xs p = (, ((), p)) <$> xs

builtinPostfix :: [(Text, (Int, ()))]
builtinPostfix = concat [ ]
  where
    bp xs p = (, (p, ())) <$> xs

builtinSchemes :: Map Text Scheme
builtinSchemes = Map.fromList
  [ ("+", f n3)
  , ("-", f n3)
  , ("*", f n3)
  , ("/", f n3)
  , (".+", f d3)
  , (".-", f d3)
  , (".*", f d3)
  , ("./", f d3)
  , ("pure", Set.singleton "a" :&: arrow a (io a))
  , (">>=", Set.fromList ["a", "b"] :&:
       arrow (io a) (arrow (arrow a (io b)) (io b)))
  , (">>", Set.fromList ["a", "b"] :&:
       arrow (io a) (arrow (io b) (io b)))
  , ("putStrLn", f $ arrow str (io nil))
  , ("strFromChr", f $ arrow chr str)
  , ("strFromNum", f $ arrow num str)
  , ("strFromDec", f $ arrow dec str)
  , ("strFromBin", f $ arrow bin str)
  , ("strFromSym", f $ arrow sym str)
  , ("strFromNil", f $ arrow nil str)
  ]
  where
    s = mempty

    con = TyCon s
    var = TyVar s
    app = TyApp s

    arrow x y = app (app (con "->") x) y
    io x = app (con "IO") x

    a = var "a"
    b = var "b"

    num = con "Num"
    dec = con "Dec"
    bin = con "Bin"
    chr = con "Chr"
    str = con "Str"
    nil = con "Nil"
    sym = con "Sym"

    n3 = arrow num (arrow num num)
    d3 = arrow dec (arrow dec dec)

    f m = mempty :&: m

keywords :: [Text]
keywords = [ "then"
           , "else"
           , "let"
           , "if"
           , "in"
           ]

data Item x
  = ItemMain (Exp x)
  | ItemFn   (Fn x)

deriving instance Show (Item Parse)
deriving instance Show (Item Typed)
deriving instance Show (Item Infer)

type Module x = [Item x]

isMain :: Item x -> Bool
isMain (ItemMain _) = True
isMain (ItemFn   _) = False

splitMain :: Error InferError :> es => Module x -> Eff es (Item x, Module x)
splitMain mod = case partition isMain mod of
                  ([], _)    -> throwError UndefinedMain
                  (x:[], xs) -> pure (x, xs)
                  _          -> throwError DuplicateMain

refs :: Exp Infer -> Set Text
refs (ExpLet _ _ x y) = refs x `Set.union` refs y
refs (ExpExt (_, n))  = Set.singleton n
refs (ExpApp _ x y)   = refs x `Set.union` refs y
refs (ExpLst _ xs)    = Set.unions $ refs <$> xs
refs (ExpTup _ xs)    = Set.unions $ refs <$> xs
refs (ExpAbs _ _ x)   = refs x
refs _                = mempty
