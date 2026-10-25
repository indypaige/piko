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
  = TyApp Ty Ty
  | TyCon Text
  | TyVar Text
  deriving ( Show
           , Ord
           , Eq
           )

infixr 9 :->
pattern (:->) a b = TyApp (TyApp (TyCon "->") a) b

pattern TyTup ts <- (tupleArgs -> Just ts)
  where
    TyTup ts = foldl TyApp (TyCon "Tup") ts

tupleArgs = f []
  where
    f args (TyApp f' x)   = f (x : args) f'
    f args (TyCon "Tup") = Just args
    f _    _             = Nothing

pattern TyBin     = TyCon "Bin"
pattern TyStr     = TyCon "Str"
pattern TyDec     = TyCon "Dec"
pattern TyChr     = TyCon "Chr"
pattern TyNum     = TyCon "Num"
pattern TyNil     = TyCon "Nil"
pattern TySym     = TyCon "Nil"

pattern TyIO a    = TyApp (TyCon "IO") a
pattern TyLst a   = TyApp (TyCon "Lst") a

instance Plated Ty where
  plate f (TyApp x y) = TyApp <$> f x <*> f y
  plate _ x           = pure x

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
  = UnknownTypeConstructor Text
  | KindMismatch Kind Kind
  | InfiniteKind Text Kind
  | Undefined Span Text
  | Unbound Span Text
  | Infinite Text Ty
  | Mismatch Ty Ty
  | UndefinedMain
  | DuplicateMain
  deriving Show

data Fn x = Fn Span (Maybe (Span, Ty)) Text (Exp x)

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
builtinSchemes = Map.fromList [ ("+", f n3)
                              , ("-", f n3)
                              , ("*", f n3)
                              , ("/", f n3)
                              , (".+", f d3)
                              , (".-", f d3)
                              , (".*", f d3)
                              , ("./", f d3)
                              , ("pure", Set.singleton "a" :&: TyVar "a" :-> TyIO (TyVar "a"))
                              , (">>=", Set.fromList ["a", "b"] :&: TyIO (TyVar "a") :-> (TyVar "a" :-> TyIO (TyVar "b")) :-> TyIO (TyVar "b"))
                              , (">>", Set.fromList ["a", "b"] :&: TyIO (TyVar "a") :-> TyIO (TyVar "b") :-> TyIO (TyVar "b"))
                              , ("putStrLn", f $ TyStr :-> TyIO TyNil)
                              , ("strFromChr", f $ TyChr :-> TyStr)
                              , ("strFromNum", f $ TyNum :-> TyStr)
                              , ("strFromDec", f $ TyNum :-> TyStr)
                              , ("strFromBin", f $ TyBin :-> TyStr)
                              , ("strFromSym", f $ TySym :-> TyStr)
                              , ("strFromNil", f $ TyNil :-> TyStr)
                              ]
  where
    f m = mempty :&: m
    n3  = TyNum :-> TyNum :-> TyNum
    d3  = TyDec :-> TyDec :-> TyDec

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
