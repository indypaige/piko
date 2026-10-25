module Piko.Pretty where

import qualified Data.Text as Text
import qualified Piko.Ast as Ast
import Data.Text (Text)


prettyTy :: Ast.Ty -> Text
prettyTy ty =
  case ty of
    Ast.TyVar _ name -> name

    Ast.TyCon _ name -> name

    Ast.TyApp _ (Ast.TyApp _ (Ast.TyCon _ "->") lhs) rhs ->
      prettyArrow lhs rhs

    Ast.TyApp _ f x ->
      prettyApplication f x

prettyArrow :: Ast.Ty -> Ast.Ty -> Text
prettyArrow lhs rhs =
  prettyArrowLhs lhs <> " -> " <> prettyTy rhs
  where
    prettyArrowLhs t =
      case t of
        Ast.TyApp _ (Ast.TyApp _ (Ast.TyCon _ "->") _) _ ->
          "(" <> prettyTy t <> ")"
        _ ->
          prettyTy t

prettyApplication :: Ast.Ty -> Ast.Ty -> Text
prettyApplication f x =
  prettyFunction f <> " " <> prettyArgument x
  where
    prettyFunction t =
      case t of
        Ast.TyApp {} -> "(" <> prettyTy t <> ")"
        _            -> prettyTy t

    prettyArgument t =
      case t of
        Ast.TyApp {} -> "(" <> prettyTy t <> ")"
        _            -> prettyTy t
