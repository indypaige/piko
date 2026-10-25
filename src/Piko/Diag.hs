module Piko.Diag where

import qualified Piko.Pretty as Pretty
import qualified Data.Text as Text
import qualified Piko.Ast as Ast
import Data.Text (Text)

import qualified Data.Text as Text
import Data.Text (Text)

sourceLine :: Int -> Text -> Text
sourceLine offset source = Text.takeWhile (/= '\n') (Text.drop start source)
  where
    before = Text.take offset source
    start = Text.length before - Text.length (Text.takeWhileEnd (/= '\n') before)

sourceColumn :: Int -> Text -> Int
sourceColumn offset source = Text.length (Text.takeWhileEnd (/= '\n') (Text.take offset source))

class Diag a where
  diag :: a -> Text -> Text

instance Diag Ast.Span where
    diag (Ast.Span lo hi) source =
        line
        <> "\n"
        <> Text.replicate column " "
        <> Text.replicate width "^"
      where
        line = sourceLine lo source
        column = sourceColumn lo source
        width = max 1 (min (hi - lo) (Text.length line - column))

instance Diag Ast.InferError where
  diag err source =
    case err of
      Ast.UnknownTypeConstructor sp name ->
        render sp ("Unknown type constructor: " <> name)

      Ast.Undefined sp name ->
        render sp ("Undefined variable: " <> name)

      Ast.Unbound sp name ->
        render sp ("Unbound name: " <> name)

      Ast.Infinite sp name t ->
        render sp ("Infinite type: " <> name <> " occurs in " <> Pretty.prettyTy t)

      Ast.Mismatch sp t1 t2 ->
        render sp
          ("Type mismatch: " <> Pretty.prettyTy t1 <> " <-> " <> Pretty.prettyTy t2)
      _ -> showText err
    where
      render sp message =
        message <> "\n" <> diag sp source

showText :: Show a => a -> Text
showText = Text.pack . show
