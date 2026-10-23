module Piko.Parse where

import qualified Text.Megaparsec.Char.Lexer as Lexer
import qualified Control.Monad.State.Lazy as Lazy
import Control.Monad.Trans.Class
import qualified Piko.Ast as Ast
import Text.Megaparsec.Char
import Prelude hiding (exp)
import Text.Show.Pretty
import Piko.Ast (X(..))
import Data.Text (Text)
import Text.Megaparsec

import Control.Monad
import Control.Lens
import Data.Void

type Power = Int

data Ctx = Ctx
  { _power :: Power
  , _binds :: [(Text, (Power, Power))]
  }
emptyCtx :: Ctx
emptyCtx = Ctx 0 Ast.builtinOperators

makeLenses ''Ctx

type Parser = ParsecT Void Text (Lazy.State Ctx)

withBp :: Lazy.MonadState Ctx m => Int -> m a -> m a
withBp i m = do
  x <- use power
  power .= i
  r <- m
  power .= x
  pure r

symbol :: Text -> Parser Text
symbol = Lexer.symbol hspace

parens, square :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")
square = between (symbol "[") (symbol "]")

spanned' :: Parser a -> Parser ((Ast.Span -> a -> b) -> b)
spanned' m = do
  (s, a) <- spanned m
  pure $ \f -> f s a

spanned :: Parser a -> Parser (Ast.Span, a)
spanned m = do
  lo <- getOffset
  xy <- m 
  hi <- getOffset
  pure $ (Ast.Span lo hi, xy)

symbols :: String
symbols = [ '!', '#', '$', '%', '&', '*'
          , '+', '.', '/', '>', '<', '='
          , '?', '@', '\\','^', '|', '-'
          , '~'
          ]

symbolsC :: String
symbolsC = ':':symbols

consym :: Parser Text
consym = fst <$> match m
  where
    m = char ':' >> many (oneOf symbolsC)

conid :: Parser Text
conid = fst <$> match m
  where
    m = upperChar >> many f
    f = msum [ alphaNumChar
             , char '\''
             , char '_'
             ]

varid :: Parser Text
varid = do
  x <- fst <$> match m

  if x `elem` Ast.keywords
    then empty
    else pure x
  where
    m = (letterChar <|> f) >> many (alphaNumChar <|> f)
    f = char '_'

varsym :: Parser Text
varsym = fst <$> match m
  where
    m = oneOf symbols >> many (oneOf symbolsC)

lit :: Parser (Ast.Lit Parse)
lit = msum [ bin
           , try dec
           , num
           , str
           , chr
           ]
  where
    str = spanned' (char '"' >> manyTill Lexer.charLiteral (char '"')) ?? Ast.LitStr
    chr = spanned' (char '\'' *> Lexer.charLiteral <* char '\'')       ?? Ast.LitChr
    num = spanned' (Lexer.signed hspace Lexer.decimal)                 ?? Ast.LitNum
    dec = spanned' (Lexer.signed hspace Lexer.float)                   ?? Ast.LitDec
    bin = spanned' b                                                   ?? Ast.LitBin
      where
        b = (True <$ "true") <|> (False <$ "false")

dot, comma :: Parser Text
comma = symbol ","
dot   = symbol "."

pat :: Parser (Ast.Pat Parse)
pat = msum [ var
           , lst
           , tup
           , lit'
           ]
  where
    lit' = spanned' lit                          ?? Ast.PatLit
    lst  = spanned' (square (pat `sepBy` comma)) ?? Ast.PatLst
    tup  = spanned' (parens (pat `sepBy` comma)) ?? Ast.PatTup
    var  = Ast.PatVar <$> spanned varid

exp :: Parser (Ast.Exp Parse)
exp = m
  where
    m = do
      lhs <- app
      f lhs
        where
          f lhs = do
            sym <- optional $ try $ lookAhead (hspace *> varsym)
            bps <- use binds

            case sym >>= (`lookup` bps) of
              Nothing     -> pure lhs
              Just (l, r) -> do
                min <- use power
                if l < min
                  then pure lhs
                  else do
                    hspace
                    mid <- spanned varsym
                    rhs <- withBp r (hspace *> exp)

                    let s  = Ast.spanOf lhs <> Ast.spanOf rhs
                        s' = Ast.spanOf lhs <> fst mid
                        f' = Ast.ExpApp s' (Ast.ExpVar mid) lhs

                    f (Ast.ExpApp s f' rhs)

    lst  = spanned' (square (exp `sepBy` comma)) ?? Ast.ExpLst
    tup  = spanned' (parens (exp `sepBy` comma)) ?? Ast.ExpTup

    lit' = spanned' lit ?? Ast.ExpLit
    abs  = spanned' ((,) <$> pat <* dot <*> exp) ?? (uncurry . Ast.ExpAbs)
    var  = Ast.ExpVar <$> spanned (varid <|> try (parens varsym))

    let' = do
      (s, _) <- spanned "let"
      hspace
      b <- pat
      hspace
      "="
      hspace
      e <- exp
      hspace
      "in"
      hspace
      (s', n) <- spanned exp
      pure $ Ast.ExpLet (s <> s') b e n

    cnd  = do
      (s, _) <- spanned "if"
      hspace
      c <- exp
      hspace
      "then"
      hspace
      t <- exp
      hspace
      "else"
      hspace
      (s', f) <- spanned exp
      pure $ Ast.ExpCnd (s <> s') c t f

    atm  = msum [ try abs
                , lit'
                , try cnd
                , try let'
                , var
                , lst
                , try (parens (withBp 0 exp))
                , tup
                ]

    app = do
      f <- spanned atm

      x <- many $ try $ spanned $ do
        hspace
        notFollowedBy (oneOf ['+', '-'])
        atm

      let y = foldl (\(s, a) (s', b) ->
                       let s'' = s <> s'
                       in (s'', Ast.ExpApp s'' a b)) f x

      pure $ snd y

bindingPower :: Parser ()
bindingPower = do
  "infix"
  hspace
  sym <- varsym
  hspace
  lBp <- Lexer.decimal
  hspace
  rBp <- Lexer.decimal
  binds %= ((sym, (lBp, rBp)):)

test :: Show a => Parser a -> Text -> IO ()
test m t = case Lazy.evalState (runParserT (m <* eof) "test.piko" t) emptyCtx of
             Left x -> putStr (errorBundlePretty x)
             Right x -> pPrint x
