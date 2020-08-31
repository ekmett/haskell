{-# Language BlockArguments #-}
{-# Language Strict #-}
{-# Language ImportQualifiedPost #-}
{-# Language TupleSections #-}

-- |
-- Copyright :  (c) Edward Kmett 2020, András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Source.Parser where

import Control.Monad (guard)
import Data.Char
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Data.String 
import Data.Void (Void)
import Icit
import Names
import Source.Term
import Prelude hiding (pi)
import Text.Megaparsec
import Text.Megaparsec.Char qualified as C
import Text.Megaparsec.Char.Lexer qualified as L

underscore :: SourceName
underscore = fromString "_"
{-# NOINLINE underscore #-}

-- TODO: carry a small interning table to get better sharing on ShortText names?
type Parser = Parsec Void String

loc :: Parser Term -> Parser Term
loc p = Loc <$> getSourcePos <*> p

whitespace :: Parser ()
whitespace = L.space C.space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme whitespace

symbol :: String -> Parser String
symbol s = lexeme (C.string s)

char :: Char -> Parser Char
char c = lexeme (C.char c)

parens, braces :: Parser a -> Parser a
parens p = char '(' *> p <* char ')'
braces p = char '{' *> p <* char '}'

arr :: Parser String
arr = symbol "→" <|> symbol "->"

bind :: Parser SourceName
bind = ident 
   <|> underscore <$ symbol "_"

colon, dot, lambda :: Parser String
colon = op ":"
dot = op "."
lambda = pure <$> char 'λ'
     <|> op "\\"

isKeyword :: String -> Bool
isKeyword x = x `elem` ["let","in","λ","U"]

ident :: Parser SourceName
ident = try do
  x <- takeWhile1P Nothing isAlphaNum <* whitespace
  fromString x <$ guard (not (isKeyword x))

kw :: String -> Parser String
kw s = try do
  x <- takeWhile1P Nothing isAlphaNum <* whitespace
  x <$ guard (x == s)

op :: String -> Parser String
op s = try do
  x <- takeWhile1P Nothing (`elem` ":!#$%&*+./<=>?@\\^|-~") <* whitespace
  x <$ guard (x == s)

-- TODO: use symbol parsing to find : rather than char

atom :: Parser Term
atom = loc (Var <$> ident
          <|> U <$ kw "U"
          <|> Hole <$ kw "_"
       ) <|> parens term

arg :: Parser (Icit, Term)
arg = (Implicit,) <$> braces term
  <|> (Explicit,) <$> parens term

spine :: Parser Term
spine = foldl' (\t (i, u) -> App i t u) <$> atom <*> many arg

lam :: Parser Term
lam = go <$ lambda <*> some binder <* dot <*> term where
  binder :: Parser (SourceName, Maybe Term, Icit)
  binder = ((,Nothing,Explicit) <$> bind)
    <|> parens ((,,Explicit) <$> bind <*> optional (colon *> term))
    <|> braces ((,,Implicit) <$> bind <*> optional (colon *> term))
  go xs t = foldr (\(x, a, ni) r -> Lam x a ni r) t xs

let_ :: Parser Term
let_ = go <$ symbol "let" <*> ident <*> optional (colon *> term)
          <* char '=' <*> term <* symbol "in" <*> term where
  go x ann t u = Let x (fromMaybe Hole ann) t u

pi :: Parser Term
pi = go <$> try (some binder) <* arr <*> term
 <|> Pi underscore Explicit <$> spine <* arr <*> term where
  go dom cod = foldr (\(xs, a, i) t -> foldr (\x -> Pi x i a) t xs) cod dom
  binder = braces ((,,Implicit) <$> some bind <*> ((colon *> term) <|> pure Hole))
       <|> parens ((,,Explicit) <$> some bind <* colon <*> term)
   
term :: Parser Term
term = loc (lam <|> let_ <|> pi)

src :: Parser Term
src = whitespace *> term <* eof
