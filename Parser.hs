{-# LANGUAGE OverloadedStrings #-}
module Parser where

import Text.Megaparsec
import Text.Megaparsec.Char
import Data.Monoid ((<>))
import Core4

import Data.Void
import Data.Text hiding (length, map, foldl1, foldr1)

type Parser a = Parsec Void Text a

-- precedence levels
-- highest: @ 
-- lowest:  :

parser :: Parser E
parser = do
  space
  parseE1

parseE1 :: Parser E
parseE1 = parseCons 

parseCons :: Parser E
parseCons = do
  es <- sepBy1 parseE2 colon
  space
  case es of
    [e]   -> return e
    (_:_) -> return (foldr1 (\e1 e2 -> Ctor Cons [e1,e2]) es)

parseE2 :: Parser E
parseE2 = do
  es <- some parseE3
  space
  case es of
    [e]   -> return e
    (_:_) -> return (foldl1 (\e1 e2 -> Dtor App [e1,e2]) es)

colon :: Parser ()
colon = do
  char ':'
  space
  return ()

comma :: Parser ()
comma = do
  char ','
  space
  return ()

parseE3 :: Parser E
parseE3 =
  try parseUnit <|>
  try parseP <|>
  parseParens <|>
  parseAtom 'Z' Z <|>
  parseAtom 'T' T <|>
  parseAtom 'F' F <|>
  parseS <|>
  parseNil <|>
  parse1D "pr1" Pr1 <|>
  parse1D "pr2" Pr2 <|>
  parse3D "if" Ifte <|>
  parse3D "iter" Iter <|>
  parse3D "fold" Fold <|>
  parseLam <|>
  parseLetrec <|>
  parseVar

parseAtom :: Char -> H -> Parser E
parseAtom c h = do
  char c
  space
  return (Ctor h [])

parseParens :: Parser E
parseParens = do
  char '('
  space
  e <- parseE1
  char ')'
  space
  return e

parse1D :: Text -> D -> Parser E
parse1D prefix d = do
  string (prefix <> "(")
  space
  e <- parseE1
  char ')'
  space
  return (Dtor d [e])

parseUnit :: Parser E
parseUnit = do
  string "()"
  space
  return (Ctor Star [])

parseNil :: Parser E
parseNil = do
  string "[]"
  space
  return (Ctor Nil [])

parseLam :: Parser E
parseLam = do
  char '\\'
  space
  x <- variable
  space
  string "->"
  space
  body <- parseE1
  return (Lam (abstr x body))

parseLetrec :: Parser E
parseLetrec = do
  string "letrec["
  space
  eqns <- sepBy parseEquation comma
  space
  char ']'
  space1
  body <- parseE1
  let vars = map fst eqns
  let es = map snd eqns
  return (LetRec (length vars) (map (links vars) es) (links vars body))

parseVar :: Parser E
parseVar = do
  x <- variable
  space
  return (FV x)

variable :: Parser String
variable = do
  c <- lowerChar
  cs <- many alphaNumChar
  return (c:cs)

parseS :: Parser E
parseS = do
  string "S("
  space
  e <- parseE1
  char ')'
  space
  return (Ctor S [e])
  

parseP :: Parser E
parseP = do
  char '('
  space
  e1 <- parseE1
  char ','
  space
  e2 <- parseE1
  char ')'
  space
  return (Ctor P [e1,e2])

parse3D :: Text -> D -> Parser E
parse3D prefix d = do
  string (prefix <> "(")
  space
  e1 <- parseE1
  char ','
  space
  e2 <- parseE2
  char ','
  space
  e3 <- parseE3
  char ')'
  space
  return (Dtor d [e1,e2,e3])

parseEquation :: Parser (String,E)
parseEquation = do
  x <- variable
  space
  char '='
  space
  e <- parseE1
  return (x,e)
