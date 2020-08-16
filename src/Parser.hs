
module Parser where

import Data.Maybe
import Text.Parsec
import Data.List (find)
import qualified Text.Parsec.Token as Tok
import qualified Text.Parsec.Expr as Ex
import Data.Functor.Identity (Identity)
import DepTypes

type Parser = Parsec String [Term]

reservedNames = [
  "type",
  "value",
  "def"] 
reservedOps = [
  ":",
  "\\",
  "\n",
  "match",
  "with",
  "|",
  "->",
  "=>",
  "=",
  "."]

langDef :: Tok.LanguageDef [Term]
langDef  = Tok.LanguageDef
  {
    Tok.commentStart = ""
  , Tok.commentEnd = ""
  , Tok.commentLine = ""
  , Tok.nestedComments = False 
  , Tok.identStart = letter 
  , Tok.identLetter = alphaNum 
  , Tok.opStart         = oneOf ""
  , Tok.opLetter        = oneOf ""
  , Tok.reservedNames   = reservedNames
  , Tok.reservedOpNames = reservedOps
  , Tok.caseSensitive   = True
  }

lexer :: Tok.TokenParser [Term]
lexer = Tok.makeTokenParser langDef

parens :: Parser a -> Parser a
parens = Tok.parens lexer

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

semiSep :: Parser a -> Parser [a]
semiSep = Tok.semiSep lexer

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer

symbol :: String -> Parser String
symbol s = Tok.symbol lexer s

{-|
prefixOp :: String -> (a -> a) -> Ex.Operator String () Identity a
prefixOp s f = Ex.Prefix (reservedOp s >> return f)
prefixOp s f = Ex.Prefix (reservedOp s >> return f)
-}

ident :: Parser String
ident = Tok.identifier lexer


-- DECLARATION PARSERS
-- Parse Values 
funcTypeParser :: Parser Term
funcTypeParser = do 
  val <- identParser
  reservedOp "->"
  rest <- typeParser
  return (Func val rest)

identParser :: Parser Term 
identParser = do 
  name <- ident
  vars <- getState
  ty <- (if name == "Type0" then return Type0 else
    case findNamed name vars of
    Nothing -> return (Var name) -- # TODO: decide what's right: fail ("Type " <> name <> " not yet declared")
    Just t -> return t)
  return ty

-- helper to search for whether a type has been declared
{-|
findType :: String -> [Term] -> Maybe Term 
findType _ [] = Nothing 
findType s (x : xs) = case x of
  Value v t -> if s == v then (Just $ Value v t) else findType s xs
  _ -> findType s xs
-}
typeParser :: Parser Term 
typeParser = do
  (try funcTypeParser) <|> identParser

valueParser :: Parser Term 
valueParser = do
  (reserved "value" <|> reserved "type")
  name <- ident 
  ty <- option Type0 ( do 
    reservedOp ":"
    typeParser)
  return (Value name ty)

namedDecParser :: Parser Term 
namedDecParser = do
  reserved "def"
  name <- ident
  reserved "="
  expr <- exprParser
  return (Named name expr)

-- EXPRESSION PARSERS

-- Parse abstractions
paramParser :: Parser (String, Term) 
paramParser = do 
  parens (do
    name <- ident 
    reservedOp ":"
    ty <- typeParser
    return (name, ty))

absParser :: Parser Term 
absParser = try(do 
  reservedOp "\\"
  param <- paramParser
  reservedOp "."
  expr <- exprParser
  return (Abs param expr))

-- Parse applications
appParser :: Parser Term 
appParser = try (do 
  t1 <- parens (try namedOrValParser
    <|> exprParser)
  t2 <- exprParser
  return (App t1 t2))


-- Parse Matches
matchParser :: Parser Term 
matchParser = try (do
  reservedOp "match"
  matchee <- exprParser 
  reservedOp "with"
  cases <- many $ try (do
    reservedOp "|"
    lt <- exprParser 
    reservedOp "->"
    rt <- exprParser 
    return (lt, rt))
  return (Match matchee cases))

-- basic named/var parsers
namedOrValParser :: Parser Term 
namedOrValParser = try (do
  name <- ident
  terms <- getState
  term <- (case findNamed name terms of
    Just t -> return t
    Nothing -> fail $ "Function " <> name <> " doesn't exist")
  return term)

varParser :: Parser Term 
varParser = try(do 
  name <- ident
  return (Var name))

-- General expression parser
exprParser :: Parser Term 
exprParser = choice [
      appParser
    , absParser 
    , matchParser
    , namedOrValParser
    , varParser
    , decParse]

-- Parse declarations
decParse :: Parser Term
decParse = do
  dec <- valueParser
    <|> namedDecParser
  modifyState ((:) dec)
  return dec

allDecParse :: Parser [Term]
allDecParse = do
  t <- many (decParse <|> do
    many (char '\n')
    decParse)
  return t

finalParse :: Parser Term 
finalParse = do
  allDecParse 
  many (char '\n')
  exprParser

testParser s = runParser exprParser [] "" s

parseAll :: String -> Either ParseError [Term]
parseAll s = runParser allDecParse [] "" s

parseFromFile :: FilePath -> IO (Either ParseError [Term])
parseFromFile fpath = do 
  input <- readFile fpath 
  return (parseAll input)

parseFinalExp :: String -> Either ParseError Term
parseFinalExp s = runParser finalParse [] "" s

parseExpFromFile :: FilePath -> IO (Either ParseError Term)
parseExpFromFile fpath = do 
  input <- readFile fpath 
  return (parseFinalExp input)

-- debug playground
parse1 :: Parser Term 
parse1 = do 
  reservedOp "match"
  reservedOp "with"
  reservedOp "|"
  varParser
  reservedOp "->"
  varParser

runParse1 s = runParser parse1 [] "" s

-- # TODO check no duplicates

{-|
expr :: Parser Term
expr = Ex.buildExpressionParser table factor

factor :: Parser Term
factor =
      true
  <|> false
  <|> zero
  <|> ifthen
  <|> parens expr

contents :: Parser a -> Parser a
contents p = do
  Tok.whiteSpace lexer
  r <- p
  eof
  return r

  -}



-- helper to find a term named such
findNamed :: String -> [Term] -> Maybe Term 
findNamed s arr = listToMaybe $ mapMaybe (\t -> case t of
  Named name t -> if name == s then Just (Named name t) else Nothing
  Value v t -> if s == v then (Just $ Value v t) else Nothing
  _ -> Nothing) arr