
module Parser where

import Data.Maybe
import Text.Parsec
import Text.Parsec.Prim
import Data.List (find)
import qualified Text.Parsec.Token as Tok
import qualified Text.Parsec.Expr as Ex
import Data.Functor.Identity (Identity)
import DepTypes

type Parser = Parsec String (Maybe ContextElement, [Identifier])


reservedNames = [
  "type",
  "value",
  "rec",
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

langDef :: Tok.LanguageDef (Maybe ContextElement, [Identifier])
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

lexer :: Tok.TokenParser (Maybe ContextElement, [Identifier])
lexer = Tok.makeTokenParser langDef

parens :: Parser a -> Parser a
parens = Tok.parens lexer

braces :: Parser a -> Parser a
braces = Tok.braces lexer

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

semiSep :: Parser a -> Parser [a]
semiSep = Tok.semiSep lexer

reservedOp :: String -> Parser ()
reservedOp = Tok.reservedOp lexer

symbol :: String -> Parser String
symbol s = Tok.symbol lexer s

-- parse wrapper to check type after parsing a term 
-- # TODO: make sure recursive type definition matches actual type
checkTypeParse :: Parser Term -> Parser Term 
checkTypeParse p = do
  pos <- getPosition
  e <- p
  (ce, arr) <- getState
  (case checkType (fromMaybe [] (fmap (\e -> e : []) ce)) e of 
    Nothing -> error $ "Check type failed " <> (show pos) <> (show arr)
    Just _ -> return e)

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
  val <- braces (
    try ( -- optional naming of function parameter
      paramParser) <|> (do 
        expr <- exprParser
        return ("", expr)))
  reservedOp "->"
  rest <- exprParser
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

-- # TODO: remove weird application paranthesis thing

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

valueParserHelper :: Parser (String, Term)
valueParserHelper = do
  (reserved "value" <|> reserved "type")
  name <- ident 
  ty <- option Type0 ( do 
    reservedOp ":"
    exprParser)
  return (name, ty)

valueParser :: Parser Term 
valueParser = try (do
  (name, ty) <- valueParserHelper
  return (Value name ty))

valueDecParser :: Parser Identifier
valueDecParser = do
  (name, ty) <- valueParserHelper
  return (Named name (Value name ty))

namedDecParser :: Parser Identifier 
namedDecParser = do
  reserved "def"
  name <- ident
  reserved "="
  expr <- exprParser
  return (Named name expr)

recursiveDefParser = do
  reserved "rec"
  name <- ident 
  reserved ":"
  ty <- exprParser 
  modifyState (\(_, arr) -> (Just $ Elem name ty, arr)) -- add this context element to state for check type purposes
  reserved "="
  expr <- exprParser 
  return (Named name expr)



-- EXPRESSION PARSERS

-- Parse abstractions
paramParser :: Parser (String, Term) 
paramParser = parens (do
    name <- ident 
    reservedOp ":"
    ty <- exprParser
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
  t1 <- parens (exprParser)
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

type0Parser :: Parser Term 
type0Parser = try(do
  symbol "Type0"
  return Type0)

varParser :: Parser Term 
varParser = try(do 
  name <- ident
  return (Var name))

-- General expression parser
exprParser :: Parser Term 
exprParser = choice [
      type0Parser
    , appParser
    , absParser 
    , matchParser
    , namedOrValParser
    , valueParser
    , funcTypeParser
    , varParser]
  

-- Parse declarations
decParse :: Parser Term
decParse = do
  dec <- valueDecParser
    <|> namedDecParser
    <|> recursiveDefParser
  modifyState (\(ce, arr) -> (ce, (Named (name dec) (eval [] $ term dec) : arr))) -- evaluating
  checkTypeParse (return (term dec)) -- check type before... 
  return (term dec)

allDecParse :: Parser ()
allDecParse = do 
  many decParse
  return ()

finalParse :: Parser Term 
finalParse = do
  allDecParse 
  many (char '\n')
  expr <- checkTypeParse exprParser
  (_, vars) <- getState
  return $ eval vars expr


testParser s = runParser exprParser (Nothing, []) "" s


parseFinalExp :: String -> Either ParseError Term
parseFinalExp s = runParser finalParse (Nothing, []) "" s

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

runParse1 s = runParser parse1 (Nothing, []) "" s

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
findNamed :: String -> (Maybe ContextElement, [Identifier]) -> Maybe Term 
findNamed s (_, arr) = listToMaybe $ mapMaybe (\(Named name t) -> if name == s then Just t else Nothing) arr