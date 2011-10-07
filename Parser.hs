{-# OPTIONS -fwarn-unused-imports #-}
module Parser (runParser, parse, parsed, parser) where

import Base
import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.Reader
import Data.List(elemIndex)
import Text.Parsec hiding ((<|>), many, optional, parse, runParser)
import qualified Text.Parsec.Token as P

lexer :: P.GenTokenParser String () (Reader r)
lexer = P.makeTokenParser P.LanguageDef
           { P.commentStart = "{-"
           , P.commentEnd = "-}"
           , P.nestedComments = True
           , P.commentLine = "--"
           , P.identStart = letter
           , P.identLetter = alphaNum <|> char '_'
           , P.opStart = mzero
           , P.opLetter = mzero
           , P.reservedNames = ["forall"]
           , P.reservedOpNames = ["\\", ",", "->" , "'", "$", ":", "%", "_" ]
           , P.caseSensitive = False
           }
parens = P.parens lexer
ident = P.identifier lexer
reserved = P.reserved lexer
op = P.reservedOp lexer
nat = P.natural lexer

type DBContext = [Maybe String]

extend :: Maybe String -> DBContext -> DBContext
extend = (:)

find :: DBContext -> String -> Term s
find ctx id = maybe (Free id) Var (elemIndex (Just id) ctx)

type Parser t = ParsecT String () (Reader DBContext) t

freeVar :: Parser (Term Int)
freeVar = Free <$ op "'" <*> ident
boundVar :: Parser (Term Int)
boundVar = find <$> ask <*> ident
sortP :: Parser (Term Int)
sortP = Sort . fromInteger <$ op "%" <*> nat

type Binder = (Maybe String, Term Int)

boundName :: Parser (Maybe String)
boundName = (Just <$> ident) <|> (op "_" *> return Nothing)

openBinder :: Parser [Binder]
openBinder = zip <$> some boundName <*> (repeat <$ op ":" <*> parseTerm)
closedBinder :: Parser [Binder]
closedBinder = parens openBinder
closedBinders :: Parser [Binder]
closedBinders = closedBinder >>= \bind -> g bind <|> return bind
    where
      g :: [Binder] -> Parser [Binder]
      g = (uncurry (++) <$>) . extendP closedBinder

binders :: Parser [Binder]
binders = openBinder <|> closedBinders

extendP :: Parser t -> [Binder] -> Parser ([Binder], t)
extendP p bind = (,) bind <$> local (foldl (flip extend) $ map fst bind) p

applyBinders b = flip $ foldr (uncurry b)

abstraction :: Parser () -> (Maybe String -> Term Int -> Term Int -> Term Int) -> Parser (Term Int)
abstraction header binder = header >> uncurry (applyBinders binder) <$> (binders >>= extendP (op "," *> parseTerm))

application :: Parser (Term Int)
application = do t <- parseSimple
                 (optional (op "$") *> parseTerm >>= \s -> return $ Apply t s) <|> (op"->" *> local (extend Nothing) parseTerm >>= \s -> return $ Forall Nothing t s) <|>  return t

func :: Parser (Term Int)
func = Forall Nothing <$> parseSimple <* op"->" <*> local (extend Nothing) parseTerm

parseSimple :: Parser (Term Int)
parseSimple =     parens parseTerm
              <|> freeVar
              <|> boundVar
              <|> sortP
parseTerm :: Parser (Term Int)
parseTerm =     application
            <|> func
            <|> abstraction (reserved "forall") Forall
            <|> abstraction (op "\\") Lambda


runR name str = runReader (runPT parseTerm () name str) []
runParser :: Sort s => String -> String -> Either String (Term s)
runParser name str = (show +++ fromIntSort) $ runR name str

parser :: Sort s => String -> Either String (Term s)
parser str = runParser str str

parse :: Sort s => String -> IO (Term s)
parse = either fail return . parser

parsed :: Sort s => String -> Term s
parsed s = case parser s of { Right t -> t ; Left err -> error err }
