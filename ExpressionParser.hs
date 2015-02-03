{-# LANGUAGE NoImplicitPrelude, TupleSections #-}

module ExpressionParser (parseTerm, parseFormula, parseProof, parseHeading, parseWhole, parseFromFile) where

import Prelude

import Data.Char (isDigit, isLower, isUpper, isSpace)
import Data.Maybe

import Control.Applicative ((<|>), some, many)
import Control.Monad
import Control.Monad.Trans.State

import qualified Data.ByteString.Char8 as B

import Expression

type Parser = StateT B.ByteString Maybe

allowChar :: (Char -> Bool) -> Parser Char
allowChar f = StateT $ \str -> if not $ B.null str
    then let Just res@(c, rem) = B.uncons str in if f c then return res else mzero
    else mzero

allowMany :: (Char -> Bool) -> Parser B.ByteString
allowMany f = StateT $ \str -> return $ B.span f str

char :: Char -> Parser ()
char = (>> return ()) . allowChar . (==)

lowercase :: Parser B.ByteString
lowercase = liftM2 B.cons (allowChar isLower) $ allowMany isDigit

uppercase :: Parser B.ByteString
uppercase = liftM2 B.cons (allowChar isUpper) $ allowMany isDigit

sepBy :: Parser a -> String -> Parser [a]
sepBy p s = p >>= \res -> (forM_ s char >> liftM (res:) (sepBy p s)) <|> return [res]

braces :: Parser a -> Parser a
braces p = char '(' >> liftM2 const p (char ')')

parseTerm :: Parser Function
parseTerm = parsePlus
    where
        parsePlus = liftM (foldl1 (+++)) $ parseMult `sepBy` "+"
        parseMult = liftM (foldl1 (***)) $ parseStroke `sepBy` "*"
        parseStroke = do
            arg <- parseFunc
            strokes <- liftM (foldl (.) id) $ many $ char '\'' >> return Stroke
            return $ strokes arg
        parseFunc = (lowercase >>= \name -> (liftM (Func name) $ braces $ parseTerm `sepBy` ",") <|> return (Var name)) <|> parseZero
        parseZero = (char '0' >> return zero) <|> braces parseTerm

parseFormula :: Parser Expression
parseFormula = parseImpl
    where
        parseImpl = liftM (foldr1 (-->)) $ parseOr `sepBy` "->"
        parseOr = liftM (foldl1 (|||)) $ parseAnd `sepBy` "|"
        parseAnd = liftM (foldl1 (&&&)) $ parseNot `sepBy` "&"
        parseNot = (char '!' >> liftM Not parseNot) <|> parseForall
        parseForall = (char '@' >> liftM2 Forall lowercase parseNot) <|> parseExist
        parseExist = (char '?' >> liftM2 Exist lowercase parseNot) <|> parsePredicate
        parsePredicate = (uppercase >>= \name -> (liftM (Predicate name) $ braces $ parseTerm `sepBy` ",") <|> return (Gap name)) <|> parseEqual
        parseEqual = (liftM2 Equal parseTerm $ char '=' >> parseTerm) <|> braces parseFormula

skipNewline :: B.ByteString -> [B.ByteString]
skipNewline = B.lines . fst . B.spanEnd isSpace

parseProof :: Parser [Expression]
parseProof = StateT $ liftM (, B.empty) . mapM (evalStateT parseFormula) . skipNewline

parseHeading :: Parser ([Expression], Expression)
parseHeading = liftM2 (,) ((parseFormula `sepBy` ",") <|> return []) $ char '|' >> char '-' >> parseFormula

parseWhole :: Parser (([Expression], Expression), [Expression])
parseWhole = StateT $ \str ->
    let head:tail = skipNewline str
    in (liftM (, B.empty)) $ liftM2 (,) (evalStateT parseHeading head) (mapM (evalStateT parseFormula) tail)

parseFromFile :: Parser a -> String -> IO a
parseFromFile parser name = liftM (fromJust . evalStateT parser) $ B.readFile name
