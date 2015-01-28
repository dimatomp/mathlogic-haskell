{-# LANGUAGE NoImplicitPrelude, FlexibleContexts #-}

module ExpressionParser  where

import Prelude

import Data.List

import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Combinator

import Control.Monad
import Control.Monad.Identity

import Expression

lexemeLower :: Stream s m Char => ParsecT s u m String
lexemeLower = liftM2 (:) lower $ many digit

lexemeUpper :: Stream s m Char => ParsecT s u m String
lexemeUpper = liftM2 (:) upper $ many digit

braces :: Stream s m Char => ParsecT s u m a -> ParsecT s u m a
braces = between (char '(') (char ')')

parseTerm :: Stream s m Char => ParsecT s u m Function
parseTerm = parsePlus
    where
        parsePlus = liftM (foldl1 (+++)) $ parseMult `sepBy1` char '+'
        parseMult = liftM (foldl1 (***)) $ parseFunc `sepBy1` char '*'
        parseFunc = (liftM2 Func lexemeLower $ braces $ parseTerm `sepBy` char ',') <|> parseStroke
        parseStroke = liftM Stroke (liftM2 const parseFunc $ char '\'') <|> parseVar
        parseVar = (char '0' >> return Zero) <|> liftM Var lexemeLower <|> braces parseTerm

parseFormula :: Stream s m Char => ParsecT s u m Expression
parseFormula = parseImpl
    where
        parseImpl = liftM (foldr1 (-->)) $ parseOr `sepBy1` string "->"
        parseOr = liftM (foldl1 (|||)) $ parseAnd `sepBy1` char '|'
        parseAnd = liftM (foldl1 (&&&)) $ parseNot `sepBy1` char '&'
        parseNot = (liftM Not $ char '!' >> parseNot) <|> parseForall
        parseForall = (char '@' >> liftM2 Forall lexemeLower parseForall) <|> parseExist
        parseExist = (char '?' >> liftM2 Exist lexemeLower parseForall) <|> parsePredicate
        parsePredicate = (lexemeUpper >>= \lex -> (liftM (Predicate lex) $ braces $ parseTerm `sepBy` char ',') <|> (return $ Gap lex)) <|> braces parseFormula

parseProof :: Stream s m Char => ParsecT s u m [Expression]
parseProof = many1 $ liftM2 const parseFormula endOfLine

parseHeading :: Stream s m Char => ParsecT s u m ([Expression], Expression)
parseHeading = liftM2 (,) (parseFormula `sepBy` char ',') $ string "|-" >> parseFormula

parseFile :: Stream s m Char => ParsecT s u m (([Expression], Expression), [Expression])
parseFile = liftM2 (,) (liftM2 const parseHeading endOfLine) parseProof
