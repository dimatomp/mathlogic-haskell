{-# LANGUAGE NoImplicitPrelude, FlexibleContexts #-}

module ExpressionParser where

import Prelude

import Data.List

import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Combinator

--import Debug.Trace

import Control.Monad

import Expression

trace _ = id

lexemeLower :: Stream s m Char => ParsecT s u m String
lexemeLower = liftM2 (:) lower $ many digit

lexemeUpper :: Stream s m Char => ParsecT s u m String
lexemeUpper = liftM2 (:) upper $ many digit

braces :: Stream s m Char => ParsecT s u m a -> ParsecT s u m a
braces = between (char '(') (char ')')

parseTerm :: Stream s m Char => ParsecT s u m Function
parseTerm = parsePlus
    where
        parsePlus = trace "parsePlus" $ liftM (foldl1 (+++)) $ parseMult `sepBy1` char '+'
        parseMult = trace "parseMult" $ liftM (foldl1 (***)) $ parseStroke `sepBy1` char '*'
        parseStroke = trace "parseStroke" $ do
            applyTo <- parseFunc
            howMuch <- liftM length $ many $ char '\''
            return $ iterate Stroke applyTo !! howMuch
        parseFunc = trace "parseFunc" $ (lexemeLower >>= \str -> (liftM (Func str) $ braces $ parseTerm `sepBy1` char ',') <|> return (Var str)) <|> parseZero
        parseZero = trace "parseZero" $ (char '0' >> return Zero) <|> try (braces parseTerm)

trySepBy1 p c = p >>= \fst -> try (c >> trySepBy1 p c >>= return . (fst:)) <|> return [fst]

parseSimpleFormula :: Stream s m Char => ParsecT s u m Expression
parseSimpleFormula = parseImpl
    where
        parseImpl = trace "parseImpl" $ liftM (foldr1 (-->)) $ parseOr `sepBy1` string "->"
        parseOr = trace "parseOr" $ liftM (foldl1 (|||)) $ parseAnd `trySepBy1` char '|'
        parseAnd = trace "parseAnd" $ liftM (foldl1 (&&&)) $ parseNot `sepBy1` char '&'
        parseNot = trace "parseNot" $ (liftM Not $ char '!' >> parseNot) <|> parseVar
        parseVar = trace "parseVar" $ liftM Gap lexemeUpper <|> braces parseSimpleFormula

parseFormula :: Stream s m Char => ParsecT s u m Expression
parseFormula = parseImpl
    where
        parseImpl = trace "parseImpl" $ liftM (foldr1 (-->)) $ parseOr `sepBy1` string "->"
        parseOr = trace "parseOr" $ liftM (foldl1 (|||)) $ parseAnd `trySepBy1` char '|'
        parseAnd = trace "parseAnd" $ liftM (foldl1 (&&&)) $ parseNot `sepBy1` char '&'
        parseNot = trace "parseNot" $ (liftM Not $ char '!' >> parseNot) <|> parseForall
        parseForall = trace "parseForall" $ (char '@' >> liftM2 Forall lexemeLower parseNot) <|> parseExist
        parseExist = trace "parseExist" $ (char '?' >> liftM2 Exist lexemeLower parseNot) <|> parsePredicate
        parsePredicate = trace "parsePredicate" $ (lexemeUpper >>= \lex -> (liftM (Predicate lex) $ braces $ parseTerm `sepBy1` char ',') <|> (return $ Gap lex)) <|> parseEqual
        parseEqual = trace "parseEqual" $ (liftM2 Equal parseTerm $ char '=' >> parseTerm) <|> braces parseFormula

parseProof :: Stream s m Char => ParsecT s u m [Expression]
parseProof = many1 $ liftM2 const parseFormula endOfLine

parseSimpleProof :: Stream s m Char => ParsecT s u m [Expression]
parseSimpleProof = many1 $ liftM2 const parseSimpleFormula endOfLine

parseHeading :: Stream s m Char => ParsecT s u m ([Expression], Expression)
parseHeading = liftM2 (,) (parseFormula `sepBy` char ',') $ string "|-" >> parseFormula

parseSimpleHeading :: Stream s m Char => ParsecT s u m ([Expression], Expression)
parseSimpleHeading = liftM2 (,) (parseSimpleFormula `sepBy` char ',') $ string "|-" >> parseSimpleFormula

parseFile :: Stream s m Char => ParsecT s u m (([Expression], Expression), [Expression])
parseFile = liftM2 (,) (liftM2 const parseHeading endOfLine) parseProof

parseSimpleFile :: Stream s m Char => ParsecT s u m (([Expression], Expression), [Expression])
parseSimpleFile = liftM2 (,) (liftM2 const parseSimpleHeading endOfLine) parseSimpleProof
