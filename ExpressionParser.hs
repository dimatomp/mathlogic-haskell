{-# LANGUAGE NoImplicitPrelude, FlexibleContexts, NoMonomorphismRestriction #-}

module ExpressionParser where

import Prelude

import Data.List

import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Token
import Text.Parsec.Expr

import Control.Monad

import Expression

import Debug.Trace
--trace _ = id

lexemeLower = liftM2 (:) lower $ many digit

lexemeUpper = liftM2 (:) upper $ many digit

languageDef = defaultDef { whiteSpace = endOfLine >> return () }
    where
        defaultDef = makeTokenParser $ LanguageDef {
            commentStart = "",
            commentEnd = "",
            commentLine = "",
            nestedComments = True,
            identStart = parserZero,
            identLetter = parserZero,
            opStart = oneOf "-|&!@?+*'",
            opLetter = oneOf ">-",
            reservedNames = ["0"],
            reservedOpNames = ["+", "*", "'", "=", "->", "|", "&", "!", "@", "?", "|-"],
            caseSensitive = True
        }

mReservedOp = reservedOp languageDef
mReserved = reserved languageDef
mParens = parens languageDef
mCommaSep = commaSep languageDef
mCommaSep1 = commaSep1 languageDef
mLexeme = lexeme languageDef

parseTerm :: Stream s m Char => ParsecT s u m Function
parseTerm = trace "parseTerm" $ buildExpressionParser table termStroke
    where
        term = (lexemeLower >>= \str -> (trace "function" $ liftM (Func str) $ mParens $ mCommaSep1 parseTerm) <|> trace "variable" (return (Var str)))
           <|> (try (mReserved "0") >> trace "zero" (return Zero))
           <|> trace "term parens" (mParens parseTerm)
        termStroke = do
            before <- term
            howMuch <- liftM (foldl (.) id) $ many $ (try (mReservedOp "'") >> return Stroke)
            return $ howMuch before
        table = [ [Infix (mReservedOp "+" >> return Plus) AssocLeft]
                , [Infix (mReservedOp "*" >> return Mult) AssocLeft]
                ]

parseSimpleFormula :: Stream s m Char => ParsecT s u m Expression
parseSimpleFormula = trace "parseSimpleFormula" $ buildExpressionParser table term
    where
        term = (try (mReservedOp "!") >> trace "not" (liftM Not term))
           <|> trace "variable" (liftM Gap $ try lexemeUpper)
           <|> trace "formula parens" (mParens parseSimpleFormula)
        table = [ [Infix (mReservedOp "->" >> trace "implication" (return (-->))) AssocRight]
                , [Infix (mReservedOp "|" >> trace "or" (return (|||))) AssocLeft]
                , [Infix (mReservedOp "&" >> trace "and" (return (&&&))) AssocLeft]
                ]

parseFormula :: Stream s m Char => ParsecT s u m Expression
parseFormula = trace "parseFormula" $ buildExpressionParser table term
    where
        term = (try (mReservedOp "!") >> liftM Not term)
           <|> (try (mReservedOp "@") >> liftM2 Forall lexemeLower term)
           <|> (try (mReservedOp "?") >> liftM2 Exist lexemeLower term)
           <|> trace "predicate" (liftM2 Predicate lexemeUpper $ mParens $ mCommaSep1 parseTerm)
           <|> trace "equal" (liftM2 Equal (try parseTerm) $ char '=' >> parseTerm)
           <|> trace "formula parens" (mParens parseFormula)
        table = [ [Infix (mReservedOp "->" >> return (-->)) AssocRight]
                , [Infix (mReservedOp "|" >> return (|||)) AssocLeft]
                , [Infix (mReservedOp "&" >> return (&&&)) AssocLeft]
                ]

parseProof :: Stream s m Char => ParsecT s u m [Expression]
parseProof = many1 $ mLexeme parseFormula

parseSimpleProof :: Stream s m Char => ParsecT s u m [Expression]
parseSimpleProof = many1 $ liftM2 const parseSimpleFormula endOfLine

parseHeading :: Stream s m Char => ParsecT s u m ([Expression], Expression)
parseHeading = liftM2 (,) (mCommaSep parseFormula) $ mReservedOp "|-" >> parseFormula

parseSimpleHeading :: Stream s m Char => ParsecT s u m ([Expression], Expression)
parseSimpleHeading = liftM2 (,) (mCommaSep parseSimpleFormula) $ mReservedOp "|-" >> parseSimpleFormula

parseFile :: Stream s m Char => ParsecT s u m (([Expression], Expression), [Expression])
parseFile = liftM2 (,) (mLexeme parseHeading) parseProof

parseSimpleFile :: Stream s m Char => ParsecT s u m (([Expression], Expression), [Expression])
parseSimpleFile = liftM2 (,) (mLexeme parseSimpleHeading) parseSimpleProof
