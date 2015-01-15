{-# LANGUAGE NoImplicitPrelude #-}

module ExpressionParser  where

import Prelude hiding (head, tail, null, span)

import Data.Char
import Data.ByteString.Char8 hiding (foldr, foldl, map)

import Control.Monad.State

import Expression

type Parser = StateT ByteString Maybe

allowChars :: (Char -> Bool) -> Parser String
allowChars pred = StateT $ \str ->
    let (pref, suf) = span pred str
    in if null pref
        then mzero
        else return (unpack pref, suf)

char c = StateT $ \str -> if null str then mzero else
    let f = head str
        s = tail str
    in if c == f
        then return (f, s)
        else mzero

once :: Parser a -> Parser [a]

many :: Parser a -> Parser [a]
many prs = once prs `mplus` return []

once prs = do
    first <- prs
    rem <- many prs
    return (first:rem)

parseImpl :: Parser Expression

brackets = do
    char '('
    res <- parseImpl
    char ')'
    return res

varName = (fmap Var $ allowChars isAlphaNum) `mplus` brackets

parseNot = (do
    char '!'
    par <- parseNot
    return $ Not par) `mplus` varName

parseAnd = do
    left <- parseNot
    (do
        right <- once $ char '&' >> parseNot
        return $ foldl (&&&) left right
        ) `mplus` return left

parseOr = do
    left <- parseAnd
    (do
        right <- once $ char '|' >> parseAnd
        return $ foldl (|||) left right
        ) `mplus` return left

parseImpl = do
    left <- parseOr
    (do
        right <- char '-' >> char '>' >> parseImpl
        return $ left --> right
        ) `mplus` return left

parseExpr :: ByteString -> Maybe Expression
parseExpr s = fmap fst $ runStateT parseImpl s

heading :: Parser ([Expression], Expression)
heading = do
    fst <- parseImpl
    rem <- many $ char ',' >> parseImpl
    char '|' >> char '-'
    res <- parseImpl
    return (fst:rem, res)

parseHead :: ByteString -> Maybe ([Expression], Expression)
parseHead s = fmap fst $ runStateT heading s
