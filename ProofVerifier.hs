{-# LANGUAGE NoImplicitPrelude #-}

import Prelude hiding (readFile, lines, null)

import Data.List hiding (lines, null)
import Data.Char
import Data.ByteString.Char8 hiding (last, writeFile, map, intercalate, filter)
import Data.Maybe

import System.Environment

import Control.Monad
import Control.Monad.ST

import Expression
import ExpressionParser
import Proof

buildProof :: [Expression] -> String
buildProof exprs = runST $ do
    builder <- newBuilder
    mapM_ (nextSt builder) exprs
    liftM (intercalate "\n" . map show) $ getFixedProof builder exprs

main = do
    [fin, fout] <- getArgs
    inputData <- liftM (map (fromJust . parseExpr) . filter (not . null) . splitWith isSpace) $ readFile fin
    writeFile fout $ (buildProof inputData) ++ "\n"
