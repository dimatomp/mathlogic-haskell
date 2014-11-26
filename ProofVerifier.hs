{-# LANGUAGE NoImplicitPrelude #-}

import Prelude hiding (readFile, null)

import Data.List hiding (null)
import Data.Char
import Data.ByteString.Char8 (readFile, splitWith, null)
import Data.Maybe

import System.Environment

import Control.Monad

import ExpressionParser
import MonadProof

main = do
    [fin, fout] <- getArgs
    inputData <- liftM (map (fromJust . parseExpr) . filter (not . null) . splitWith isSpace) $ readFile fin
    let output = getFixed $ forM inputData tellEx
    writeFile fout $ (intercalate "\n" $ map show output) ++ "\n"
