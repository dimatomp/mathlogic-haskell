{-# LANGUAGE NoImplicitPrelude #-}

import Prelude hiding (readFile, null)

import Data.List hiding (null)
import Data.Char
import Data.ByteString.Char8 (readFile, splitWith, null)
import Data.Maybe

import System.Environment

import Control.Monad
import Control.Monad.ST

import ExpressionParser
import Proof
import ProofUtils

main = do
    [fin, fout] <- getArgs
    inputData <- liftM (map (fromJust . parseExpr) . filter (not . null) . splitWith isSpace) $ readFile fin
    let output = getLoggedProof $ runST $ getLog $ liftM last $ forM inputData tellEx
    writeFile fout $ concatMap (++ "\n") $ map show output
