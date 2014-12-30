{-# LANGUAGE NoImplicitPrelude #-}

import Prelude hiding (readFile, dropWhile)

import Data.List hiding (null, dropWhile)
import Data.Char
import Data.ByteString.Char8 (readFile, dropWhile, unpack)
import Data.Maybe

import System.Environment

import Control.Monad
import Control.Monad.ST

import ExpressionParser
import Proof
import ProofGeneration
import ProofUtils

main = do
    [fin, fout] <- getArgs
    inputData <- liftM (fromJust . parseExpr . dropWhile isSpace) $ readFile fin
    let output = runST $ getProof $ proveStmt inputData
    case output of
        Just proof -> writeFile fout $ concatMap (++ "\n") $ map show $ getNumberedProof proof
        Nothing -> let Just list = traceExpr inputData
                       output = map (\(str, val) -> unpack str ++ "=" ++ if val then "И" else "Л") list
                   in writeFile fout $ "Высказывание ложно при " ++ intercalate ", " output ++ "\n"
