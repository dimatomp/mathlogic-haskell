{-# LANGUAGE NoImplicitPrelude #-}

import Prelude

import Data.List
import Data.Char
import Data.Maybe
import Data.ByteString.Char8 (unpack)

import System.Environment

import Control.Monad.State

import ExpressionParser
import Proof
import Axioms
import ProofGeneration
import ProofUtils

main = do
    [fin, fout] <- getArgs
    inputData <- parseFromFile parseFormula fin
    let output = evalStateT (proveStmt inputData) $ initBuilder $ basicAxioms ++ [classicAxiom]
    case output of
        Right proof -> writeFile fout $ concatMap (++ "\n") $ map show $ getNumberedProof proof
        Left _ -> let Just list = traceExpr inputData
                      output = map (\(str, val) -> unpack str ++ "=" ++ if val then "И" else "Л") list
                  in writeFile fout $ "Высказывание ложно при " ++ intercalate ", " output ++ "\n"
