{-# LANGUAGE NoImplicitPrelude #-}

import Prelude

import Data.List
import Data.Char
import Data.Maybe

import System.Environment

import Control.Monad
import Control.Monad.Trans.State

import Text.Parsec.ByteString

import ExpressionParser
import Proof
import Axioms
import ProofGeneration
import ProofUtils

main = do
    [fin, fout] <- getArgs
    Right inputData <- parseFromFile parseSimpleFormula fin
    let output = evalStateT (proveStmt inputData) $ initBuilder $ basicAxioms ++ [classicAxiom]
    case output of
        Right proof -> writeFile fout $ concatMap (++ "\n") $ map show $ getNumberedProof proof
        Left _ -> let Just list = traceExpr inputData
                      output = map (\(str, val) -> str ++ "=" ++ if val then "И" else "Л") list
                  in writeFile fout $ "Высказывание ложно при " ++ intercalate ", " output ++ "\n"
