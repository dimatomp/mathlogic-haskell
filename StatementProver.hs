{-# LANGUAGE NoImplicitPrelude #-}

import Prelude

import Data.List
import Data.Char
import Data.Maybe
import Data.ByteString.Char8 (unpack)

import Control.Monad

import System.Environment

import ExpressionParser
import Proof
import Axioms
import ProofGeneration
import ProofUtils

main = do
    (fin:_) <- getArgs
    inputData <- parseFromFile parseFormula fin
    let output = evalProof (proveStmt inputData) $ initBuilder $ basicAxioms ++ [classicAxiom]
    case output of
        Right proof -> forM_ (getNumberedProof proof) print
        Left _ -> let Just list = traceExpr inputData
                      output = map (\(str, val) -> unpack str ++ "=" ++ if val then "И" else "Л") list
                  in putStrLn $ "Высказывание ложно при " ++ intercalate ", " output ++ "\n"
