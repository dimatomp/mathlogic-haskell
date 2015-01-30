{-# LANGUAGE NoImplicitPrelude #-}

import Prelude hiding (readFile, null)

import Data.List hiding (null)

import System.Environment

import Control.Monad

import ExpressionParser
import Proof
import Axioms
import ProofUtils

main = do
    [fin, fout] <- getArgs
    inputData <- parseFromFile parseProof fin
    let Right proof = flip evalProof (initBuilder $ basicAxioms ++ [classicAxiom]) $ forM inputData tryTell
    writeFile fout $ concatMap (++ "\n") $ map show $ getLoggedProof proof
