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
    (fin:_) <- getArgs
    inputData <- parseFromFile parseProof fin
    let Right proof = flip evalProof (initBuilder $ basicAxioms ++ [classicAxiom]) $ forM inputData tryTell
    forM_ (getLoggedProof proof) print
