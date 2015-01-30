{-# LANGUAGE NoImplicitPrelude #-}

import Prelude hiding (readFile, null)

import Data.List hiding (null)

import System.Environment

import Control.Monad

import ExpressionParser
import Proof
import ProofUtils
import Axioms

main = do
    [fin, fout] <- getArgs
    ((supp, _), inputData) <- parseFromFile parseWhole fin
    let assumeAll = foldr (\s f -> assume s . f) id supp
        Right [Root _ _ _ log] = flip execProof (initBuilder $ basicAxioms ++ [classicAxiom]) $ assumeAll $ forM_ inputData tellEx
    writeFile fout $ concatMap (++ "\n") $ map show $ getLoggedProof $ map Right $ reverse log
