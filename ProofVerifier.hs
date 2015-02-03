import Data.List hiding (null)

import System.Environment

import Control.Monad

import ExpressionParser
import Proof
import Axioms
import ProofUtils

main = do
    argList <- getArgs
    if not $ null argList
        then do let fin = head argList
                inputData <- parseFromFile parseProof fin
                let Right proof = flip evalProof (initBuilder $ basicAxioms ++ [classicAxiom]) $ forM inputData tryTell
                forM_ (getLoggedProof proof) print
        else do name <- getProgName
                putStrLn $ "Использование: " ++ name ++ " <имя входного файла>"
                putStrLn $ "Поддерживаются файлы конечного размера (не /dev/stdin)"
