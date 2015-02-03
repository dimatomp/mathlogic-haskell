import ExpressionParser
import Axioms
import Proof
import ProofUtils
import QuantifierLifting

import Control.Monad

import System.Environment

main = do
    argList <- getArgs
    if not $ null argList
        then do let fin = head argList
                expr <- parseFromFile parseFormula fin
                let Right result = evalProof (liftQuantifiers expr >> liftM last getRootLog) $ initBuilder $ basicAxioms ++ [classicAxiom] ++ predAxioms ++ [supposition expr]
                putStrLn $ show expr ++ "|-" ++ show (getExpression result)
                forM_ (getNumberedProof result) $ print . getContent
        else do name <- getProgName
                putStrLn $ "Использование: " ++ name ++ " <имя входного файла>"
                putStrLn $ "Поддерживаются файлы конечного размера (не /dev/stdin)"
