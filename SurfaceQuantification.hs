import ExpressionParser
import Axioms
import Proof
import QuantifierLifting

import Control.Monad

import System.Environment

main = do
    (fin:_) <- getArgs
    expr <- parseFromFile parseFormula fin
    let Right result = evalProof (liftQuantifiers expr) $ initBuilder $ basicAxioms ++ [classicAxiom] ++ predAxioms ++ [supposition expr]
    putStrLn $ show expr ++ "|-" ++ show (last result)
    forM_ result print
