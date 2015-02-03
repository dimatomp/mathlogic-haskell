import ExpressionParser
import Axioms
import Proof
import ProofUtils
import QuantifierLifting

import Control.Monad

import System.Environment

main = do
    (fin:_) <- getArgs
    expr <- parseFromFile parseFormula fin
    let Right result = evalProof (liftQuantifiers expr >> liftM last getRootLog) $ initBuilder $ basicAxioms ++ [classicAxiom] ++ predAxioms ++ [supposition expr]
    putStrLn $ show expr ++ "|-" ++ show (getExpression result)
    forM_ (getNumberedProof result) $ print . getContent
