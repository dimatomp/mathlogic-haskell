import Expression
import Axioms
import ExpressionParser
import Proof hiding (trace)

import Data.List
import Data.ByteString.Char8 (unpack)

import Control.Monad

import System.Environment

main = do
    (fin:_) <- getArgs
    ((supp, stmt), inputData) <- parseFromFile parseWhole fin
    let suppInit = if null supp then [] else init supp
        builder = initBuilder $ basicAxioms ++ [classicAxiom] ++ predAxioms ++ arithAxioms ++ map supposition suppInit
        sandbox = flip evalProof builder $ ((if null supp then id else assume $ last supp) $ forM_ inputData tellEx) >> getLog
        result = if null supp then stmt else last supp --> stmt
        prefix = "Вывод некорректен начиная с формулы номер "
    case sandbox of
        Left (num, Nothing) -> putStrLn $ prefix ++ show (num + 1)
        Left (num, Just (UnsafeForSubst f e s)) -> putStrLn $ prefix ++ show (num + 1) ++ ": терм " ++ show f ++ " не свободен для подстановки в формулу " ++ show e ++ " вместо переменной " ++ unpack s
        Left (num, Just (FreeOccurrence x e)) -> putStrLn $ prefix ++ show (num + 1) ++ ": переменная " ++ unpack x ++ " входит свободно в формулу " ++ show e
        Left (num, Just (BadRuleUsage x e)) -> putStrLn $ prefix ++ show (num + 1) ++ ": используется правило с квантором по переменной " ++ unpack x ++ ", входящей свободно в допущение " ++ show e
        Right list -> do
            putStrLn $ intercalate "," (map show suppInit) ++ "|-" ++ show result
            forM_ list print
