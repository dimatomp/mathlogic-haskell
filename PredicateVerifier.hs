import Expression
import Axioms
import ExpressionParser
import Proof hiding (trace)

import Data.List
import Data.ByteString.Char8 (unpack)

import Control.Monad

import System.Environment

sandbox :: [Expression] -> [Expression] -> Either (Int, ErrorReport) [Expression]
sandbox supp text = flip evalProof (initBuilder $ basicAxioms ++ [classicAxiom] ++ predAxioms ++ arithAxioms) $ do
    forM_ supp addAssumption
    forM_ text tellEx
    when (not $ null supp) remAssumption
    getLog

main = do
    [fin, fout] <- getArgs
    ((supp, stmt), inputData) <- parseFromFile parseWhole fin
    let prefix = "Вывод некорректен начиная с формулы номер "
        suppInit = if null supp then [] else init supp
        result = if null supp then stmt else last supp --> stmt
    writeFile fout $ (++ "\n") $ case sandbox supp inputData of
        Left (num, Nothing) -> prefix ++ show (num + 1)
        Left (num, Just (UnsafeForSubst f e s)) -> prefix ++ show (num + 1) ++ ": терм " ++ show f ++ " не свободен для подстановки в формулу " ++ show e ++ " вместо переменной " ++ unpack s
        Left (num, Just (FreeOccurrence x e)) -> prefix ++ show (num + 1) ++ ": переменная " ++ unpack x ++ " входит свободно в формулу " ++ show e
        Left (num, Just (BadRuleUsage x e)) -> prefix ++ show (num + 1) ++ ": используется правило с квантором по переменной " ++ unpack x ++ ", входящей свободно в допущение " ++ show e
        Right list -> intercalate "," (map show suppInit) ++ "|-" ++ show result ++ concatMap ('\n':) (map show list)
