{-# LANGUAGE NoImplicitPrelude #-}

module ProofUtils where

import Prelude

import Expression
import Axioms
import Proof

import Data.Maybe
import Data.HashMap.Strict hiding (foldl)

import Control.Monad

data NumberedStatement = NumUnproved Expression Int
                       | NumAxiom Expression Int Int
                       | NumModusPonens Expression Int Int Int

getNumber (NumUnproved _ num) = num
getNumber (NumAxiom _ _ num) = num
getNumber (NumModusPonens _ _ _ num) = num

showPref expr num = "(" ++ show num ++ ") " ++ show expr ++ " "

instance Show NumberedStatement where
    show (NumUnproved expr num) = showPref expr num ++ "(Не доказано)"
    show (NumAxiom expr axiom num) = showPref expr num ++ "(Сх. акс. " ++ show axiom ++ ")"
    show (NumModusPonens expr l r num) = showPref expr num ++ "(M.P. " ++ show l ++ ", " ++ show r ++ ")"

getNumberedProof :: ProofStatement -> [NumberedStatement]
getNumberedProof stmt =
    let process (num, map, res) stmt = if getExpression stmt `member` map
            then (num, map, res)
            else case stmt of
                AxiomStatement expr axiom -> (num + 1, insert expr num map, NumAxiom expr axiom num : res)
                ModusPonens expr left right ->
                    let (nNum, nMap, nRes) = (`process` right) $ process (num, map, res) left
                        leftNum = nMap ! getExpression left
                        rightNum = nMap ! getExpression right
                    in (nNum + 1, insert expr nNum nMap, NumModusPonens expr leftNum rightNum nNum : nRes)
        (_, _, result) = process (1, empty, []) stmt
    in reverse result

getLoggedProof :: [Either Expression ProofStatement] -> [NumberedStatement]
getLoggedProof list =
    let process (num, map, res) (Left expr) = (num + 1, map, NumUnproved expr num : res)
        process (num, map, res) (Right (AxiomStatement expr axiom)) = (num + 1, insert expr num map, NumAxiom expr axiom num : res)
        process (num, map, res) (Right (ModusPonens expr left right)) =
            let leftNum = map ! getExpression left
                rightNum = map ! getExpression right
            in (num + 1, insert expr num map, NumModusPonens expr leftNum rightNum num : res)
        (_, _, result) = foldl process (1, empty, []) list
    in reverse result
