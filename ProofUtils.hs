{-# LANGUAGE NoImplicitPrelude #-}

module ProofUtils where

import Prelude

import Expression
import Axioms
import Proof

import Data.Maybe
import Data.Map hiding (foldl)

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
{-
getNumberedProof :: ProofStatement -> [NumberedStatement]
getNumberedProof stmt = runST $ do
    table <- new :: ST s (HashTable s Expression Int)
    let dfs (Axiom expr) num = do
            exist <- lift $ lookup table expr
            if isNothing exist
                then lift (insert table expr num) >> return ([NumAxiom expr num], num + 1)
                else return ([], num)
        dfs (ModusPonens expr left right) num = do
            exist <- lift $ lookup table expr
            if isNothing exist then do
                (lList, num) <- dfs left num
                (rList, num) <- dfs right num
                lift $ insert table expr num
                lNum <- lift $ lookup table $ getExpression left
                rNum <- lift $ lookup table $ getExpression right
                return ([NumModusPonens expr (fromJust lNum) (fromJust rNum) num] ++ rList ++ lList, num + 1)
            else return ([], num)
    result <- runContT (dfs stmt 1) $ return . fst
    return $ reverse result
    -}

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
