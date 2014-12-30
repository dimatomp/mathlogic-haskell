{-# LANGUAGE NoImplicitPrelude #-}

module ProofUtils where

import Prelude hiding (lookup)

import Expression hiding (getNumber)
import Axioms
import Proof

import Data.Maybe

import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans
import Control.Monad.Trans.Cont

import Data.HashTable.ST.Basic

data NumberedStatement = NumAxiom Expression Int
                       | NumModusPonens Expression Int Int Int

getNumber (NumAxiom _ num) = num
getNumber (NumModusPonens _ _ _ num) = num

showPref expr num = "(" ++ show num ++ ") " ++ show expr ++ " "

instance Show NumberedStatement where
    show (NumAxiom expr num) = showPref expr num ++ "(Сх. акс. " ++ show (fromJust $ getClassicAxiom expr) ++ ")"
    show (NumModusPonens expr l r num) = showPref expr num ++ "(M.P. " ++ show l ++ ", " ++ show r ++ ")"

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
