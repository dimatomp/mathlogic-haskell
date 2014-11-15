{-# LANGUAGE NoImplicitPrelude #-}

module Proof where

import Prelude hiding (lookup)

import Data.HashTable.IO
import Data.Maybe
import Data.Sequence

import Control.Monad

import Expression
import Axioms

data ProofStatement = Unproved { getExpression :: Expression, getNum :: Maybe Int }
                    | Axiom { getExpression :: Expression, getNum :: Maybe Int }
                    | ModusPonens { getExpression :: Expression, getFrom :: ProofStatement, getImpl :: ProofStatement, getNum :: Maybe Int }

instance Show ProofStatement where
    show (Unproved expr Nothing) = show expr ++ " (Не доказано)"
    show (Unproved expr (Just num)) = "(" ++ show num ++ ") " ++ show (Unproved expr Nothing)
    show (Axiom expr Nothing) = show expr ++ " (Сх. акс. " ++ show (1 + (length $ takeWhile isNothing $ map (`matches` expr) classicAxioms)) ++ ")"
    show (Axiom expr (Just num)) = "(" ++ show num ++ ") " ++ show (Axiom expr Nothing)
    show (ModusPonens expr from impl Nothing) = show expr ++ " (M.P. " ++ unwrap from ++ ", " ++ unwrap impl ++ ")"
        where 
            unwrap stmt = case getNum stmt of
                Nothing  -> "?"
                Just num -> show num
    show (ModusPonens expr from impl (Just num)) = "(" ++ show num ++ ") " ++ show (ModusPonens expr from impl Nothing)

type HashMap k v = BasicHashTable k v

data ProofBuilder = Builder (HashMap Expression ProofStatement) 
                            (HashMap Expression [ProofStatement])
                            (Sequence ProofStatement)

newBuilder :: IO ProofBuilder
newBuilder = do
    proved <- new
    forMP <- new
    return $ Builder proved forMP

nextSt :: ProofBuilder -> Expression -> IO ()
nextSt (Builder proved forMP) expr = do
    alreadyProved <- lookup proved expr
    let isAxiom = if any (isJust . (`matches` expr)) classicAxioms
        then Just $ Axiom expr Nothing
        else Nothing
    firstSuccess <- liftM (listToMaybe . catMaybes) $ lookupOrEmpty forMP expr >>= mapM ((lookup proved) . getLeft . getExpression)
    modusPonens <- case firstSuccess of
        Nothing -> return Nothing
        Just fromPart -> do
            implPart <- lookup proved $ Implication (getExpression fromPart) expr
            return $ Just $ ModusPonens expr fromPart (fromJust implPart) Nothing
    let statement = fromMaybe (Unproved expr Nothing) $ alreadyProved `mplus` isAxiom `mplus` modusPonens 
    insert proved expr statement
    case expr of
        Implication l r -> do
            findRight <- lookupOrEmpty forMP r
            insert forMP r $ statement:findRight
        _               -> return ()
    where lookupOrEmpty t k = liftM (fromMaybe []) $ lookup t k

addProof :: ProofBuilder -> ProofStatement -> IO ()
addProof builder stmt = do
    case stmt of
        ModusPonens _ left right _ -> addProof builder left >> addProof builder right
        _ -> return ()
    nextSt builder $ getExpression stmt

findProof :: ProofBuilder -> Expression -> IO ProofStatement
findProof (Builder proved _) expr = liftM (fromMaybe $ Unproved expr Nothing) $ lookup proved expr

getNumberedProof :: ProofStatement -> IO [ProofStatement]
getNumberedProof stmt = do
    table <- new :: IO (HashMap Expression ProofStatement)
    let dfs cPos stmt = do
        already <- lookup table $ getExpression stmt
        case already of
            Just res -> return ([], res)
            Nothing -> do
                (list, ret) <- case stmt of
                    Unproved expr _ -> let ret = Unproved expr (Just cPos) in return ([ret], ret)
                    Axiom expr _ -> let ret = Axiom expr (Just cPos) in return ([ret], ret)
                    ModusPonens expr left right _ -> do
                        (lList, lLast) <- dfs cPos left
                        (rList, rLast) <- dfs ((fromJust $ getNum lLast) + 1) right
                        let ret = ModusPonens expr lLast rLast (Just $ (fromJust $ getNum rLast) + 1)
                        return (lList ++ rList ++ [ret], ret)
                insert table (getExpression stmt) ret
                return (list, ret)
    liftM fst $ dfs 1 stmt
