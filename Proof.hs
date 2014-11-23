{-# LANGUAGE NoImplicitPrelude #-}

module Proof where

import Prelude hiding (lookup)

import Data.HashTable.ST.Basic
import Data.Maybe
import Data.List (find)

import Control.Monad
import Control.Monad.ST

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

data ProofBuilder s = Builder (HashTable s Expression ProofStatement) 
                              (HashTable s Expression [ProofStatement])

newBuilder :: ST s (ProofBuilder s)
newBuilder = do
    proved <- new
    forMP <- new
    return $ Builder proved forMP

findProof :: ProofBuilder s -> Expression -> ST s ProofStatement
findProof (Builder proved _) expr = liftM (fromMaybe (Unproved expr Nothing)) $ lookup proved expr

tryAdd :: ProofBuilder s -> Expression -> ST s ProofStatement
tryAdd builder@(Builder proved forMP) expr = do 
    alreadyProved <- lookup proved expr
    let isAxiom = if any (isJust . (`matches` expr)) classicAxioms
        then Just $ Axiom expr Nothing
        else Nothing
    success <- liftM catMaybes $ lookupOrEmpty forMP expr >>= mapM ((lookup proved) . getLeft . getExpression)
    let firstSuccess = (find (\x -> case x of Unproved _ _ -> False; _ -> True) success) `mplus` (listToMaybe success)
    modusPonens <- case firstSuccess of
        Nothing -> return Nothing
        Just fromPart -> do
            implPart <- lookup proved $ Implication (getExpression fromPart) expr
            return $ Just $ ModusPonens expr fromPart (fromJust implPart) Nothing
    let priority = case alreadyProved of
            Just (Unproved _ _) -> isAxiom `mplus` modusPonens `mplus` alreadyProved
            _ -> alreadyProved `mplus` isAxiom `mplus` modusPonens
    return $ fromMaybe (Unproved expr Nothing) priority
    where lookupOrEmpty t k = liftM (fromMaybe []) $ lookup t k

addStatement :: ProofBuilder s -> ProofStatement -> ST s ProofStatement
addStatement builder@(Builder proved forMP) stmt = do
    let expr = getExpression stmt
    insert proved expr stmt
    case expr of
        Implication l r -> do
            findRight <- lookupOrEmpty forMP r
            insert forMP r $ stmt:findRight
        _               -> return ()
    findProof builder expr
    where lookupOrEmpty t k = liftM (fromMaybe []) $ lookup t k
    
nextSt :: ProofBuilder s -> Expression -> ST s ProofStatement
nextSt builder expr = tryAdd builder expr >>= addStatement builder

addProof :: ProofBuilder s -> ProofStatement -> ST s ProofStatement
addProof builder stmt = case stmt of
    ModusPonens expr left right _ -> do
        addNow <- tryAdd builder expr
        case addNow of
            Unproved _ _ -> do
                addProof builder left
                addProof builder right
                nextSt builder expr
            _ -> return addNow
    _ -> nextSt builder $ getExpression stmt

renumber :: ProofStatement -> Int -> ProofStatement
renumber (Unproved e _) pos = Unproved e $ Just pos
renumber (Axiom e _) pos = Axiom e $ Just pos
renumber (ModusPonens e l r _) pos = ModusPonens e l r $ Just pos

getNumberedProof :: ProofStatement -> [ProofStatement]
getNumberedProof stmt = runST $ do
    table <- new :: ST s (HashTable s Expression ProofStatement)
    let dfs cPos stmt = do
        already <- lookup table $ getExpression stmt
        case already of
            Just res -> return ([], renumber res $ cPos - 1)
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

getFixedProof :: ProofBuilder s -> [Expression] -> ST s [ProofStatement]
getFixedProof builder list = do
    table <- new :: ST s (HashTable s Expression ProofStatement)
    let addSeq [] = return []
        addSeq list@(expr:res) = do
            prevStatements <- addSeq res
            let stNumber = length list
                renumber stmt = case stmt of
                    Unproved e _ -> return $ Unproved e $ Just stNumber
                    Axiom a _ -> return $ Axiom a $ Just stNumber
                    ModusPonens e l r _ -> do
                        let lExpr = getExpression l
                            rExpr = getExpression r
                        leftB <- liftM (fromMaybe $ Unproved lExpr Nothing) $ lookup table lExpr
                        rightB <- liftM (fromMaybe $ Unproved rExpr Nothing) $ lookup table rExpr
                        return $ ModusPonens e leftB rightB $ Just stNumber
            stmt <- findProof builder expr >>= renumber
            insert table expr stmt
            return $ stmt:prevStatements
    liftM reverse $ addSeq $ reverse list 
