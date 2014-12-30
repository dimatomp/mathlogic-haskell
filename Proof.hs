{-# LANGUAGE NoImplicitPrelude #-}

module Proof (getProof, Proof, tellEx, assume, ProofStatement(..)) where

import Prelude hiding (lookup)

import Data.HashTable.ST.Basic
import Data.Maybe
import Data.List (find)

import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.List

import Expression
import Axioms (getClassicAxiom)

data ProofStatement = Axiom { getExpression :: Expression }
                    | ModusPonens { getExpression :: Expression
                                  , getFrom :: ProofStatement, getImpl :: ProofStatement }

instance Show ProofStatement where
    show = show . getExpression

data ProofBuilder s = Root (HashTable s Expression ProofStatement) (HashTable s Expression [ProofStatement])
                    | Supposition Expression (HashTable s Expression ()) (HashTable s Expression [Expression])

tellRec :: [ProofBuilder s] -> Expression -> MaybeT (ST s) ProofStatement
tellRec [Root proved forMP] expr = mplus (MaybeT $ lookup proved expr) $
    let accept stmt = do
        lift $ insert proved expr stmt
        case expr of
            Implication _ r -> do
                existing <- lift $ liftM (fromMaybe []) $ lookup forMP r
                lift $ insert forMP r (stmt:existing)
            _ -> return ()
        return stmt
    in if isJust $ getClassicAxiom expr then accept $ Axiom expr else do
        (left, impl) <- MaybeT $ liftM listToMaybe $ runListT $ do
            impl <- ListT $ liftM (fromMaybe []) $ lookup forMP expr
            left <- lift $ lookup proved $ getLeft $ getExpression impl
            guard $ isJust left
            return (fromJust left, impl)
        accept $ ModusPonens expr left impl
tellRec list@(Supposition supp proved forMP : nextStep) expr =
    let accept = do
            lift $ insert proved expr ()
            case expr of
                Implication _ r -> do
                    existing <- lift $ liftM (fromMaybe []) $ lookup forMP r
                    lift $ insert forMP r (expr:existing)
                _ -> return ()
        assume = do
            tellRec nextStep $ expr
            tellRec nextStep $ expr --> supp --> expr
            lastProved <- tellRec nextStep $ supp --> expr
            accept
            return lastProved
    in (do
        MaybeT $ lookup proved expr
        let Root lastProved _ = last nextStep
            fullExpr = foldl (\impl (Supposition supp _ _) -> supp --> impl) expr $ init list
        MaybeT $ lookup lastProved fullExpr
    ) `mplus` if expr == supp then do
        accept
        tellRec nextStep $ expr --> expr --> expr
        tellRec nextStep $ expr --> (expr --> expr) --> expr
        tellRec nextStep $ (expr --> expr --> expr) --> (expr --> (expr --> expr) --> expr) --> expr --> expr
        tellRec nextStep $ (expr --> (expr --> expr) --> expr) --> expr --> expr
        tellRec nextStep $ expr --> expr
    else if isJust (getClassicAxiom expr) then assume else flip mplus assume $ do
        left <- MaybeT $ liftM listToMaybe $ runListT $ do
            left <- ListT $ liftM (fromMaybe []) $ lookup forMP expr
            exists <- lift $ lookup proved $ getLeft left
            guard $ isJust exists
            return $ getLeft left
        accept
        tellRec nextStep $ (supp --> left) --> (supp --> left --> expr) --> supp --> expr
        tellRec nextStep $ (supp --> left --> expr) --> supp --> expr
        tellRec nextStep $ supp --> expr

type Proof s = StateT [ProofBuilder s] (MaybeT (ST s))

tellEx :: Expression -> Proof s ProofStatement
tellEx expr = StateT $ \builder -> do
    result <- tellRec builder expr
    return (result, builder)

assume :: Expression -> Proof s ProofStatement -> Proof s ProofStatement
assume expr inside = do
    proved <- lift $ lift new
    forMP <- lift $ lift new
    StateT $ \supp -> return ((), (Supposition expr proved forMP : supp))
    tellEx expr
    lastStmt <- inside
    StateT $ \(_:supp) -> return (lastStmt, supp)

tellSt :: ProofStatement -> Proof s ProofStatement
tellSt (Axiom expr) = tellEx expr
tellSt (ModusPonens expr left right) = tellSt left >> tellSt right >> tellEx expr

getProof :: Proof s ProofStatement -> ST s (Maybe ProofStatement)
getProof p = newBuilder >>= runMaybeT . evalStateT p
    where
        newBuilder = do
            proved <- new
            forMP <- new
            return [Root proved forMP]
