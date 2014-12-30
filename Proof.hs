{-# LANGUAGE NoImplicitPrelude #-}

module Proof (execProof, getProof, getLog, Proof, tellEx, assume, ProofStatement(..)) where

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
import Control.Monad.Trans.Writer

import Expression
import Axioms (getClassicAxiom)

data ProofStatement = Axiom { getExpression :: Expression }
                    | ModusPonens { getExpression :: Expression
                                  , getFrom :: ProofStatement, getImpl :: ProofStatement }

instance Show ProofStatement where
    show = show . getExpression

data ProofBuilder s = Root (HashTable s Expression ProofStatement) (HashTable s Expression [ProofStatement])
                    | Supposition Expression (HashTable s Expression ()) (HashTable s Expression [Expression])

tellRec :: [ProofBuilder s] -> Expression -> MaybeT (WriterT [Either Expression ProofStatement] (ST s)) ProofStatement
tellRec [Root proved forMP] expr = mplus (MaybeT (lift $ lookup proved expr) >>= \stmt -> lift (tell [Right stmt]) >> return stmt) $
    let accept stmt = do
        lift $ lift $ insert proved expr stmt
        case expr of
            Implication _ r -> do
                existing <- lift $ lift $ liftM (fromMaybe []) $ lookup forMP r
                lift $ lift $ insert forMP r (stmt:existing)
            _ -> return ()
        lift $ tell [Right stmt]
        return stmt
    in if isJust $ getClassicAxiom expr then accept $ Axiom expr else (do
        (left, impl) <- MaybeT $ lift $ liftM listToMaybe $ runListT $ do
            impl <- ListT $ liftM (fromMaybe []) $ lookup forMP expr
            left <- lift $ lookup proved $ getLeft $ getExpression impl
            guard $ isJust left
            return (fromJust left, impl)
        accept $ ModusPonens expr left impl) `mplus` (MaybeT $ tell [Left expr] >> return Nothing)
tellRec list@(Supposition supp proved forMP : nextStep) expr =
    let accept = do
            lift $ lift $ insert proved expr ()
            case expr of
                Implication _ r -> do
                    existing <- lift $ lift $ liftM (fromMaybe []) $ lookup forMP r
                    lift $ lift $ insert forMP r (expr:existing)
                _ -> return ()
        assume = do
            tellRec nextStep $ expr
            tellRec nextStep $ expr --> supp --> expr
            lastProved <- tellRec nextStep $ supp --> expr
            accept
            return lastProved
    in (do
        MaybeT $ lift $ lookup proved expr
        let Root lastProved _ = last nextStep
            fullExpr = foldl (\impl (Supposition supp _ _) -> supp --> impl) expr $ init list
        MaybeT $ lift $ lookup lastProved fullExpr
    ) `mplus` if expr == supp then do
        accept
        tellRec nextStep $ expr --> expr --> expr
        tellRec nextStep $ expr --> (expr --> expr) --> expr
        tellRec nextStep $ (expr --> expr --> expr) --> (expr --> (expr --> expr) --> expr) --> expr --> expr
        tellRec nextStep $ (expr --> (expr --> expr) --> expr) --> expr --> expr
        tellRec nextStep $ expr --> expr
    else if isJust (getClassicAxiom expr) then assume else flip mplus assume $ do
        left <- MaybeT $ lift $ liftM listToMaybe $ runListT $ do
            left <- ListT $ liftM (fromMaybe []) $ lookup forMP expr
            exists <- lift $ lookup proved $ getLeft left
            guard $ isJust exists
            return $ getLeft left
        accept
        tellRec nextStep $ (supp --> left) --> (supp --> left --> expr) --> supp --> expr
        tellRec nextStep $ (supp --> left --> expr) --> supp --> expr
        tellRec nextStep $ supp --> expr

type Proof s = StateT [ProofBuilder s] (MaybeT (WriterT [Either Expression ProofStatement] (ST s)))

tellEx :: Expression -> Proof s ProofStatement
tellEx expr = StateT $ \builder -> do
    result <- tellRec builder expr
    return (result, builder)

assume :: Expression -> Proof s a -> Proof s a
assume expr inside = do
    proved <- lift $ lift $ lift new
    forMP <- lift $ lift $ lift new
    StateT $ \supp -> return ((), (Supposition expr proved forMP : supp))
    --tellEx expr
    lastStmt <- inside
    StateT $ \(_:supp) -> return (lastStmt, supp)

tellSt :: ProofStatement -> Proof s ProofStatement
tellSt (Axiom expr) = tellEx expr
tellSt (ModusPonens expr left right) = tellSt left >> tellSt right >> tellEx expr

execProof :: Proof s ProofStatement -> ST s (Maybe ProofStatement, [Either Expression ProofStatement])
execProof p = newBuilder >>= runWriterT . runMaybeT . evalStateT p
    where
        newBuilder = do
            proved <- new
            forMP <- new
            return [Root proved forMP]

getProof = liftM fst . execProof

getLog = liftM snd . execProof
