{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module MonadProof where

import Expression
import Proof

import Data.List
import Data.Monoid hiding (getLast)

import Control.Monad
import Control.Monad.ST
import Control.Monad.Identity
import Control.Monad.Writer hiding (getLast)

newtype ProofContainer = ProofContainer { runContainer :: [ProofStatement] }

instance Monoid ProofContainer where
    mempty = ProofContainer []
    mappend a b = ProofContainer $ runContainer b ++ runContainer a

getCached :: ProofContainer -> ST s ([ProofStatement], ProofBuilder s)
getCached (ProofContainer origList) =
    let extract res@(Unproved _ _) = [res]
        extract res@(Axiom _ _) = [res]
        extract res@(ModusPonens _ l r _) = res : (extract r ++ extract l)
        
        -- TODO There must be a better solution!
        removeDuplicates [] = []
        removeDuplicates [a] = [a]
        removeDuplicates (f:s:suf) = if getExpression f == getExpression s
            then removeDuplicates $ s:suf
            else f:(removeDuplicates $ s:suf)

        list = removeDuplicates $ concatMap extract origList
    in do
        builder <- newBuilder
        builder <- foldM nextSt builder $ map getExpression $ reverse list
        stmts <- mapM (findProof builder . getExpression) list
        return (stmts, builder)

type Proof a = Writer ProofContainer a
type ProofT m a = WriterT ProofContainer m a

tellSt :: Monad m => ProofStatement -> ProofT m ()
tellSt stmt = tell $ ProofContainer [stmt]

tellEx :: Monad m => Expression -> ProofT m ()
tellEx expr = tellSt $ Unproved expr Nothing

getFixedM :: Monad m => ProofT m a -> m [ProofStatement]
getFixedM (WriterT m) = m >>= \(_, cont) -> return $ runST $ do
    (stmts, builder) <- getCached cont
    getFixedProof builder $ map getExpression stmts

getLastM :: Monad m => ProofT m a -> m ProofStatement
getLastM (WriterT m) = m >>= \(_, cont) -> return $ runST $ do
    (stmts, _) <- getCached cont
    return $ head stmts

getMinimalM :: Monad m => ProofT m a -> m [ProofStatement]
getMinimalM proof = liftM getNumberedProof $ getLastM proof

getFixed = runIdentity . getFixedM
getLast = runIdentity . getLastM
getMinimal = runIdentity . getMinimalM
