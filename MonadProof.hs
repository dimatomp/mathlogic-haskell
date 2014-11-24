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

data ProofContainer s = Cached (ST s ([ProofStatement], ProofBuilder s))
                      | Plain [ProofStatement]

getCached :: ProofContainer s -> ProofContainer s
getCached res@(Cached _) = res
getCached (Plain origList) =
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
        builderST = do
            builder <- newBuilder
            builder <- foldM nextSt builder $ map getExpression $ reverse list
            stmts <- mapM (findProof builder . getExpression) list
            return (stmts, builder)
    in Cached builderST

instance Monoid (ProofContainer s) where
    mempty = Plain []
    mappend (Plain list) (Plain list2) = Plain (list2 ++ list)
    mappend src@(Plain _) plus@(Cached _) = mappend (getCached src) plus
    mappend (Cached builder) plus = 
        let builderST = do
            (oldList, oldBuilder) <- builder
            newList <- case plus of
                Plain list -> return list
                Cached cont -> liftM fst cont
            builder <- foldM addProof oldBuilder $ reverse newList
            newList <- mapM (findProof builder . getExpression) newList
            return (newList ++ oldList, builder)
        in Cached builderST

-- TODO Support monad transformers

type Proof s a = Writer (ProofContainer s) a

tellSt :: ProofStatement -> Proof s ()
tellSt stmt = tell $ Plain [stmt]

tellEx :: Expression -> Proof s ()
tellEx expr = tellSt $ Unproved expr Nothing

getFixed :: Proof s a -> ST s [ProofStatement]
getFixed (WriterT m) = let cont = snd $ runIdentity m in case cont of
    Plain _ -> getFixed $ tell $ getCached cont
    Cached builder -> do
        (stmts, builder) <- builder
        getFixedProof builder $ map getExpression stmts

getLast :: Proof s a -> ST s ProofStatement
getLast (WriterT m) = let cont = snd $ runIdentity m in case cont of
    Plain _ -> getLast $ tell $ getCached cont
    Cached stmt -> liftM (head . fst) stmt

getMinimal :: Proof s a -> ST s [ProofStatement]
getMinimal proof = liftM getNumberedProof $ getLast proof
