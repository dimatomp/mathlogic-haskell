{-# LANGUAGE NoImplicitPrelude, TupleSections, FlexibleInstances, GeneralizedNewtypeDeriving #-}

module Proof where

import Prelude hiding (lookup)

import Data.HashMap.Strict hiding (empty, foldl, foldr, map)
import Data.Maybe
import qualified Data.List as L
import qualified Data.HashMap.Strict as H (empty)

import Control.Applicative (Applicative(..), Alternative(..))
import Control.Monad
import Control.Monad.State.Class
import Control.Monad.State

import Expression
import Axioms

--import Debug.Trace

data ProofStatement = AxiomStatement { getExpression :: Expression, getNum :: Int }
                    | ModusPonens { getExpression :: Expression
                                  , getFrom :: ProofStatement, getImpl :: ProofStatement }
                    | Any { getExpression :: Expression, getFrom :: ProofStatement }
                    | Exists { getExpression :: Expression , getFrom :: ProofStatement }

instance Show ProofStatement where
    show = show . getExpression

data ProofBuilder = Root [Axiom] (HashMap Expression ProofStatement) (HashMap Expression [Expression]) [ProofStatement]
                  | Assumption Expression (HashMap Expression [Expression])

initBuilder :: [Axiom] -> [ProofBuilder]
initBuilder axioms = [Root axioms H.empty H.empty []]

newtype Proof a = Proof { unProof :: StateT [ProofBuilder] (Either (Int, ErrorReport)) a }
                  deriving (Functor, Applicative, Monad, MonadState [ProofBuilder])

eplus res@(Right _) _ = res
eplus _ res@(Right _) = res
eplus (Left (_, Nothing)) res = res
eplus res _ = res

esum = foldl1 eplus

instance Alternative Proof where
    empty = liftM length getLog >>= \len -> Proof (StateT $ \_ -> Left (len, Nothing))
    a <|> b = Proof $ StateT $ liftM2 eplus (runProof a) (runProof b)

runProof :: Proof a -> [ProofBuilder] -> Either (Int, ErrorReport) (a, [ProofBuilder])
runProof = runStateT . unProof

evalProof :: Proof a -> [ProofBuilder] -> Either (Int, ErrorReport) a
evalProof = evalStateT . unProof

execProof :: Proof a -> [ProofBuilder] -> Either (Int, ErrorReport) [ProofBuilder]
execProof = execStateT . unProof

addAssumption :: Expression -> Proof ()
addAssumption expr = modify (Assumption expr H.empty :)

remAssumption :: Proof ()
remAssumption = modify tail

assume :: Expression -> Proof a -> Proof a
assume expr proof = do
    addAssumption expr
    res <- proof
    remAssumption
    return res

tellEx :: Expression -> Proof ProofStatement
tellEx expr = Proof $ StateT (`tellRec` expr)

tryTell :: Expression -> Proof (Either Expression ProofStatement)
tryTell expr = liftM Right (tellEx expr) <|> return (Left expr)

getRootLog :: Proof [ProofStatement]
getRootLog = gets $ (\(Root _ _ _ l) -> reverse l) . last

getLog :: Proof [Expression]
getLog = liftM (map getExpression) getRootLog

asRoot :: Proof ProofStatement -> Proof ProofStatement
asRoot proof = do
    oldState <- get
    put [last oldState]
    result <- liftM getExpression proof
    newRoot <- get
    put $ init oldState ++ newRoot
    tellEx result

tellRec :: [ProofBuilder] -> Expression -> Either (Int, ErrorReport) (ProofStatement, [ProofBuilder])
tellRec [Root axioms proved mp log] expr =
    let wrapMaybe (Just res) = Right res
        wrapMaybe Nothing = Left (length log, Nothing)
        wrap a = Left (length log, Just a)
        mapBoth _ f (Right r) = Right (f r)
        mapBoth f _ (Left l) = Left (f l)
        checkProved = wrapMaybe $ lookup expr proved
        tryAxioms = do
            number <- esum $ zipWith (\num f -> mapBoth (length log,) (const num) (f expr)) [1..] axioms
            return $ AxiomStatement expr number
        tryMP = do
            list <- wrapMaybe $ lookup expr mp
            left <- esum $ map (wrapMaybe . (`lookup` proved)) list
            let impl = fromJust $ lookup (getExpression left --> expr) proved
            return $ ModusPonens expr left impl
        tryExistence = case expr of
            Implication (Exist x a) b -> do
                from <- wrapMaybe $ lookup (a --> b) proved
                when (hasOccurrences x b) $ wrap $ FreeOccurrence x b
                return $ Exists expr from
            _ -> wrapMaybe Nothing
        tryForall = case expr of
            Implication a (Forall x b) -> do
                from <- wrapMaybe $ lookup (a --> b) proved
                when (hasOccurrences x a) $ wrap $ FreeOccurrence x a
                return $ Any expr from
            _ -> wrapMaybe Nothing
    in do
        result <- {-trace ("1: " ++ show expr) $ -}checkProved `eplus` tryAxioms `eplus` tryMP `eplus` tryExistence `eplus` tryForall
        let newProved = insert expr result proved
            newMP = case expr of
                Implication l r -> let list = fromMaybe [] $ lookup r mp in insert r (L.insert l list) mp
                _ -> mp
        {-trace ("1: Success") $-}
        return (result, [Root axioms newProved newMP (result:log)])
tellRec stack@(Assumption supp mp : tail) expr =
    let rootLength = let Root _ _ _ l = last tail in length l
        wrapMaybe (Just res) = Right res
        wrapMaybe Nothing = Left (rootLength, Nothing)
        wrap a = Left (rootLength, Just a)
        retrieve expr =
            let grown = foldl (flip (-->)) expr $ map (\(Assumption s _) -> s) $ init stack
                Root _ table _ _ = last tail
            in {-trace ("Checking for " ++ show grown) $ -}liftM (, tail) $ wrapMaybe $ lookup grown table
        itsMe = do
            when (expr /= supp) $ wrapMaybe Nothing
            (_, tail) <- tellRec tail $ expr --> expr --> expr
            (_, tail) <- tellRec tail $ expr --> (expr --> expr) --> expr
            (_, tail) <- tellRec tail $ (expr --> (expr --> expr)) --> (expr --> (expr --> expr) --> expr) --> expr --> expr
            (_, tail) <- tellRec tail $ (expr --> (expr --> expr) --> expr) --> expr --> expr
            tellRec tail $ expr --> expr
        whoKnows = do
            (_, tail) <- tellRec tail expr
            (_, tail) <- tellRec tail $ expr --> supp --> expr
            tellRec tail $ supp --> expr
        tryMP = do
            list <- wrapMaybe $ lookup expr mp
            left <- esum $ map (liftM2 (>>) retrieve return) list
            (_, tail) <- tellRec tail $ (supp --> left) --> (supp --> left --> expr) --> supp --> expr
            (_, tail) <- tellRec tail $ (supp --> left --> expr) --> supp --> expr
            tellRec tail $ supp --> expr
        swapArgs a b c = assume b $ assume a $ do
            tellEx $ a --> b --> c
            tellEx $ a
            tellEx $ b --> c
            tellEx $ b
            tellEx $ c
        tryExistence = case expr of
            Implication (Exist x a) b -> do
                retrieve $ a --> b
                when (hasOccurrences x b) $ wrap $ FreeOccurrence x b
                when (hasOccurrences x supp) $ wrap $ BadRuleUsage x supp
                (_, tail) <- runProof (swapArgs supp a b) tail
                (_, tail) <- tellRec tail $ Exist x a --> supp --> b
                runProof (swapArgs (Exist x a) supp b) tail
            _ -> wrapMaybe Nothing
        tryForall = case expr of
            Implication a (Forall x b) -> do
                retrieve $ a --> b
                when (hasOccurrences x a) $ wrap $ FreeOccurrence x a
                when (hasOccurrences x supp) $ wrap $ BadRuleUsage x supp
                (_, tail) <- flip runProof tail $ assume (supp &&& a) $ do
                    tellEx $ supp &&& a
                    tellEx $ supp &&& a --> supp
                    tellEx $ supp
                    tellEx $ supp &&& a --> a
                    tellEx $ a
                    tellEx $ supp --> a --> b
                    tellEx $ a --> b
                    tellEx $ b
                (_, tail) <- tellRec tail $ supp &&& a --> Forall x b
                flip runProof tail $ assume supp $ assume a $ do
                    tellEx $ supp
                    tellEx $ a
                    tellEx $ supp --> a --> supp &&& a
                    tellEx $ a --> supp &&& a
                    tellEx $ supp &&& a
                    tellEx $ supp &&& a --> Forall x b
                    tellEx $ Forall x b
            _ -> wrapMaybe Nothing
    in do
        (result, tail) <- {-trace (show (length stack) ++ ": " ++ show expr) $-}
            {-checkProved `eplus` -}itsMe `eplus` whoKnows `eplus` tryMP `eplus` tryExistence `eplus` tryForall
        let newMP = case expr of
                Implication l r -> let list = fromMaybe [] $ lookup r mp in insert r (L.insert l list) mp
                _ -> mp
        {-trace (show (length stack) ++ ": Success") $-}
        return (result, Assumption supp newMP : tail)
