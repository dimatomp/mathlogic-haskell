{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Expression where

import Data.Maybe
import Data.List
import Data.Hashable

import qualified Data.ByteString.Char8 as B

import Control.Monad
import Control.Monad.Trans.State

bind2 :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
bind2 f ma mb = do
    a <- ma
    b <- mb
    f a b

data Function = Stroke Function
              | Mult Function Function
              | Plus Function Function
              | Func B.ByteString [Function]
              | Var B.ByteString
              | Zero
              deriving (Eq, Ord)

showB = showString . B.unpack

instance Show Function where
    showsPrec _ (Stroke p) = showsPrec 7 p . showChar '\''
    showsPrec _ (Var s) = showB s
    showsPrec n (Mult l r) = showParen (n > 6) $ showsPrec 6 l . showChar '*' . showsPrec 7 r
    showsPrec n (Plus l r) = showParen (n > 5) $ showsPrec 5 l . showChar '+' . showsPrec 6 r
    showsPrec _ (Func s list) = showB s . showChar '(' . showList list . showChar ')'
        where
            showList [expr] = shows expr
            showList (f:s) = shows f . showChar ',' . showList s
    showsPrec _ Zero = showChar '0'

data Expression = Gap B.ByteString
                | Not Expression
                | And Expression Expression
                | Or Expression Expression
                | Implication Expression Expression
                | Forall B.ByteString Expression
                | Exist B.ByteString Expression
                | Equal Function Function
                | Predicate B.ByteString [Function]
                deriving (Eq, Ord)

instance Show Expression where
    showsPrec _ (Gap n) = showB n
    showsPrec _ (Not p) = showChar '!' . showsPrec 5 p
    showsPrec n (And l r) = showParen (n > 3) $ showsPrec 3 l . showChar '&' . showsPrec 4 r
    showsPrec n (Or l r) = showParen (n > 2) $ showsPrec 2 l . showChar '|' . showsPrec 3 r
    showsPrec n (Implication l r) = showParen (n > 1) $ showsPrec 2 l . showString "->" . showsPrec 1 r
    showsPrec _ (Forall s e) = showChar '@' . showB s . showsPrec 7 e
    showsPrec _ (Exist s e) = showChar '?' . showB s . showsPrec 7 e
    showsPrec _ (Equal f1 f2) = shows f1 . showChar '=' . shows f2
    showsPrec _ (Predicate s list) = showB s . showChar '(' . showParam list . showChar ')'
        where
            showParam [expr] = shows expr
            showParam (f:s) = shows f . showChar ',' . showParam s

instance Hashable Function where
    hashWithSalt p (Stroke f) = hashWithSalt p f * p + 1
    hashWithSalt p (Mult l r) = hashWithSalt p l * p * p + hashWithSalt p r * p + 2
    hashWithSalt p (Plus l r) = hashWithSalt p l * p * p + hashWithSalt p r * p + 3
    hashWithSalt p (Func e l) = foldr ((+) . (* p) . hashWithSalt p) (hashWithSalt p e) l * p + 4
    hashWithSalt p (Var s) = hashWithSalt p s * p + 5
    hashWithSalt p Zero = 6

instance Hashable Expression where
    hashWithSalt p (Gap s) = hashWithSalt p s * p + 7
    hashWithSalt p (Not a) = hashWithSalt p a * p + 8
    hashWithSalt p (And l r) = hashWithSalt p l * p * p + hashWithSalt p r * p + 9
    hashWithSalt p (Or l r) = hashWithSalt p l * p * p + hashWithSalt p r * p + 10
    hashWithSalt p (Implication l r) = hashWithSalt p l * p * p + hashWithSalt p r * p + 11
    hashWithSalt p (Forall x e) = hashWithSalt p e * p * p + hashWithSalt p x * p + 12
    hashWithSalt p (Exist x e) = hashWithSalt p e * p * p + hashWithSalt p x * p + 13
    hashWithSalt p (Equal l r) = hashWithSalt p l * p * p + hashWithSalt p r * p + 14
    hashWithSalt p (Predicate s l) = foldr ((+) . (* p) . hashWithSalt p) (hashWithSalt p s) l * p + 15

infixl 6 ***
infixl 5 +++
infixl 4 ===
infixl 3 &&&
infixl 2 |||
infixr 1 -->
(***) = Mult
(+++) = Plus
(===) = Equal
(&&&) = And
(|||) = Or
(-->) = Implication

data ErrorMessage = UnsafeForSubst Function Expression B.ByteString
                  | FreeOccurrence B.ByteString Expression
                  | BadRuleUsage B.ByteString Expression
                  deriving Show

matches = (isJust .) . matchWith

matchWith :: Expression -> Expression -> Maybe (([(B.ByteString, Expression)], [(B.ByteString, Function)]), Maybe ErrorMessage)
matchWith e1 e2 = runStateT (matchesMaybe [] e1 e2) Nothing
    where
        mergeFunc :: (Eq a, MonadPlus m) => [(B.ByteString, a)] -> [(B.ByteString, a)] -> m [(B.ByteString, a)]
        mergeFunc l1 l2 = (forM_ l1 $ \(k, v) ->
            case lookup k l2 of
                Just v2 -> guard $ v == v2
                Nothing -> return ()) >> return (union l1 l2)

        isSafe :: [B.ByteString] -> Function -> Bool
        isSafe list (Stroke f) = isSafe list f
        isSafe list (Var n) = not $ n `elem` list
        isSafe list (Plus l r) = isSafe list l && isSafe list r
        isSafe list (Mult l r) = isSafe list l && isSafe list r
        isSafe list (Func s args) = all (isSafe list) args
        isSafe _ Zero = True

        matchesFunc :: [B.ByteString] -> Function -> Function -> StateT (Maybe ErrorMessage) Maybe [(B.ByteString, Function)]
        matchesFunc _ Zero Zero = return []
        matchesFunc t (Var n) res@(Var m)
            | n == m = return $ if n `elem` t then [] else [(n, res)]
            | otherwise = do
                guard $ not $ n `elem` t
                when (m `elem` t) $ put $ Just $ UnsafeForSubst res e1 n
                return [(n, res)]
        matchesFunc t (Var n) res = do
            guard $ not $ n `elem` t
            when (not $ isSafe t res) $ put $ Just $ UnsafeForSubst res e1 n
            return [(n, res)]
        matchesFunc t (Stroke e1) (Stroke e2) = matchesFunc t e1 e2
        matchesFunc t (Plus l1 r1) (Plus l2 r2) = bind2 mergeFunc (matchesFunc t l1 l2) (matchesFunc t r1 r2)
        matchesFunc t (Mult l1 r1) (Mult l2 r2) = bind2 mergeFunc (matchesFunc t l1 l2) (matchesFunc t r1 r2)
        matchesFunc t (Func s1 l1) (Func s2 l2)
            | s1 == s2 = zipWithM (matchesFunc t) l1 l2 >>= foldM mergeFunc []
            | otherwise = mzero
        matchesFunc _ _ _ = mzero

        merge (e1, f1) (e2, f2) = do
            e <- mergeFunc e1 e2
            f <- mergeFunc f1 f2
            return (e, f)

        matchesMaybe t (Gap n) res = return ([(n, res)], [])
        matchesMaybe t (And l1 r1) (And l2 r2) = bind2 merge (matchesMaybe t l1 l2) (matchesMaybe t r1 r2)
        matchesMaybe t (Or l1 r1) (Or l2 r2) = bind2 merge (matchesMaybe t l1 l2) (matchesMaybe t r1 r2)
        matchesMaybe t (Implication l1 r1) (Implication l2 r2) = bind2 merge (matchesMaybe t l1 l2) (matchesMaybe t r1 r2)
        matchesMaybe t (Not p1) (Not p2) = matchesMaybe t p1 p2
        matchesMaybe t (Forall s1 e1) (Forall s2 e2) = matchesMaybe (s1:t) e1 e2
        matchesMaybe t (Exist s1 e1) (Exist s2 e2) = matchesMaybe (s1:t) e1 e2
        matchesMaybe t (Equal a b) (Equal c d) = liftM (\l -> ([], l)) $ bind2 mergeFunc (matchesFunc t a c) (matchesFunc t b d)
        matchesMaybe t (Predicate s1 l1) (Predicate s2 l2) = do
            guard $ s1 == s2
            l <- zipWithM (matchesFunc t) l1 l2 >>= foldM mergeFunc []
            return ([], l)
        matchesMaybe _ _ _ = mzero

hasOccurFunc s (Var n) = s == n
hasOccurFunc s (Stroke l) = hasOccurFunc s l
hasOccurFunc s (Plus l r) = hasOccurFunc s l || hasOccurFunc s r
hasOccurFunc s (Mult l r) = hasOccurFunc s l || hasOccurFunc s r
hasOccurFunc s (Func _ p) = any (hasOccurFunc s) p
hasOccurFunc _ Zero = False

hasOccurrences :: B.ByteString -> Expression -> Bool
hasOccurrences s (And l r) = hasOccurrences s l || hasOccurrences s r
hasOccurrences s (Or l r) = hasOccurrences s l || hasOccurrences s r
hasOccurrences s (Implication l r) = hasOccurrences s l || hasOccurrences s r
hasOccurrences s (Not p) = hasOccurrences s p
hasOccurrences s (Forall n e) = s /= n && hasOccurrences s e
hasOccurrences s (Exist n e) = s /= n && hasOccurrences s e
hasOccurrences s (Equal l r) = hasOccurFunc s l || hasOccurFunc s r
hasOccurrences s (Predicate _ list) = any (hasOccurFunc s) list
hasOccurrences _ _ = False
