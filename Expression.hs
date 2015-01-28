{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Expression where

import Data.Maybe
import Data.List

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
              | Var String
              | Zero
              deriving (Eq, Ord)

instance Show Function where
    showsPrec _ (Stroke p) = showsPrec 7 p . showChar '\''
    showsPrec _ (Var s) = showString s
    showsPrec n (Mult l r) = showParen (n > 6) $ showsPrec 6 l . showChar '*' . showsPrec 7 r
    showsPrec n (Plus l r) = showParen (n > 5) $ showsPrec 5 l . showChar '+' . showsPrec 6 r
    showsPrec _ Zero = showChar '0'

data Expression = Gap String
                | Not Expression
                | And Expression Expression
                | Or Expression Expression
                | Implication Expression Expression
                | Forall String Expression
                | Exist String Expression
                | Equal Function Function
                | Predicate String [Function]
                deriving (Eq, Ord)

instance Show Expression where
    showsPrec _ (Gap n) = showString n
    showsPrec _ (Not p) = showChar '!' . showsPrec 5 p
    showsPrec n (And l r) = showParen (n > 3) $ showsPrec 3 l . showChar '&' . showsPrec 4 r
    showsPrec n (Or l r) = showParen (n > 2) $ showsPrec 2 l . showChar '|' . showsPrec 3 r
    showsPrec n (Implication l r) = showParen (n > 1) $ showsPrec 2 l . showString "->" . showsPrec 1 r
    showsPrec _ (Forall s e) = showChar '@' . showString s . showsPrec 7 e
    showsPrec _ (Exist s e) = showChar '?' . showString s . showsPrec 7 e
    showsPrec _ (Equal f1 f2) = shows f1 . showChar '=' . shows f2
    showsPrec _ (Predicate s list) = showString s . showChar '(' . showParam list . showChar ')'
        where
            showParam [expr] = shows expr
            showParam (f:s) = shows f . showChar ',' . showParam s

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

data ErrorMessage = UnsafeForSubst Function Expression String
                  | FreeOccurrence String Expression
                  | BadRuleUsage String Expression
                  deriving Show

matches = (isJust .) . matchWith

matchWith :: Expression -> Expression -> Maybe (([(String, Expression)], [(String, Function)]), Maybe ErrorMessage)
matchWith e1 e2 = runStateT (matchesMaybe [] e1 e2) Nothing
    where
        mergeFunc :: (Eq a, MonadPlus m) => [(String, a)] -> [(String, a)] -> m [(String, a)]
        mergeFunc l1 l2 = (forM_ l1 $ \(k, v) ->
            case lookup k l2 of
                Just v2 -> guard $ v == v2
                Nothing -> return ()) >> return (union l1 l2)

        isSafe :: [String] -> Function -> Bool
        isSafe list (Stroke f) = isSafe list f
        isSafe list (Var n) = not $ n `elem` list
        isSafe list (Plus l r) = isSafe list l && isSafe list r
        isSafe list (Mult l r) = isSafe list l && isSafe list r
        isSafe _ Zero = True

        matchesFunc :: [(String, String)] -> Function -> Function -> StateT (Maybe ErrorMessage) Maybe [(String, Function)]
        matchesFunc _ Zero Zero = return []
        matchesFunc t (Var n) res@(Var m) = mapM checkForFail t >>= foldr mplus (return [(n, res)])
            where
                checkForFail (s1, s2)
                    | s1 == n || s2 == m = if s1 == n && s2 == m then return $ return [] else mzero
                    | otherwise = return mzero
        matchesFunc t (Var n) res = do
            forM_ t $ guard . (n /=) . fst
            when (not $ isSafe (map fst t) res) $ put $ Just $ UnsafeForSubst res e1 n
            return [(n, res)]
        matchesFunc t (Stroke e1) (Stroke e2) = matchesFunc t e1 e2
        matchesFunc t (Plus l1 r1) (Plus l2 r2) = bind2 mergeFunc (matchesFunc t l1 l2) (matchesFunc t r1 r2)
        matchesFunc t (Mult l1 r1) (Mult l2 r2) = bind2 mergeFunc (matchesFunc t l1 l2) (matchesFunc t r1 r2)
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
        matchesMaybe t (Forall s1 e1) (Forall s2 e2) = matchesMaybe ((s1, s2):t) e1 e2
        matchesMaybe t (Exist s1 e1) (Exist s2 e2) = matchesMaybe ((s1, s2):t) e1 e2
        matchesMaybe t (Equal a b) (Equal c d) = liftM (\l -> ([], l)) $ bind2 mergeFunc (matchesFunc t a c) (matchesFunc t b d)
        matchesMaybe t (Predicate s1 l1) (Predicate s2 l2)
            | s1 == s2 = liftM (\l -> ([], l)) $ zipWithM (matchesFunc t) l1 l2 >>= foldM mergeFunc []
            | otherwise = mzero
        matchesMaybe _ _ _ = mzero

hasOccurFunc s (Var n) = s == n
hasOccurFunc s (Stroke l) = hasOccurFunc s l
hasOccurFunc s (Plus l r) = hasOccurFunc s l || hasOccurFunc s r
hasOccurFunc s (Mult l r) = hasOccurFunc s l || hasOccurFunc s r
hasOccurFunc _ Zero = False

hasOccurrences :: String -> Expression -> Bool
hasOccurrences s (And l r) = hasOccurrences s l || hasOccurrences s r
hasOccurrences s (Or l r) = hasOccurrences s l || hasOccurrences s r
hasOccurrences s (Implication l r) = hasOccurrences s l || hasOccurrences s r
hasOccurrences s (Not p) = hasOccurrences s p
hasOccurrences s (Forall n e) = s /= n && hasOccurrences s e
hasOccurrences s (Exist n e) = s /= n && hasOccurrences s e
hasOccurrences s (Equal l r) = hasOccurFunc s l || hasOccurFunc s r
hasOccurrences s (Predicate _ list) = any (hasOccurFunc s) list
hasOccurrences _ _ = False
