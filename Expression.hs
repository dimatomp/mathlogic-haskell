{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Expression where

import Data.Maybe
import Data.Functor
import Data.List

import Control.Monad

import Algebra.Monad.Base (bind2)

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

freeForSubst :: Function -> Expression -> String -> Bool
freeForSubst theta phi x = verify (grabFunc theta) phi
  where
      grabFunc (Stroke p) = grabFunc p
      grabFunc (Mult l r) = grabFunc l `union` grabFunc r
      grabFunc (Plus l r) = grabFunc l `union` grabFunc r
      grabFunc (Var x) = [x]
      grabFunc Zero = []

      verifyNot (Forall _ p) = verifyNot p
      verifyNot (Exist _ p) = verifyNot p
      verifyNot (Not p) = verifyNot p
      verifyNot (And a b) = verifyNot a && verifyNot b
      verifyNot (Or a b) = verifyNot a && verifyNot b
      verifyNot (Implication a b) = verifyNot a && verifyNot b
      verifyNot (Equal l r) = not $ x `elem` grabFunc l ++ grabFunc r
      verifyNot (Predicate _ list) = all (not . elem x . grabFunc) list
      verifyNot (Gap _) = True

      verify l (Forall y p)
        | y `elem` l = verifyNot p
        | otherwise = verify l p
      verify l (Exist y p)
        | y `elem` l = verifyNot p
        | otherwise = verify l p
      verify l (Not p) = verify l p
      verify l (And a b) = verify l a && verify l b
      verify l (Or a b) = verify l a && verify l b
      verify l (Implication a b) = verify l a && verify l b
      verify _ _ = True

matches = (isJust .) . matchWith

matchWith :: Expression -> Expression -> Maybe ([(String, Expression)], [(String, Function)])
matchWith e1 e2 = matchesMaybe (\_ -> Nothing) e1 e2
    where
        mergeFunc :: Eq a => [(String, a)] -> [(String, a)] -> Maybe [(String, a)]
        mergeFunc l1 l2 = (forM_ l1 $ \(k, v) ->
            case lookup k l2 of
                Just v2 -> guard $ v == v2
                Nothing -> return ()) >> Just (union l1 l2)

        matchesFunc _ Zero Zero = Just []
        matchesFunc t (Var n) res = case t n of
            Just name -> guard (res == Var name) >> Just []
            Nothing -> Just [(n, res)]
        matchesFunc t (Stroke e1) (Stroke e2) = matchesFunc t e1 e2
        matchesFunc t (Plus l1 r1) (Plus l2 r2) = bind2 mergeFunc (matchesFunc t l1 l2) (matchesFunc t r1 r2)
        matchesFunc t (Mult l1 r1) (Mult l2 r2) = bind2 mergeFunc (matchesFunc t l1 l2) (matchesFunc t r1 r2)
        matchesFunc _ _ _ = Nothing

        merge (e1, f1) (e2, f2) = do
            e <- mergeFunc e1 e2
            f <- mergeFunc f1 f2
            return (e, f)

        add t s1 s2 s = if s == s1 then Just s2 else t s

        matchesMaybe t (Gap n) res = Just ([(n, res)], [])
        matchesMaybe t (And l1 r1) (And l2 r2) = bind2 merge (matchesMaybe t l1 l2) (matchesMaybe t r1 r2)
        matchesMaybe t (Or l1 r1) (Or l2 r2) = bind2 merge (matchesMaybe t l1 l2) (matchesMaybe t r1 r2)
        matchesMaybe t (Implication l1 r1) (Implication l2 r2) = bind2 merge (matchesMaybe t l1 l2) (matchesMaybe t r1 r2)
        matchesMaybe t (Not p1) (Not p2) = matchesMaybe t p1 p2
        matchesMaybe t (Forall s1 e1) (Forall s2 e2) = matchesMaybe (add t s1 s2) e1 e2
        matchesMaybe t (Exist s1 e1) (Exist s2 e2) = matchesMaybe (add t s1 s2) e1 e2
        matchesMaybe t (Equal a b) (Equal c d) = fmap (\l -> ([], l)) $ bind2 mergeFunc (matchesFunc t a c) (matchesFunc t b d)
        matchesMaybe t (Predicate s1 l1) (Predicate s2 l2)
            | s1 == s2 = liftM (\l -> ([], l)) $ zipWithM (matchesFunc t) l1 l2 >>= foldM mergeFunc []
            | otherwise = Nothing
        matchesMaybe _ _ _ = Nothing
