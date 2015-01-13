module Expression where

import Data.Maybe
import Data.Hashable
import Data.ByteString.Char8 hiding (all)

data Expression = Var { getName :: ByteString }
                | Gap { getNumber :: Int }
                | Not { getParameter :: Expression }
                | And { getLeft :: Expression, getRight :: Expression }
                | Or { getLeft :: Expression, getRight :: Expression }
                | Implication { getLeft :: Expression, getRight :: Expression }
                deriving Eq

instance Show Expression where
    show (Gap n) = "[" ++ show n ++ "]"
    show (Var a) = unpack a
    show (Not p) = "!" ++ (case p of
        Var a -> show p
        Gap a -> show p
        Not a -> show p
        _     -> "(" ++ show p ++ ")")
    show (And l r) = (case l of
        Gap _ -> show l
        Var _ -> show l
        Not _ -> show l
        _     -> "(" ++ show l ++ ")") ++ "&" ++ (case r of
            Or _ _          -> "(" ++ show r ++ ")"
            Implication _ _ -> "(" ++ show r ++ ")"
            _               -> show r)
    show (Or l r) = (case l of
        Or _ _          -> "(" ++ show l ++ ")"
        Implication _ _ -> "(" ++ show l ++ ")"
        _               -> show l) ++ "|" ++ (case r of
            Implication _ _ -> "(" ++ show r ++ ")"
            _               -> show r)
    show (Implication l r) = (case l of
        Implication _ _ -> "(" ++ show l ++ ")"
        _               -> show l) ++ "->" ++ show r

infixl 3 &&&
infixl 2 |||
infixr 1 -->
(&&&) = And
(|||) = Or
(-->) = Implication

wrapInBrackets :: Int -> Int -> Int
wrapInBrackets p a = (p + a) * p + 2

instance Hashable Expression where
    hashWithSalt p (Var str) = wrapInBrackets p $ hashWithSalt p str
    hashWithSalt p (And left right) = wrapInBrackets p $ ((hashWithSalt p left) * p + 5) * p + hashWithSalt p right
    hashWithSalt p (Or left right) = wrapInBrackets p $ ((hashWithSalt p left) * p + 4) * p + hashWithSalt p right
    hashWithSalt p (Implication left right) = wrapInBrackets p $ ((hashWithSalt p left) * p + 3) * p + hashWithSalt p right
    hashWithSalt p (Not param) = wrapInBrackets p $ 6 * p + hashWithSalt p param
    hashWithSalt p (Gap num) = wrapInBrackets p $ num + 7

fillInGaps :: Expression -> [Expression] -> Expression
fillInGaps r@(Var _) _ = r
fillInGaps (And left right) list = (fillInGaps left list) &&& (fillInGaps right list)
fillInGaps (Or left right) list = (fillInGaps left list) ||| (fillInGaps right list)
fillInGaps (Implication left right) list = (fillInGaps left list) --> (fillInGaps right list)
fillInGaps (Not par) list = Not $ fillInGaps par list
fillInGaps (Gap i) list = list !! i

merge :: Maybe [Maybe Expression] -> Maybe [Maybe Expression] -> Maybe [Maybe Expression]
merge (Just (s1:f1)) (Just (s2:f2)) = do
    f <- merge (Just f1) (Just f2)
    case s1 of
        Nothing -> return (s2:f)
        _       -> case s2 of
            Nothing -> return (s1:f)
            _       -> if s1 == s2 then return (s1:f) else Nothing
merge (Just []) (Just res) = Just res
merge (Just res) (Just []) = Just res
merge _ _ = Nothing

matchesMaybe :: Expression -> Expression -> Maybe [Maybe Expression]
matchesMaybe ra@(Var a) rb@(Var b) = merge (Just [Just ra]) (Just [Just rb])
matchesMaybe (And l1 r1) (And l2 r2) = merge (matchesMaybe l1 l2) (matchesMaybe r1 r2)
matchesMaybe (Or l1 r1) (Or l2 r2) = merge (matchesMaybe l1 l2) (matchesMaybe r1 r2)
matchesMaybe (Implication l1 r1) (Implication l2 r2) = merge (matchesMaybe l1 l2) (matchesMaybe r1 r2)
matchesMaybe (Not p1) (Not p2) = matchesMaybe p1 p2
matchesMaybe (Gap n) res = Just [if i < n then Nothing else Just res | i <- [0..n]]
matchesMaybe _ _ = Nothing

matches :: Expression -> Expression -> Maybe [Expression]
matches e1 e2 = matchesMaybe e1 e2 >>= sequence
