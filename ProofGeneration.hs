module ProofGeneration (applyDeductionPreserve, proveStmt, findUnproved, traceExpr) where

import Expression hiding (merge)
import Proof
import MonadProof

import Data.List
import Data.Maybe
import Data.ByteString.Char8 (ByteString)

import Debug.Trace

import Control.Monad
import Control.Monad.ST

fillProof :: ProofStatement -> [Expression] -> ProofStatement
fillProof (Unproved expr num) list = Unproved (fillInGaps expr list) num
fillProof (Axiom expr num) list = Axiom (fillInGaps expr list) num
fillProof (ModusPonens expr left right num) list = ModusPonens (fillInGaps expr list) (fillProof left list) (fillProof right list) num

a = Gap 0
b = Gap 1
c = Gap 2

proofAG :: ProofStatement
proofAG = getLast $ do
    tellEx $ a --> b
    tellEx $ a --> b --> c
    tellEx $ (a --> b) --> (a --> b --> c) --> (a --> c)
    tellEx $ (a --> b --> c) --> (a --> c)
    tellEx $ a --> c

proofAA :: ProofStatement
proofAA = getLast $ do
    tellEx $ a --> a --> a
    tellEx $ a --> (a --> a) --> a
    tellSt $ fillProof proofAG [a, a --> a, a]

proofBA :: ProofStatement
proofBA = getLast $ do
    tellEx $ b
    tellEx $ b --> a --> b
    tellEx $ a --> b

dfs stmt expr = case stmt of
    Unproved unpr _ -> if unpr == expr
        then tellSt $ fillProof proofAA [expr]
        else tellSt $ fillProof proofBA [expr, unpr]
    Axiom axm _ -> tellSt $ fillProof proofBA [expr, axm]
    ModusPonens mpe left right _ -> do
        dfs left expr
        dfs right expr
        tellSt $ fillProof proofAG [expr, getExpression left, getRight $ getExpression right]

applyDeductionPreserve :: [ProofStatement] -> Expression -> [ProofStatement]
applyDeductionPreserve list expr = getFixed $ forM list (`dfs` expr)

applyDeduction :: Expression -> ProofStatement -> ProofStatement
applyDeduction expr res = getLast $ dfs res expr

contraposition = applyDeduction (a --> b) $ applyDeduction (Not b) $ getLast $ do
    tellEx $ a --> b
    tellEx $ Not b
    tellSt $ fillProof proofBA [a, Not b]
    tellEx $ (a --> b) --> (a --> Not b) --> Not a
    tellEx $ (a --> Not b) --> Not a
    tellEx $ Not a

deMorganOr = applyDeduction (Not (a ||| b)) $ getLast $ do
    tellEx $ Not (a ||| b)
    tellEx $ a --> a ||| b
    tellSt $ fillProof proofBA [a, Not (a ||| b)]
    tellEx $ (a --> a ||| b) --> (a --> Not (a ||| b)) --> Not a
    tellEx $ (a --> Not (a ||| b)) --> Not a
    tellEx $ Not a
    tellEx $ b --> a ||| b
    tellSt $ fillProof proofBA [b, Not (a ||| b)]
    tellEx $ (b --> a ||| b) --> (b --> Not (a ||| b)) --> Not b
    tellEx $ (b --> Not (a ||| b)) --> Not b
    tellEx $ Not b
    tellEx $ Not a --> Not b --> Not a &&& Not b
    tellEx $ Not b --> Not a &&& Not b
    tellEx $ Not a &&& Not b

aOrNotA = getLast $ do
    tellSt $ fillProof deMorganOr [a, Not a]
    tellEx $ Not a &&& Not (Not a) --> Not a
    tellSt $ fillProof proofBA [Not (a ||| Not a), Not a &&& Not (Not a) --> Not a]
    tellSt $ fillProof proofAG [Not (a ||| Not a), Not a &&& Not (Not a), Not a]
    tellEx $ Not a &&& Not (Not a) --> Not (Not a)
    tellEx $ Not (Not a)
    tellSt $ fillProof proofBA [Not (a ||| Not a), Not a &&& Not (Not a) --> Not (Not a)]
    tellSt $ fillProof proofAG [Not (a ||| Not a), Not a &&& Not (Not a), Not (Not a)]
    tellEx $ (Not (a ||| Not a) --> Not a) --> (Not (a ||| Not a) --> Not (Not a)) --> Not (Not (a ||| Not a))
    tellEx $ (Not (a ||| Not a) --> Not (Not a)) --> Not (Not (a ||| Not a))
    tellEx $ Not (Not (a ||| Not a))
    tellEx $ Not (Not (a ||| Not a)) --> a ||| Not a
    tellEx $ a ||| Not a

implicationIsOr = applyDeduction (a --> b) $ getLast $ do
    tellEx $ a --> b
    tellSt $ contraposition
    tellEx $ Not b --> Not a
    tellEx $ Not a --> Not a ||| b
    tellEx $ b --> Not a ||| b
    tellSt $ fillProof proofBA [b, Not a --> Not a ||| b]
    tellSt $ fillProof proofAG [b, Not a, Not a ||| b]
    tellSt $ fillProof proofBA [Not b, Not a --> Not a ||| b]
    tellSt $ fillProof proofAG [Not b, Not a, Not a ||| b]
    tellEx $ (b --> Not a ||| b) --> (Not b --> Not a ||| b) --> b ||| Not b --> Not a ||| b
    tellEx $ (Not b --> Not a ||| b) --> b ||| Not b --> Not a ||| b
    tellEx $ b ||| Not b --> Not a ||| b
    tellSt $ fillProof aOrNotA [b]
    tellEx $ Not a ||| b

deMorganAnd = applyDeduction (Not (a &&& b)) $ getLast $ do
    tellEx $ Not (a &&& b)
    tellSt $ applyDeduction a $ getLast $ do
        tellEx $ a
        tellEx $ a --> b --> a &&& b
        tellEx $ b --> a &&& b
        tellSt $ fillProof proofBA [b, Not (a &&& b)]
        tellEx $ (b --> a &&& b) --> (b --> Not (a &&& b)) --> Not b
        tellEx $ (b --> Not (a &&& b)) --> Not b
        tellEx $ Not b
    tellEx $ Not a --> Not a ||| Not b
    tellEx $ Not b --> Not a ||| Not b
    tellSt $ fillProof proofBA [a, Not b --> Not a ||| Not b]
    tellSt $ fillProof proofAG [a, Not b, Not a ||| Not b]
    tellEx $ (a --> Not a ||| Not b) --> (Not a --> Not a ||| Not b) --> a ||| Not a --> Not a ||| Not b
    tellEx $ (Not a --> Not a ||| Not b) --> a ||| Not a --> Not a ||| Not b
    tellEx $ a ||| Not a --> Not a ||| Not b
    tellSt $ aOrNotA
    tellEx $ Not a ||| Not b

intuitionist = applyDeduction (Not a) $ applyDeduction a $ getLast $ do
    tellEx $ Not a
    tellEx $ a
    tellSt $ fillProof proofBA [Not b, a]
    tellSt $ fillProof proofBA [Not b, Not a]
    tellEx $ (Not b --> a) --> (Not b --> Not a) --> Not (Not b)
    tellEx $ (Not b --> Not a) --> Not (Not b)
    tellEx $ Not (Not b)
    tellEx $ Not (Not b) --> b
    tellEx $ b

notImplIsAnd = applyDeduction (Not (a --> b)) $ getLast $ do
    tellEx $ Not (a --> b)
    tellSt $ fillProof proofBA [Not a, Not (a --> b)]
    tellSt $ intuitionist
    tellEx $ (Not a --> a --> b) --> (Not a --> Not (a --> b)) --> Not (Not a)
    tellEx $ (Not a --> Not (a --> b)) --> Not (Not a)
    tellEx $ Not (Not a)
    tellEx $ Not (Not a) --> a
    tellEx $ a
    tellSt $ fillProof proofBA [b, Not (a --> b)]
    tellEx $ b --> a --> b
    tellEx $ (b --> a --> b) --> (b --> Not (a --> b)) --> Not b
    tellEx $ (b --> Not (a --> b)) --> Not b
    tellEx $ Not b
    tellEx $ a --> Not b --> a &&& Not b
    tellEx $ Not b --> a &&& Not b
    tellEx $ a &&& Not b

inMorganOr = getLast $ do
    let notAIsNotAnd wa = applyDeduction (Not wa) $ getLast $ do
        tellEx $ Not wa
        tellEx $ a &&& b --> wa
        tellSt $ fillProof proofBA [a &&& b, Not wa]
        tellEx $ (a &&& b --> wa) --> (a &&& b --> Not wa) --> Not (a &&& b)
        tellEx $ (a &&& b --> Not wa) --> Not (a &&& b)
        tellEx $ Not (a &&& b)
    tellSt $ notAIsNotAnd a
    tellSt $ notAIsNotAnd b
    tellEx $ (Not a --> Not (a &&& b)) --> (Not b --> Not (a &&& b)) --> (Not a ||| Not b --> Not (a &&& b))
    tellEx $ (Not b --> Not (a &&& b)) --> (Not a ||| Not b --> Not (a &&& b))
    tellEx $ Not a ||| Not b --> Not (a &&& b)

addNotNot = applyDeduction a $ getLast $ do
    tellEx $ a
    tellSt $ fillProof proofAA [Not a]
    tellSt $ fillProof proofBA [Not a, a]
    tellEx $ (Not a --> a) --> (Not a --> Not a) --> Not (Not a)
    tellEx $ (Not a --> Not a) --> Not (Not a)
    tellEx $ Not (Not a)

addNotNotToOr = getLast $ do
    tellSt $ addNotNot
    tellEx $ Not (Not a) --> Not (Not a) ||| Not (Not b)
    tellSt $ fillProof proofBA [a, Not (Not a) --> Not (Not a) ||| Not (Not b)]
    tellSt $ fillProof proofAG [a, Not (Not a), Not (Not a) ||| Not (Not b)]
    tellSt $ fillProof addNotNot [b]
    tellEx $ Not (Not b) --> Not (Not a) ||| Not (Not b)
    tellSt $ fillProof proofBA [b, Not (Not b) --> Not (Not a) ||| Not (Not b)]
    tellSt $ fillProof proofAG [b, Not (Not b), Not (Not a) ||| Not (Not b)]
    tellEx $ (a --> Not (Not a) ||| Not (Not b)) --> (b --> Not (Not a) ||| Not (Not b)) --> a ||| b --> Not (Not a) ||| Not (Not b)
    tellEx $ (b --> Not (Not a) ||| Not (Not b)) --> a ||| b --> Not (Not a) ||| Not (Not b)
    tellEx $ a ||| b --> Not (Not a) ||| Not (Not b)

notAThenB = applyDeduction (a ||| b) $ applyDeduction (Not a) $ getLast $ do
    tellEx $ a ||| b
    tellEx $ Not a
    tellSt $ addNotNotToOr
    tellEx $ Not (Not a) ||| Not (Not b)
    tellSt $ fillProof inMorganOr [Not a, Not b]
    tellEx $ Not (Not a &&& Not b)
    tellEx $ Not a --> Not b --> Not a &&& Not b
    tellEx $ Not b --> Not a &&& Not b
    tellSt $ fillProof proofBA [Not b, Not (Not a &&& Not b)]
    tellEx $ (Not b --> Not a &&& Not b) --> (Not b --> Not (Not a &&& Not b)) --> Not (Not b)
    tellEx $ (Not b --> Not (Not a &&& Not b)) --> Not (Not b)
    tellEx $ Not (Not b)
    tellEx $ Not (Not b) --> b
    tellEx $ b

-- TODO Maybe there is a simple proof
inMorganAnd = applyDeduction (Not a &&& Not b) $ getLast $ do
    tellEx $ Not a &&& Not b
    tellEx $ Not a &&& Not b --> Not a
    tellEx $ Not a
    tellSt $ fillProof proofBA [a ||| b, Not a]
    tellSt $ notAThenB
    tellSt $ fillProof proofAG [a ||| b, Not a, b]
    tellEx $ Not a &&& Not b --> Not b
    tellEx $ Not b
    tellSt $ fillProof proofBA [a ||| b, Not b]
    tellEx $ (a ||| b --> b) --> (a ||| b --> Not b) --> Not (a ||| b)
    tellEx $ (a ||| b --> Not b) --> Not (a ||| b)
    tellEx $ Not (a ||| b)

notAndIsImpl = applyDeduction (a &&& Not b) $ getLast $ do
    tellEx $ a &&& Not b
    tellEx $ a &&& Not b --> a
    tellEx $ a
    tellSt $ fillProof proofBA [a --> b, a]
    tellSt $ fillProof proofAA [a --> b]
    tellSt $ fillProof proofAG [a --> b, a, b]
    tellEx $ a &&& Not b --> Not b
    tellEx $ Not b
    tellSt $ fillProof proofBA [a --> b, Not b]
    tellEx $ ((a --> b) --> b) --> ((a --> b) --> Not b) --> Not (a --> b)
    tellEx $ ((a --> b) --> Not b) --> Not (a --> b)
    tellEx $ Not (a --> b)

notAThenBIsOr = getLast $ do
    tellSt $ fillProof contraposition [Not (a ||| b), Not (Not a --> b)]
    tellSt $ applyDeduction (Not (a ||| b)) $ getLast $ do
        tellEx $ Not (a ||| b)
        tellSt $ deMorganOr
        tellEx $ Not a &&& Not b
        tellSt $ fillProof notAndIsImpl [Not a, b]
        tellEx $ Not (Not a --> b)
    tellEx $ Not (Not (Not a --> b)) --> Not (Not (a ||| b))
    tellSt $ fillProof addNotNot [Not a --> b]
    tellSt $ fillProof proofBA [Not a --> b, Not (Not (Not a --> b)) --> Not (Not (a ||| b))]
    tellSt $ fillProof proofAG [Not a --> b, Not (Not (Not a --> b)), Not (Not (a ||| b))]
    tellEx $ Not (Not (a ||| b)) --> a ||| b
    tellSt $ fillProof proofBA [Not a --> b, Not (Not (a ||| b)) --> a ||| b]
    tellSt $ fillProof proofAG [Not a --> b, Not (Not (a ||| b)), a ||| b]

proveStmt :: Monad m => Expression -> ProofT m ()
proveStmt toBeProved@(Implication left right) = case left of
    And andL andR -> do
        tellEx $ left --> andL
        tellEx $ left --> andR
        proveStmt $ andL --> andR --> right
        tellSt $ fillProof proofBA [left, andL --> andR --> right]
        tellSt $ fillProof proofAG [left, andL, andR --> right]
        tellSt $ fillProof proofBA [left, andR --> right]
        tellSt $ fillProof proofAG [left, andR, right]
    Or orL orR -> do
        -- FIXME Something from the left may be always false
        proveStmt $ orL --> right
        proveStmt $ orR --> right
        tellEx $ (orL --> right) --> (orR --> right) --> orL ||| orR --> right
        tellEx $ (orR --> right) --> orL ||| orR --> right
        tellEx $ orL ||| orR --> right
    Implication implL implR -> do
        tellSt $ fillProof implicationIsOr [implL, implR]
        proveStmt $ Not implL ||| implR --> right
        tellSt $ fillProof proofBA [left, Not implL ||| implR --> right]
        tellSt $ fillProof proofAG [left, Not implL ||| implR, right]
    Not (Or orL orR) -> do
        tellSt $ fillProof deMorganOr [orL, orR]
        proveStmt $ Not orL &&& Not orR --> right
        tellSt $ fillProof proofBA [left, Not orL &&& Not orR --> right]
        tellSt $ fillProof proofAG [left, Not orL &&& Not orR, right]
    Not (And andL andR) -> do
        tellSt $ fillProof deMorganAnd [andL, andR]
        proveStmt $ Not andL ||| Not andR --> right
        tellSt $ fillProof proofBA [left, Not andL ||| Not andR --> right]
        tellSt $ fillProof proofAG [left, Not andL ||| Not andR, right]
    Not (Implication implL implR) -> do
        tellSt $ fillProof notImplIsAnd [implL, implR]
        proveStmt $ implL &&& Not implR --> right
        tellSt $ fillProof proofBA [left, implL &&& Not implR --> right]
        tellSt $ fillProof proofAG [left, implL &&& Not implR, right]
    Not (Not p) -> do
        tellEx $ Not (Not p) --> p
        proveStmt $ p --> right
        tellSt $ fillProof proofBA [Not (Not p), p --> right]
        tellSt $ fillProof proofAG [Not (Not p), p, right]
    _ -> tellSt $ applyDeduction left $ getLast $ do
        -- TODO And how about Not?
        tellEx left
        proveStmt right
proveStmt toBeProved@(And left right) = do
    tellEx $ left
    tellEx $ right
    tellEx $ left --> right --> left &&& right
    tellEx $ right --> left &&& right
    tellEx $ toBeProved
proveStmt toBeProved@(Or left right) = do
    proveStmt $ Not left --> right
    tellSt $ fillProof notAThenBIsOr [left, right]
    tellEx $ toBeProved
proveStmt toBeProved@(Not param) = case param of
    And andL andR -> do
        proveStmt $ Not andL ||| Not andR
        tellSt $ fillProof inMorganOr [andL, andR]
        tellEx $ toBeProved
    Or orL orR -> do
        proveStmt $ Not orL &&& Not orR
        tellSt $ fillProof inMorganAnd [orL, orR]
        tellEx $ toBeProved
    Implication implL implR -> do
        proveStmt $ implL &&& Not implR
        tellSt $ fillProof notAndIsImpl [implL, implR]
        tellEx $ toBeProved
    Not p -> do
        tellSt $ fillProof addNotNot [p]
        proveStmt $ p
        tellEx $ toBeProved
    _ -> tellEx toBeProved
proveStmt toBeProved = tellEx toBeProved

findUnproved :: ProofStatement -> Maybe ProofStatement
findUnproved (Axiom _ _) = Nothing
findUnproved (ModusPonens _ l r _ ) = findUnproved l `mplus` findUnproved r
findUnproved res@(Unproved expr _) = Just res

traceExpr :: Expression -> Maybe [(ByteString, Bool)]
traceExpr expr =
    let gather (Var s) = [s]
        gather (Not p) = gather p
        gather (And l r) = union (gather l) (gather r)
        gather (Or l r) = union (gather l) (gather r)
        gather (Implication l r) = union (gather l) (gather r)

        check (Var s) list b = b == (fromJust $ lookup s list)
        check (Not p) list b = check p list $ not b
        check (And l r) list True = check l list True && check r list True
        check (And l r) list False = check l list False || check r list False
        check (Or l r) list True = check l list True || check r list True
        check (Or l r) list False = check l list False && check r list False
        check (Implication l r) list True = check l list False || check r list True
        check (Implication l r) list False = check l list True && check r list  False

        findValues [] expr list = guard (check expr list False) >> return list
        findValues (f:s) expr list = findValues s expr ((f, False):list) `mplus` findValues s expr ((f, True):list)
    in findValues (gather expr) expr []
