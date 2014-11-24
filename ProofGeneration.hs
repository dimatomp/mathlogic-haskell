module ProofGeneration (applyDeduction, applyDeductionPreserve) where

import Expression
import Proof
import MonadProof

import Data.Maybe

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
proofAG = runST $ getLast $ do
    tellEx $ a --> b
    tellEx $ a --> b --> c
    tellEx $ (a --> b) --> (a --> b --> c) --> (a --> c)
    tellEx $ (a --> b --> c) --> (a --> c)
    tellEx $ a --> c

proofAA :: ProofStatement
proofAA = runST $ getLast $ do
    tellEx $ a --> a --> a
    tellEx $ a --> (a --> a) --> a
    tellSt $ fillProof proofAG [a, a --> a, a]

proofBA :: ProofStatement
proofBA = runST $ getLast $ do
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
applyDeductionPreserve list expr = runST $ getFixed $ forM list (`dfs` expr) 

applyDeduction :: Expression -> ProofStatement -> ProofStatement
applyDeduction expr res = runST $ getLast $ dfs res expr

contraposition = applyDeduction (a --> b) $ applyDeduction (Not b) $ runST $ getLast $ do
    tellEx $ a --> b 
    tellEx $ Not b
    tellSt $ fillProof proofBA [a, Not b]
    tellEx $ (a --> b) --> (a --> Not b) --> Not a 
    tellEx $ (a --> Not b) --> Not a
    tellEx $ Not a

deMorganOr = applyDeduction (Not (a ||| b)) $ runST $ getLast $ do
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

aOrNotA = runST $ getLast $ do
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

implicationIsOr = applyDeduction (a --> b) $ runST $ getLast $ do
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

deMorganAnd = applyDeduction (Not (a &&& b)) $ runST $ getLast $ do
    tellEx $ Not (a &&& b)
    tellSt $ applyDeduction a $ runST $ getLast $ do
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

intuitionist = applyDeduction (Not a) $ applyDeduction a $ runST $ getLast $ do
    tellEx $ Not a
    tellEx $ a
    tellSt $ fillProof proofBA [Not b, a]
    tellSt $ fillProof proofBA [Not b, Not a]
    tellEx $ Not b --> a --> Not b --> Not a --> Not (Not b)
    tellEx $ (Not b --> Not a) --> Not (Not b)
    tellEx $ Not (Not b)
    tellEx $ Not (Not b) --> b
    tellEx $ b

{-
notImplIsAnd = do
    builder <- newBuilder
    tellEx $ Not (a --> b)
    tellSt $ fillProof proofBA [Not a, Not (a --> b)]
    intuitionist >>= addProof builder
    tellEx $ fillInGaps axiomABA_NOT_B_NOT_A [Not a, a --> b]
    tellEx $ (Not a --> Not (a --> b)) --> Not (Not a)
    tellEx $ Not (Not a)
    tellEx $ fillInGaps axiomNOT_NOT_AA [a]
    tellEx $ a
    tellSt $ fillProof proofBA [b, Not (a --> b)]
    tellEx $ fillInGaps axiomABA [b, a]
    tellEx $ fillInGaps axiomABA_NOT_B_NOT_A [b, a --> b]
    tellEx $ (b --> Not (a --> b)) --> Not b
    tellEx $ Not b
    tellEx $ fillInGaps axiomABA_AND_B [a, Not b]
    tellEx $ Not b --> a &&& Not b
    tellEx (a &&& Not b) >>= (`applyDeduction` [Not (a --> b)])

inMorganOr = do
    let notAIsNotAnd wa = do
            builder <- newBuilder
            tellEx $ Not wa
            tellEx $ a &&& b --> wa
            tellSt $ fillProof proofBA [a &&& b, Not wa]
            tellEx $ fillInGaps axiomABA_NOT_B_NOT_A [a &&& b, wa]
            tellEx $ (a &&& b --> Not wa) --> Not (a &&& b)
            tellEx (Not (a &&& b)) >>= (`applyDeduction` [Not wa])
    builder <- newBuilder
    notAIsNotAnd a >>= addProof builder
    notAIsNotAnd b >>= addProof builder
    tellEx $ fillInGaps axiomAGBGA_OR_BG [Not a, Not b, Not (a &&& b)]
    tellEx $ (Not b --> Not (a ||| b)) --> (Not a ||| Not b --> Not (a &&& b))
    tellEx $ Not a ||| Not b --> Not (a &&& b)

addNotNot = do
    builder <- newBuilder
    tellEx $ a
    tellEx $ fillInGaps axiomABA [Not a, Not a]
    tellEx $ fillInGaps axiomABA [Not a, Not a --> Not a]
    tellSt $ fillProof proofAG [Not a, Not a --> Not a, Not a]
    tellSt $ fillProof proofBA [Not a, a]
    tellEx $ fillInGaps axiomABA_NOT_B_NOT_A [Not a, a]
    tellEx $ (Not a --> Not a) --> Not (Not a)
    tellEx (Not (Not a)) >>= (`applyDeduction` [a])

proveStmt :: Expression -> IO ProofStatement
proveStmt toBeProved@(Implication left right) = case left of
    And andL andR -> do
        builder <- newBuilder
        tellEx $ left --> andL
        tellEx $ left --> andR
        proveStmt right >>= (`applyDeduction` [andR, andL]) >>= addProof builder
        tellSt $ fillProof proofBA [left, andL --> andR --> right]
        tellSt $ fillProof proofAG [left, andL, andR --> right]
        tellSt $ fillProof proofBA [left, andR --> right]
        tellSt $ fillProof proofAG [left, andR, right]
        findProof builder toBeProved
    Or orL orR -> do
        builder <- newBuilder
        (proveStmt $ orL --> right) >>= addProof builder
        (proveStmt $ orR --> right) >>= addProof builder
        tellEx $ fillInGaps axiomAGBGA_OR_BG [orL, orR, right]
        tellEx $ (orR --> right) --> toBeProved
        tellEx toBeProved
    Implication implL implR -> do
        builder <- newBuilder
        liftM (`fillProof` [implL, implR]) implicationIsOr >>= addProof builder
        let fromOr = Not implL ||| implR --> right
        proofStmt fromOr >>= addProof builder
        tellSt $ fillProof proofBA [left, fromOr]
        tellSt $ fillProof proofAG [left, Not implL ||| implR, implR]
        findProof builder toBeProved
    Not (Or orL orL) -> do
        builder <- newBuilder
        liftM (`fillProof` [orL, orR]) deMorganOr >>= addProof builder
        let fromAnd = Not orL &&& Not orR --> right
        proveStmt fromAnd >>= addProof builder
        tellSt $ fillProof proofBA [left, fromAnd]
        tellSt $ fillProof proofAG [left, Not orL &&& Not orR, right]
        findProof builder toBeProved
    Not (And andL andR) -> do
        builder <- newBuilder
        liftM (`fillProof` [andL, andR]) deMorganAnd >>= addProof builder
        let fromOr = Not andL ||| Not andR --> right
        proveStmt fromOr >>= addProof builder
        tellSt $ fillProof proofBA [left, fromOr]
        tellSt $ fillProof proofAG [left, Not andL ||| Not andR, right]
        findProof builder toBeProved
    Not (Implication implL implR) -> do
        builder <- newBuilder
        liftM (`fillProof` [implL, implR]) notImplIsAnd >>= addProof builder
        let fromAnd = implL &&& Not implR --> right
        proveStmt fromAnd >>= addProof builder
        tellSt $ fillProof proofBA [left, fromAnd]
        tellSt $ fillProof proofAG [left, implL &&& Not implR, right]
        findProof builder toBeProved
    _ -> proveStmt right >>= (`applyDeduction` [left])
proveStmt toBeProved@(And left right) = do
    builder <- newBuilder
    tellEx left
    tellEx right
    tellEx $ fillInGaps axiomABA_AND_B [left, right]
    tellEx $ right --> left &&& right
    tellEx toBeProved
proveStmt toBeProved@(Or left right) = do
    builder <- newBuilder
    tellEx left
    tellEx right
    tellEx $ fillInGaps axiomAA_OR_B [left, right]
    tellEx $ fillInGaps axiomBA_OR_B [left, right]
    tellEx toBeProved
proveStmt toBeProved@(Not param) = case param of
    And andL andR -> do
        builder <- newBuilder
        let orSt = Not andL ||| Not andR
        proveStmt orSt >>= addProof builder
        liftM (`fillProof` [andL, andR]) inMorganOr >>= addProof builder
        tellEx toBeProved
    Or orL orR -> do
        builder <- newBuilder
        proveStmt (Not orL) >>= addProof builder
        proveStmt (Not orR) >>= addProof builder
        tellEx $ fillInGaps axiomABA_AND_B [Not orL, Not orR]
        tellEx $ Not orR --> Not orL &&& Not orR
        tellEx $ Not orL &&& Not orR
        undefined-}
