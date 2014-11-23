module ProofGeneration (applyDeduction, applyDeductionPreserve) where

import Expression
import Axioms
import Proof

import Data.Maybe

import Control.Monad
import Control.Monad.ST

fillProof :: ProofStatement -> [Expression] -> ProofStatement
fillProof (Unproved expr num) list = Unproved (fillInGaps expr list) num
fillProof (Axiom expr num) list = Axiom (fillInGaps expr list) num
fillProof (ModusPonens expr left right num) list = ModusPonens (fillInGaps expr list) (fillProof left list) (fillProof right list) num

redImp :: ProofBuilder s -> Expression -> ST s ProofStatement
redImp builder impl@(Implication left right) = do
    nextSt builder impl 
    nextSt builder left
    redImp builder right
redImp builder other = nextSt builder other 

redImp1 :: ProofBuilder s -> Expression -> ST s ProofStatement
redImp1 builder impl@(Implication left right@(Implication _ _)) = do
    nextSt builder impl 
    nextSt builder left
    redImp1 builder right
redImp1 builder impl@(Implication _ _) = nextSt builder impl

dfs builder stmt expr = do 
    alreadyThere <- findProof builder $ expr --> (getExpression stmt)
    case alreadyThere of
        Unproved _ _ -> case stmt of
            Unproved unpr _ -> if unpr == expr
                then do
                    nextSt builder $ fillInGaps axiomABA [expr, expr]
                    nextSt builder $ fillInGaps axiomABA [expr, expr --> expr]
                    redImp1 builder $ fillInGaps axiomABABGAG [expr, expr --> expr, expr]
                else do
                    nextSt builder unpr
                    redImp1 builder (fillInGaps axiomABA [unpr, expr]) 
            Axiom axm _ -> do
                nextSt builder axm
                redImp1 builder (fillInGaps axiomABA [axm, expr]) 
            ModusPonens mpe left right _ -> do
                exprLeft <- dfs builder left expr
                exprRight <- dfs builder right expr
                redImp1 builder $ exprLeft --> exprRight --> expr --> mpe
        _ -> return alreadyThere
    return $ expr --> (getExpression stmt)

applyDeductionPreserve :: [ProofStatement] -> Expression -> [ProofStatement]
applyDeductionPreserve list expr = runST $ do
    builder <- newBuilder
    forM_ list $ \stmt -> dfs builder stmt expr
    getFixedProof builder $ map ((expr -->) . getExpression) list

applyDeduction :: ProofStatement -> Expression -> ProofStatement
applyDeduction res expr = runST $ do
    builder <- newBuilder
    dfs builder res expr >>= findProof builder 
{-
a = Gap 0
b = Gap 1

contraposition = do
    myBuilder <- newBuilder
    nextSt myBuilder $ a --> b -- (-1)
    nextSt myBuilder $ Not b -- (0)
    addSequence myBuilder proofBA [a, Not b] -- (1) M.P. 0
    nextSt myBuilder $ fillInGaps axiomABA_NOT_B_NOT_A [a, b] -- (2)
    nextSt myBuilder $ (a --> Not b) --> Not a -- (3) M.P. -1
    nextSt myBuilder (Not a) >>= (`applyDeduction` [Not b]) 

deMorganOr = do
    myBuilder <- newBuilder
    nextSt myBuilder $ Not (a ||| b) -- (0)
    nextSt myBuilder $ fillInGaps axiomAA_OR_B [a, b] -- (1) a --> a ||| b [axiom]
    addSequence myBuilder proofBA [a, Not (a ||| b)] -- (2) a --> Not (a ||| b) [M.P. 0, axiom]
    nextSt myBuilder $ fillInGaps axiomABA_NOT_B_NOT_A [a, a ||| b] -- (3) (a --> a ||| b) --> (a --> Not (a --> b)) --> Not a [axiom]
    nextSt myBuilder $ (a --> Not (a ||| b)) --> Not a -- (4) (a --> Not (a ||| b)) --> Not a [M.P. 1, 3]
    nextSt myBuilder $ Not a -- (5) Not a [M.P. 2, 4]
    nextSt myBuilder $ fillInGaps axiomBA_OR_B [a, b] -- (6) b --> a ||| b [axiom]
    addSequence myBuilder proofBA [b, Not (a ||| b)] -- (7) b --> Not (a ||| b) [M.P. 0, axiom]
    nextSt myBuilder $ fillInGaps axiomABA_NOT_B_NOT_A [b, a ||| b] -- (8) (b --> a ||| b) --> (b --> Not (a --> b)) --> Not b [axiom]
    nextSt myBuilder $ (b --> Not (a ||| b)) --> Not b -- (9) (b --> Not (a ||| b)) --> Not b [M.P. 6, 8]
    nextSt myBuilder $ Not b -- (10) Not b [M.P. 7, 9]
    nextSt myBuilder $ fillInGaps axiomABA_AND_B [Not a, Not b] -- (11) Not a --> Not b --> Not a &&& Not b [axiom]
    nextSt myBuilder $ Not b --> Not a &&& Not b -- (12) Not b --> Not a &&& Not b [M.P. 5, 11]
    nextSt myBuilder $ Not a &&& Not b >>= (`applyDeduction` [Not (a ||| b)]) -- (13) Not a &&& Not b [M.P. 10, 12]

aOrNotA = do
    builder <- newBuilder
    liftM (`fillProof` [a, Not a]) deMorganOr >>= addProof builder -- (1) Not (a ||| Not a) --> Not a &&& Not (Not a) [see above]
    let unpackAnd = fillInGaps axiomA_AND_BA [Not a, Not (Not a)]
    nextSt builder unpackAnd -- (2) Not a &&& Not (Not a) --> Not a [axiom]
    nextSt builder $ Not a -- (3) Not a [M.P. , 2]
    addSequence builder proofBA [Not (a ||| Not a), unpackAnd]
    addSequence builder proofAG [Not (a ||| Not a), getLeft unpackAnd, getRight unpackAnd]
    addSequence builder $ (Not (a ||| Not a) --> unpackAnd) --> Not (a ||| Not a) --> Not a
    addSequence builder $ Not (a ||| Not a) --> Not a
    let unpackAnd = fillInGaps axiomA_AND_BB [Not a, Not (Not a)]
    nextSt builder unpackAnd
    nextSt builder $ Not (Not a)
    addSequence builder proofBA [Not (a ||| Not a), unpackAnd]
    addSequence builder proofAG [Not (a ||| Not a), getLeft unpackAnd, getRight unpackAnd]
    addSequence builder $ (Not (a ||| Not a) --> unpackAnd) --> Not (a ||| Not a) --> Not (Not a)
    addSequence builder $ Not (a ||| Not a) --> Not (Not a)
    nextSt builder $ fillInGaps axiomABA_NOT_B_NOT_A [Not (a ||| Not a), Not a]
    nextSt builder $ (Not (a ||| Not a) --> Not (Not a)) --> Not (Not (a ||| Not a))
    nextSt builder $ Not (Not (a ||| Not a))
    nextSt builder $ fillInGaps axiomNOT_NOT_AA [a ||| Not a]
    nextSt builder $ a ||| Not a

implicationIsOr = do
    builder <- newBuilder
    contraposition >>= addProof builder
    let fromNotA = fillInGaps axiomAA_OR_B [Not a, b]
    nextSt builder fromNotA
    addSequence builder proofBA [b, fromNotA]
    addSequence builder proofAG [b, Not a, Not a ||| b]
    addSequence builder proofBA [Not b, fromNotA]
    addSequence builder proofAG [Not b, Not a, Not a ||| b]
    nextSt builder $ fillInGaps axiomAGBGA_OR_BG [b, Not b, Not a ||| b]
    nextSt builder $ (Not b --> Not a ||| b) --> (b ||| Not b --> Not a ||| b)
    nextSt builder $ b ||| Not b --> Not a ||| b
    liftM (`fillProof` [b]) aOrNotA >>= addProof builder
    nextSt builder (Not a ||| b) >>= (`applyDeduction` [a --> b])

deMorganAnd = do
    let proofFromA = do
            builder <- newBuilder
            nextSt builder a
            nextSt builder $ fillInGaps axiomABA_AND_B [a, b]
            nextSt builder $ b --> a &&& b
            addSequence builder proofBA [b, Not (a &&& b)]
            nextSt builder $ fillInGaps axiomABA_NOT_B_NOT_A [b, a &&& b]
            nextSt builder $ (b --> Not (a &&& b))) --> Not b
            nextSt builder (Not b) >>= (`applyDeduction` a)
    builder <- newBuilder
    nextSt builder $ Not (a &&& b)
    proofFromA >>= addProof
    nextSt builder $ fillInGaps axiomAA_OR_B [Not a, Not b]
    let fromB = fillInGaps axiomBA_OR_B [Not a, Not b]
    nextSt builder fromB
    addSequence builder proofBA [a, fromB]
    addSequence builder proofAG [a, Not b, Not a ||| Not b]
    nextSt builder $ fillInGaps axiomAGBGA_OR_BG [a, Not a, Not a ||| Not b]
    nextSt builder $ (Not a --> Not a ||| Not b) --> (a ||| Not a --> Not a ||| Not b)
    nextSt builder $ a ||| Not a --> Not a ||| Not b
    aOrNotA >>= addProof builder
    nextSt builder (Not a ||| Not b) >>= (`applyDeduction` (Not (a &&& b)))

intuitionist = do
    builder <- newBuilder
    nextSt builder $ Not a
    nextSt builder $ a
    addSequence builder proofBA [Not b, a]
    addSequence builder proofBA [Not b, Not a]
    nextSt builder $ fillInGaps axiomABA_NOT_B_NOT_A [Not b, a]
    nextSt builder $ (Not b --> Not a) --> Not (Not b)
    nextSt builder $ Not (Not b)
    nextSt builder $ fillInGaps axiomNOT_NOT_AA [b]
    nextSt builder b >>= (`applyDeduction` [a, Not a])

notImplIsAnd = do
    builder <- newBuilder
    nextSt builder $ Not (a --> b)
    addSequence builder proofBA [Not a, Not (a --> b)]
    intuitionist >>= addProof builder
    nextSt builder $ fillInGaps axiomABA_NOT_B_NOT_A [Not a, a --> b]
    nextSt builder $ (Not a --> Not (a --> b)) --> Not (Not a)
    nextSt builder $ Not (Not a)
    nextSt builder $ fillInGaps axiomNOT_NOT_AA [a]
    nextSt builder $ a
    addSequence builder proofBA [b, Not (a --> b)]
    nextSt builder $ fillInGaps axiomABA [b, a]
    nextSt builder $ fillInGaps axiomABA_NOT_B_NOT_A [b, a --> b]
    nextSt builder $ (b --> Not (a --> b)) --> Not b
    nextSt builder $ Not b
    nextSt builder $ fillInGaps axiomABA_AND_B [a, Not b]
    nextSt builder $ Not b --> a &&& Not b
    nextSt builder (a &&& Not b) >>= (`applyDeduction` [Not (a --> b)])

inMorganOr = do
    let notAIsNotAnd wa = do
            builder <- newBuilder
            nextSt builder $ Not wa
            nextSt builder $ a &&& b --> wa
            addSequence builder proofBA [a &&& b, Not wa]
            nextSt builder $ fillInGaps axiomABA_NOT_B_NOT_A [a &&& b, wa]
            nextSt builder $ (a &&& b --> Not wa) --> Not (a &&& b)
            nextSt builder (Not (a &&& b)) >>= (`applyDeduction` [Not wa])
    builder <- newBuilder
    notAIsNotAnd a >>= addProof builder
    notAIsNotAnd b >>= addProof builder
    nextSt builder $ fillInGaps axiomAGBGA_OR_BG [Not a, Not b, Not (a &&& b)]
    nextSt builder $ (Not b --> Not (a ||| b)) --> (Not a ||| Not b --> Not (a &&& b))
    nextSt builder $ Not a ||| Not b --> Not (a &&& b)

addNotNot = do
    builder <- newBuilder
    nextSt builder $ a
    nextSt builder $ fillInGaps axiomABA [Not a, Not a]
    nextSt builder $ fillInGaps axiomABA [Not a, Not a --> Not a]
    addSequence builder proofAG [Not a, Not a --> Not a, Not a]
    addSequence builder proofBA [Not a, a]
    nextSt builder $ fillInGaps axiomABA_NOT_B_NOT_A [Not a, a]
    nextSt builder $ (Not a --> Not a) --> Not (Not a)
    nextSt builder (Not (Not a)) >>= (`applyDeduction` [a])

inMorganAnd = do
    builder <- newBuilder
    

proveStmt :: Expression -> IO ProofStatement
proveStmt toBeProved@(Implication left right) = case left of
    And andL andR -> do
        builder <- newBuilder
        nextSt builder $ left --> andL
        nextSt builder $ left --> andR
        proveStmt right >>= (`applyDeduction` [andR, andL]) >>= addProof builder
        addSequence builder proofBA [left, andL --> andR --> right]
        addSequence builder proofAG [left, andL, andR --> right]
        addSequence builder proofBA [left, andR --> right]
        addSequence builder proofAG [left, andR, right]
        findProof builder toBeProved
    Or orL orR -> do
        builder <- newBuilder
        (proveStmt $ orL --> right) >>= addProof builder
        (proveStmt $ orR --> right) >>= addProof builder
        nextSt builder $ fillInGaps axiomAGBGA_OR_BG [orL, orR, right]
        nextSt builder $ (orR --> right) --> toBeProved
        nextSt builder toBeProved
    Implication implL implR -> do
        builder <- newBuilder
        liftM (`fillProof` [implL, implR]) implicationIsOr >>= addProof builder
        let fromOr = Not implL ||| implR --> right
        proofStmt fromOr >>= addProof builder
        addSequence builder proofBA [left, fromOr]
        addSequence builder proofAG [left, Not implL ||| implR, implR]
        findProof builder toBeProved
    Not (Or orL orL) -> do
        builder <- newBuilder
        liftM (`fillProof` [orL, orR]) deMorganOr >>= addProof builder
        let fromAnd = Not orL &&& Not orR --> right
        proveStmt fromAnd >>= addProof builder
        addSequence builder proofBA [left, fromAnd]
        addSequence builder proofAG [left, Not orL &&& Not orR, right]
        findProof builder toBeProved
    Not (And andL andR) -> do
        builder <- newBuilder
        liftM (`fillProof` [andL, andR]) deMorganAnd >>= addProof builder
        let fromOr = Not andL ||| Not andR --> right
        proveStmt fromOr >>= addProof builder
        addSequence builder proofBA [left, fromOr]
        addSequence builder proofAG [left, Not andL ||| Not andR, right]
        findProof builder toBeProved
    Not (Implication implL implR) -> do
        builder <- newBuilder
        liftM (`fillProof` [implL, implR]) notImplIsAnd >>= addProof builder
        let fromAnd = implL &&& Not implR --> right
        proveStmt fromAnd >>= addProof builder
        addSequence builder proofBA [left, fromAnd]
        addSequence builder proofAG [left, implL &&& Not implR, right]
        findProof builder toBeProved
    _ -> proveStmt right >>= (`applyDeduction` [left])
proveStmt toBeProved@(And left right) = do
    builder <- newBuilder
    nextSt builder left
    nextSt builder right
    nextSt builder $ fillInGaps axiomABA_AND_B [left, right]
    nextSt builder $ right --> left &&& right
    nextSt builder toBeProved
proveStmt toBeProved@(Or left right) = do
    builder <- newBuilder
    nextSt builder left
    nextSt builder right
    nextSt builder $ fillInGaps axiomAA_OR_B [left, right]
    nextSt builder $ fillInGaps axiomBA_OR_B [left, right]
    nextSt builder toBeProved
proveStmt toBeProved@(Not param) = case param of
    And andL andR -> do
        builder <- newBuilder
        let orSt = Not andL ||| Not andR
        proveStmt orSt >>= addProof builder
        liftM (`fillProof` [andL, andR]) inMorganOr >>= addProof builder
        nextSt builder toBeProved
    Or orL orR -> do
        builder <- newBuilder
        proveStmt (Not orL) >>= addProof builder
        proveStmt (Not orR) >>= addProof builder
        nextSt builder $ fillInGaps axiomABA_AND_B [Not orL, Not orR]
        nextSt builder $ Not orR --> Not orL &&& Not orR
        nextSt builder $ Not orL &&& Not orR
        undefined-}
