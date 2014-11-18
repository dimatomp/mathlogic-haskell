module ProofGeneration where

import Expression
import Axioms
import Proof

fillProof :: ProofStatement -> [Expression] -> ProofStatement
fillProof (Unproved expr num) list = Unproved (fillInGaps expr list) num
fillProof (Axiom expr num) list = Axiom (fillInGaps expr list) num
fillProof (ModusPonens expr left right num) list = ModusPonens (fillInGaps expr list) (fillProof left list) (fillProof right list) num

-- TODO Implement some kind of an immutable proof
proofBA = [fillInGaps axiomABA [Gap 1, Gap 0], Gap 0 --> Gap 1]
proofAG = [fillInGaps axiomABABGAG [Gap 0, Gap 1, Gap 2], (Gap 0 --> Gap 1 --> Gap 2) --> Gap 0 --> Gap 2, Gap 0 --> Gap 2]

addSequence builder exprList argList = mapM_ (nextSt builder . (`fillInGaps` argList)) exprList

applyDeduction :: ProofStatement -> [Expression] -> IO ProofStatement
applyDeduction res [] = return res
applyDeduction res (expr:suf) = do
    builder <- newBuilder
    let dfs stmt = do
            cExpr <- case stmt of
                Unproved unpr _ -> if unpr == expr
                    then do
                        nextSt builder $ fillInGaps axiomABA [expr, expr]
                        nextSt builder $ fillInGaps axiomABABGAG [expr, expr --> expr, expr]
                        nextSt builder $ (expr --> (expr --> expr) --> expr) --> expr --> expr
                        nextSt builder $ expr --> (expr --> expr) --> expr
                        return $ expr --> expr
                    else do
                        nextSt builder unpr
                        nextSt builder (fillInGaps axiomABA [unpr, expr]) 
                        return $ expr --> unpr
                Axiom axm _ -> do
                    nextSt builder axm
                    nextSt builder (fillInGaps axiomABA [axm, expr]) 
                    return $ expr --> axm
                ModusPonens mpe left right _ -> do
                    exprLeft <- dfs left
                    exprRight <- dfs right
                    nextSt builder $ exprLeft --> exprRight --> expr --> mpe
                    nextSt builder $ exprRight --> expr --> mpe
                    return $ expr --> mpe
            nextSt builder cExpr
            return cExpr
    lastExpr <- dfs res
    findProof builder lastExpr >>= (`applyDeduction` suf) 

contraposition = do
    myBuilder <- newBuilder
    nextSt myBuilder $ a --> b -- (-1)
    nextSt myBuilder $ Not b -- (0)
    addSequence myBuilder proofBA [a, Not b] -- (1) M.P. 0
    nextSt myBuilder $ fillInGaps axiomABA_NOT_B_NOT_A [a, b] -- (2)
    nextSt myBuilder $ (a --> Not b) --> Not a -- (3) M.P. -1
    nextSt myBuilder (Not a) >>= (`applyDeduction` [Not b]) 

deMorganOr = do
    let a = Gap 0
        b = Gap 1
    myBuilder <- newBuilder
    nextSt myBuilder $ Not (a ||| b)
    nextSt myBuilder $ fillInGaps axiomAA_OR_B [a, b]
    addSequence myBuilder proofBA [a, Not (a ||| b)]
    nextSt myBuilder $ fillInGaps axiomABA_NOT_B_NOT_A [a, a ||| b]
    nextSt myBuilder $ (a --> Not (a ||| b)) --> Not a
    nextSt myBuilder $ Not a
    nextSt myBuilder $ fillInGaps axiomBA_OR_B [a, b]
    addSequence myBuilder proofBA [b, Not (a ||| b)]
    nextSt myBuilder $ fillInGaps axiomABA_NOT_B_NOT_A [b, a ||| b]
    nextSt myBuilder $ (b --> Not (a ||| b)) --> Not b
    nextSt myBuilder $ Not b
    nextSt myBuilder $ fillInGaps axiomABA_AND_B [Not a, Not b]
    nextSt myBuilder $ Not b --> Not a &&& Not b
    nextSt myBuilder $ Not a &&& Not b >>= (`applyDeduction` [Not (a ||| b)])

aOrNotA = do
    let a = Gap 0
    builder <- newBuilder
    liftM (`fillProof` [a, a]) deMorganOr >>= addProof builder
    let unpackAnd = fillInGaps axiomA_AND_BA [Not a, Not (Not a)]
    nextSt builder unpackAnd
    addSequence builder proofBA [Not (a ||| Not a), unpackAnd]
    addSequence builder proofAG [Not (a ||| Not a), getLeft unpackAnd, getRight unpackAnd]
    addSequence builder $ (Not (a ||| Not a) --> unpackAnd) --> Not (a ||| Not a) --> Not a
    addSequence builder $ Not (a ||| Not a) --> Not a
    let unpackAnd = fillInGaps axiomA_AND_BB [Not a, Not (Not a)]
    nextSt builder unpackAnd
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
    let a = Gap 0
        b = Gap 1
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
    liftM (`fillProof` [b, b]) aOrNotA >>= addProof builder
    nextSt builder (Not a ||| b) >>= (`applyDeduction` [a --> b])

deMorganAnd = do
    let a = Gap 0
        b = Gap 1
        proofFromA = do
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

proveStmt :: Expression -> IO ProofStatement
proveStmt toBeProved@(Implication left right) = case left of
    Var _ -> proveStmt right >>= (`applyDeduction` [left])
    Gap _ -> proveStmt right >>= (`applyDeduction` [left])
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
        liftM (`fillInGaps` [implL, implR]) implicationIsOr >>= addProof builder
        let fromOr = Not implL ||| implR --> right
        proofStmt fromOr >>= addProof builder
        addSequence builder proofBA [left, fromOr]
        addSequence builder proofAG [left, Not implL ||| implR, implR]
        findProof builder toBeProved
    Not (Or orL orL) -> do
        builder <- newBuilder
        liftM (`fillInGaps` [orL, orR]) deMorganOr >>= addProof builder
        fromAnd <- proveStmt $ Not orL &&& Not orR --> right
        addSequence builder proofBA [left, fromAnd]
        addSequence builder proofAG [left, Not orL &&& Not orR, right]
        findProof builder toBeProved
    Not (And andL andR) -> do
        builder <- newBuilder
        liftM (`fillInGaps` [andL, andR]) deMorganAnd >>= addProof builder
        fromOr <- proveStmt $ Not andL ||| Not andR --> right
        addSequence builder proofBA [left, fromOr]
        addSequence builder proofAG [left, Not andL ||| Not andR, right]
        findProof builder toBeProved
