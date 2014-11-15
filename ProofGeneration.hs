module ProofGeneration where

import Expression
import Axioms
import Proof

fillProof :: ProofStatement -> [Expression] -> ProofStatement
fillProof (Unproved expr num) list = Unproved (fillInGaps expr list) num
fillProof (Axiom expr num) list = Axiom (fillInGaps expr list) num
fillProof (ModusPonens expr left right num) list = ModusPonens (fillInGaps expr list) (fillProof left list) (fillProof right list) num

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
