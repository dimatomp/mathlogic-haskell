module ProofGeneration where

import Expression hiding (merge)
import Proof

import Data.List
import Data.Maybe
import Data.ByteString.Char8

import Control.Applicative ((<|>))
import Control.Monad

proveAG a b c = do
    tellEx $ a --> b
    tellEx $ a --> b --> c
    tellEx $ (a --> b) --> (a --> b --> c) --> (a --> c)
    tellEx $ (a --> b --> c) --> (a --> c)
    tellEx $ a --> c

proveAA a = do
    tellEx $ a --> a --> a
    tellEx $ a --> (a --> a) --> a
    proveAG a (a --> a) a

proveBA a b = do
    tellEx $ b
    tellEx $ b --> a --> b
    tellEx $ a --> b

contraposition a b = asRoot $ assume (a --> b) $ assume (Not b) $ do
    tellEx $ a --> b
    tellEx $ Not b
    proveBA a (Not b)
    tellEx $ (a --> b) --> (a --> Not b) --> Not a
    tellEx $ (a --> Not b) --> Not a
    tellEx $ Not a

deMorganOr a b = asRoot $ assume (Not (a ||| b)) $ do
    tellEx $ Not (a ||| b)
    tellEx $ a --> a ||| b
    proveBA a (Not (a ||| b))
    tellEx $ (a --> a ||| b) --> (a --> Not (a ||| b)) --> Not a
    tellEx $ (a --> Not (a ||| b)) --> Not a
    tellEx $ Not a
    tellEx $ b --> a ||| b
    proveBA b (Not (a ||| b))
    tellEx $ (b --> a ||| b) --> (b --> Not (a ||| b)) --> Not b
    tellEx $ (b --> Not (a ||| b)) --> Not b
    tellEx $ Not b
    tellEx $ Not a --> Not b --> Not a &&& Not b
    tellEx $ Not b --> Not a &&& Not b
    tellEx $ Not a &&& Not b

aOrNotA a = asRoot $ do
    deMorganOr a (Not a)
    tellEx $ Not a &&& Not (Not a) --> Not a
    proveBA (Not (a ||| Not a)) (Not a &&& Not (Not a) --> Not a)
    proveAG (Not (a ||| Not a)) (Not a &&& Not (Not a)) (Not a)
    tellEx $ Not a &&& Not (Not a) --> Not (Not a)
    proveBA (Not (a ||| Not a)) (Not a &&& Not (Not a) --> Not (Not a))
    proveAG (Not (a ||| Not a)) (Not a &&& Not (Not a)) (Not (Not a))
    tellEx $ (Not (a ||| Not a) --> Not a) --> (Not (a ||| Not a) --> Not (Not a)) --> Not (Not (a ||| Not a))
    tellEx $ (Not (a ||| Not a) --> Not (Not a)) --> Not (Not (a ||| Not a))
    tellEx $ Not (Not (a ||| Not a))
    tellEx $ Not (Not (a ||| Not a)) --> a ||| Not a
    tellEx $ a ||| Not a

implicationIsOr a b = asRoot $ do
    contraposition a b
    aOrNotA b
    assume (a --> b) $ do
        tellEx $ a --> b
        tellEx $ (a --> b) --> Not b --> Not a
        tellEx $ Not b --> Not a
        tellEx $ Not a --> Not a ||| b
        tellEx $ b --> Not a ||| b
        proveBA (Not b) (Not a --> Not a ||| b)
        proveAG (Not b) (Not a) (Not a ||| b)
        tellEx $ (b --> Not a ||| b) --> (Not b --> Not a ||| b) --> b ||| Not b --> Not a ||| b
        tellEx $ (Not b --> Not a ||| b) --> b ||| Not b --> Not a ||| b
        tellEx $ b ||| Not b --> Not a ||| b
        tellEx $ b ||| Not b
        tellEx $ Not a ||| b

deMorganAnd a b = asRoot $ do
    aOrNotA a
    assume (Not (a &&& b)) $ do
        tellEx $ Not (a &&& b)
        assume a $ do
            tellEx $ a
            tellEx $ a --> b --> a &&& b
            tellEx $ b --> a &&& b
            proveBA b (Not (a &&& b))
            tellEx $ (b --> a &&& b) --> (b --> Not (a &&& b)) --> Not b
            tellEx $ (b --> Not (a &&& b)) --> Not b
            tellEx $ Not b
        tellEx $ Not a --> Not a ||| Not b
        tellEx $ Not b --> Not a ||| Not b
        proveBA a (Not b --> Not a ||| Not b)
        proveAG a (Not b) (Not a ||| Not b)
        tellEx $ (a --> Not a ||| Not b) --> (Not a --> Not a ||| Not b) --> a ||| Not a --> Not a ||| Not b
        tellEx $ (Not a --> Not a ||| Not b) --> a ||| Not a --> Not a ||| Not b
        tellEx $ a ||| Not a --> Not a ||| Not b
        tellEx $ a ||| Not a
        tellEx $ Not a ||| Not b

intuitionist a b = asRoot $ assume (Not a) $ assume a $ do
    tellEx $ Not a
    tellEx $ a
    proveBA (Not b) a
    proveBA (Not b) (Not a)
    tellEx $ (Not b --> a) --> (Not b --> Not a) --> Not (Not b)
    tellEx $ (Not b --> Not a) --> Not (Not b)
    tellEx $ Not (Not b)
    tellEx $ Not (Not b) --> b
    tellEx $ b

notImplIsAnd a b = asRoot $ do
    intuitionist a b
    assume (Not (a --> b)) $ do
        tellEx $ Not (a --> b)
        proveBA (Not a) (Not (a --> b))
        tellEx $ Not a --> a --> b
        tellEx $ (Not a --> a --> b) --> (Not a --> Not (a --> b)) --> Not (Not a)
        tellEx $ (Not a --> Not (a --> b)) --> Not (Not a)
        tellEx $ Not (Not a)
        tellEx $ Not (Not a) --> a
        tellEx $ a
        proveBA b (Not (a --> b))
        tellEx $ b --> a --> b
        tellEx $ (b --> a --> b) --> (b --> Not (a --> b)) --> Not b
        tellEx $ (b --> Not (a --> b)) --> Not b
        tellEx $ Not b
        tellEx $ a --> Not b --> a &&& Not b
        tellEx $ Not b --> a &&& Not b
        tellEx $ a &&& Not b

inMorganOr a b = asRoot $ do
    forM_ [a, b] $ \wa -> assume (Not wa) $ do
        tellEx $ Not wa
        tellEx $ a &&& b --> wa
        proveBA (a &&& b) (Not wa)
        tellEx $ (a &&& b --> wa) --> (a &&& b --> Not wa) --> Not (a &&& b)
        tellEx $ (a &&& b --> Not wa) --> Not (a &&& b)
        tellEx $ Not (a &&& b)
    tellEx $ (Not a --> Not (a &&& b)) --> (Not b --> Not (a &&& b)) --> (Not a ||| Not b --> Not (a &&& b))
    tellEx $ (Not b --> Not (a &&& b)) --> (Not a ||| Not b --> Not (a &&& b))
    tellEx $ Not a ||| Not b --> Not (a &&& b)

addNotNot a = asRoot $ assume a $ do
    tellEx $ a
    proveAA (Not a)
    proveBA (Not a) a
    tellEx $ (Not a --> a) --> (Not a --> Not a) --> Not (Not a)
    tellEx $ (Not a --> Not a) --> Not (Not a)
    tellEx $ Not (Not a)

addNotNotToOr a b = asRoot $ do
    addNotNot a
    tellEx $ Not (Not a) --> Not (Not a) ||| Not (Not b)
    proveBA a (Not (Not a) --> Not (Not a) ||| Not (Not b))
    proveAG a (Not (Not a)) (Not (Not a) ||| Not (Not b))
    addNotNot b
    tellEx $ Not (Not b) --> Not (Not a) ||| Not (Not b)
    proveBA b (Not (Not b) --> Not (Not a) ||| Not (Not b))
    proveAG b (Not (Not b)) (Not (Not a) ||| Not (Not b))
    tellEx $ (a --> Not (Not a) ||| Not (Not b)) --> (b --> Not (Not a) ||| Not (Not b)) --> a ||| b --> Not (Not a) ||| Not (Not b)
    tellEx $ (b --> Not (Not a) ||| Not (Not b)) --> a ||| b --> Not (Not a) ||| Not (Not b)
    tellEx $ a ||| b --> Not (Not a) ||| Not (Not b)

notAThenB a b = asRoot $ do
    addNotNotToOr a b
    inMorganOr (Not a) (Not b)
    assume (a ||| b) $ assume (Not a) $ do
        tellEx $ a ||| b
        tellEx $ Not a
        tellEx $ a ||| b --> Not (Not a) ||| Not (Not b)
        tellEx $ Not (Not a) ||| Not (Not b)
        tellEx $ Not (Not a) ||| Not (Not b) --> Not (Not a &&& Not b)
        tellEx $ Not (Not a &&& Not b)
        tellEx $ Not a --> Not b --> Not a &&& Not b
        tellEx $ Not b --> Not a &&& Not b
        proveBA (Not b) (Not (Not a &&& Not b))
        tellEx $ (Not b --> Not a &&& Not b) --> (Not b --> Not (Not a &&& Not b)) --> Not (Not b)
        tellEx $ (Not b --> Not (Not a &&& Not b)) --> Not (Not b)
        tellEx $ Not (Not b)
        tellEx $ Not (Not b) --> b
        tellEx $ b

inMorganAnd a b = asRoot $ do
    notAThenB a b
    assume (Not a &&& Not b) $ do
        tellEx $ Not a &&& Not b
        tellEx $ Not a &&& Not b --> Not a
        tellEx $ Not a
        proveBA (a ||| b) (Not a)
        tellEx $ a ||| b --> Not a --> b
        proveAG (a ||| b) (Not a) b
        tellEx $ Not a &&& Not b --> Not b
        tellEx $ Not b
        proveBA (a ||| b) (Not b)
        tellEx $ (a ||| b --> b) --> (a ||| b --> Not b) --> Not (a ||| b)
        tellEx $ (a ||| b --> Not b) --> Not (a ||| b)
        tellEx $ Not (a ||| b)

notAndIsImpl a b = asRoot $ assume (a &&& Not b) $ do
    tellEx $ a &&& Not b
    tellEx $ a &&& Not b --> a
    tellEx $ a
    proveBA (a --> b) a
    proveAA (a --> b)
    proveAG (a --> b) a b
    tellEx $ a &&& Not b --> Not b
    tellEx $ Not b
    proveBA (a --> b) (Not b)
    tellEx $ ((a --> b) --> b) --> ((a --> b) --> Not b) --> Not (a --> b)
    tellEx $ ((a --> b) --> Not b) --> Not (a --> b)
    tellEx $ Not (a --> b)

notAThenBIsOr a b = asRoot $ do
    contraposition (Not (a ||| b)) (Not (Not a --> b))
    deMorganOr a b
    notAndIsImpl (Not a) b
    assume (Not (a ||| b)) $ do
        tellEx $ Not (a ||| b)
        tellEx $ Not (a ||| b) --> Not a &&& Not b
        tellEx $ Not a &&& Not b
        tellEx $ Not a &&& Not b --> Not (Not a --> b)
        tellEx $ Not (Not a --> b)
    tellEx $ Not (Not (Not a --> b)) --> Not (Not (a ||| b))
    addNotNot (Not a --> b)
    proveBA (Not a --> b) (Not (Not (Not a --> b)) --> Not (Not (a ||| b)))
    proveAG (Not a --> b) (Not (Not (Not a --> b))) (Not (Not (a ||| b)))
    tellEx $ Not (Not (a ||| b)) --> a ||| b
    proveBA (Not a --> b) (Not (Not (a ||| b)) --> a ||| b)
    proveAG (Not a --> b) (Not (Not (a ||| b))) (a ||| b)

contradiction p right = do
    tellEx $ p
    tellEx $ Not p
    intuitionist p right
    tellEx $ p --> right
    tellEx $ right

proveStmt :: Expression -> Proof ProofStatement
proveStmt toBeProved@(Implication left right) = case left of
    And andL andR -> do
        tellEx $ left --> andL
        tellEx $ left --> andR
        proveStmt $ andL --> andR --> right
        proveBA left (andL --> andR --> right)
        proveAG left andL (andR --> right)
        proveAG left andR right
    Or orL orR -> do
        proveStmt $ orL --> right
        proveStmt $ orR --> right
        tellEx $ (orL --> right) --> (orR --> right) --> orL ||| orR --> right
        tellEx $ (orR --> right) --> orL ||| orR --> right
        tellEx $ orL ||| orR --> right
    Implication implL implR -> do
        implicationIsOr implL implR
        proveStmt $ Not implL ||| implR --> right
        proveBA left (Not implL ||| implR --> right)
        proveAG left (Not implL ||| implR) right
    Not (Or orL orR) -> do
        deMorganOr orL orR
        proveStmt $ Not orL &&& Not orR --> right
        proveBA left (Not orL &&& Not orR --> right)
        proveAG left (Not orL &&& Not orR) right
    Not (And andL andR) -> do
        deMorganAnd andL andR
        proveStmt $ Not andL ||| Not andR --> right
        proveBA left (Not andL ||| Not andR --> right)
        proveAG left (Not andL ||| Not andR) right
    Not (Implication implL implR) -> do
        notImplIsAnd implL implR
        proveStmt $ implL &&& Not implR --> right
        proveBA left (implL &&& Not implR --> right)
        proveAG left (implL &&& Not implR) right
    Not (Not p) -> do
        tellEx $ Not (Not p) --> p
        proveStmt $ p --> right
        proveBA (Not (Not p)) (p --> right)
        proveAG (Not (Not p)) p right
    Not p -> assume left $ contradiction p right <|> proveStmt right
    p -> assume left $ contradiction p right <|> proveStmt right
proveStmt toBeProved@(And left right) = do
    proveStmt $ left
    proveStmt $ right
    tellEx $ left --> right --> left &&& right
    tellEx $ right --> left &&& right
    tellEx $ toBeProved
proveStmt toBeProved@(Or left right) = do
    proveStmt $ Not left --> right
    notAThenBIsOr left right
    tellEx $ toBeProved
proveStmt toBeProved@(Not param) = case param of
    And andL andR -> do
        proveStmt $ Not andL ||| Not andR
        inMorganOr andL andR
        tellEx $ toBeProved
    Or orL orR -> do
        proveStmt $ Not orL &&& Not orR
        inMorganAnd orL orR
        tellEx $ toBeProved
    Implication implL implR -> do
        proveStmt $ implL &&& Not implR
        notAndIsImpl implL implR
        tellEx $ toBeProved
    Not p -> do
        addNotNot p
        proveStmt $ p
        tellEx $ toBeProved
    _ -> tellEx toBeProved
proveStmt toBeProved = tellEx toBeProved

traceExpr :: Expression -> Maybe [(ByteString, Bool)]
traceExpr expr =
    let gather (Gap s) = [s]
        gather (Not p) = gather p
        gather (And l r) = union (gather l) (gather r)
        gather (Or l r) = union (gather l) (gather r)
        gather (Implication l r) = union (gather l) (gather r)

        check (Gap s) list b = b == (fromJust $ lookup s list)
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
