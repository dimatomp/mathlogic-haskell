module QuantifierLifting where

import Expression
import Proof
import ProofGeneration

import Control.Applicative (Alternative(..))
import Control.Monad

mapQ :: Expression -> Expression -> Proof Expression
mapQ (Forall x p) q = liftM getExpression $ assume (Forall x (p --> q)) $ do
    assume (Forall x p) $ do
        tellEx $ Forall x p
        tellEx $ Forall x p --> p
        tellEx $ p
        tellEx $ Forall x (p --> q)
        tellEx $ Forall x (p --> q) --> p --> q
        tellEx $ p --> q
        tellEx $ q
    tellEx $ Forall x p --> Forall x q
mapQ (Exist x p) q = liftM getExpression $ assume (Forall x (p --> q)) $ assume (Exist x p) $ do
    tellEx $ Forall x (p --> q) --> p --> q
    tellEx $ p --> q
    tellEx $ Exist x p --> q
    tellEx $ Exist x p
    tellEx $ q
    tellEx $ q --> Exist x q
    tellEx $ Exist x q

orIsImplication a b = assume (Not a ||| b) $ do
    notAThenB (Not a) b
    tellEx $ Not (Not a) --> b
    addNotNot a
    proveBA a (Not (Not a) --> b)
    proveAG a (Not (Not a)) b

extractQ :: Expression -> Proof Expression
extractQ (Not (Exist x p)) = liftM getExpression $ do
    assume (Not (Exist x p)) $ do
        tellEx $ p --> Exist x p
        contraposition p (Exist x p)
        tellEx $ Not (Exist x p) --> Not p
        tellEx $ Not (Exist x p)
        tellEx $ Not p
    tellEx $ Not (Exist x p) --> Forall x (Not p)
extractQ (Not (Forall x p)) = liftM getExpression $ assume (Not (Forall x p)) $ do
    assume (Not (Exist x (Not p))) $ do
        tellEx $ Not p --> Exist x (Not p)
        contraposition (Not p) (Exist x (Not p))
        tellEx $ Not (Exist x (Not p)) --> Not (Not p)
        tellEx $ Not (Exist x (Not p))
        tellEx $ Not (Not p)
        tellEx $ Not (Not p) --> p
        tellEx $ p
    tellEx $ Not (Exist x (Not p)) --> Forall x p
    contraposition (Not (Exist x (Not p))) (Forall x p)
    tellEx $ Not (Forall x p) --> Not (Not (Exist x (Not p)))
    tellEx $ Not (Forall x p)
    tellEx $ Not (Not (Exist x (Not p)))
    tellEx $ Not (Not (Exist x (Not p))) --> Exist x (Not p)
    tellEx $ Exist x (Not p)
extractQ (Not (Not e)) = liftM getExpression $ assume (Not (Not e)) $ do
    tellEx $ Not (Not e) --> e
    tellEx $ Not (Not e)
    tellEx $ e
    Implication _ result <- extractQ e
    tellEx $ result
    let (ctr, x, e) = case result of
            Exist x e -> (Exist, x, e)
            Forall x e -> (Forall, x, e)
    addNotNot e
    proveBA result (e --> Not (Not e))
    tellEx $ result --> Forall x (e --> Not (Not e))
    tellEx $ Forall x (e --> Not (Not e))
    mapQ result (Not (Not e))
    tellEx $ result --> ctr x (Not (Not e))
    tellEx $ ctr x (Not (Not e))
extractQ (Not (And l r)) = liftM getExpression $ assume (Not (l &&& r)) $ do
    deMorganAnd l r
    tellEx $ Not (l &&& r)
    tellEx $ Not l ||| Not r
    Implication (Or (Not _) (Not _)) final <- extractQ $ Not l ||| Not r
    tellEx $ final
    let (ctr, x, l, r) = case final of
            Exist x (Or (Not l) (Not r)) -> (Exist, x, l, r)
            Forall x (Or (Not l) (Not r)) -> (Forall, x, l, r)
    inMorganOr l r
    proveBA final (Not l ||| Not r --> Not (l &&& r))
    tellEx $ final --> Forall x (Not l ||| Not r --> Not (l &&& r))
    tellEx $ Forall x (Not l ||| Not r --> Not (l &&& r))
    mapQ final (Not (l &&& r))
    tellEx $ final --> ctr x (Not (l &&& r))
    tellEx $ ctr x (Not (l &&& r))
extractQ (Not (Or l r)) = liftM getExpression $ assume (Not (l ||| r)) $ do
    deMorganOr l r
    tellEx $ Not (l ||| r)
    tellEx $ Not l &&& Not r
    Implication (And (Not _) (Not _)) final <- extractQ $ Not l &&& Not r
    tellEx $ final
    let (ctr, x, l, r) = case final of
            Exist x (And (Not l) (Not r)) -> (Exist, x, l, r)
            Forall x (And (Not l) (Not r)) -> (Forall, x, l, r)
    inMorganAnd l r
    proveBA final (Not l &&& Not r --> Not (l ||| r))
    tellEx $ final --> Forall x (Not l &&& Not r --> Not (l ||| r))
    tellEx $ Forall x (Not l &&& Not r --> Not (l ||| r))
    mapQ final (Not (l ||| r))
    tellEx $ final --> ctr x (Not (l &&& r))
    tellEx $ ctr x (Not (l &&& r))
extractQ (Not (Implication l r)) = liftM getExpression $ assume (Not (l --> r)) $ do
    notImplIsAnd l r
    tellEx $ Not (l --> r)
    tellEx $ l &&& Not r
    Implication (And _ (Not _)) result <- extractQ $ l &&& Not r
    tellEx $ result
    let (ctr, x, l, r) = case result of
            Exist x (And l (Not r)) -> (Exist, x, l, r)
            Forall x (And l (Not r)) -> (Forall, x, l, r)
    notAndIsImpl l r
    proveBA result (l &&& Not r --> Not (l --> r))
    tellEx $ result --> Forall x (l &&& r --> Not (l --> r))
    tellEx $ Forall x (l &&& r --> Not (l --> r))
    mapQ result (Not (l --> r))
    tellEx $ result --> ctr x (Not (l --> r))
    tellEx $ ctr x (Not (l --> r))
extractQ (And (Forall x p) q) = liftM getExpression $ do
    let x1 = chooseUnique x $ grabVars (Forall x p &&& q)
        px1 = substitute x x1 p
    assume (Forall x p &&& q) $ do
        tellEx $ Forall x p &&& q --> Forall x p
        tellEx $ Forall x p &&& q
        tellEx $ Forall x p
        tellEx $ Forall x p --> px1
        tellEx $ px1
        tellEx $ Forall x p &&& q --> q
        tellEx $ q
        tellEx $ px1 --> q --> px1 &&& q
        tellEx $ q --> px1 &&& q
        tellEx $ px1 &&& q
    tellEx $ Forall x p &&& q --> Forall x1 (px1 &&& q)
extractQ (And q (Forall x p)) = liftM getExpression $ do
    let x1 = chooseUnique x $ grabVars (q &&& Forall x p)
        px1 = substitute x x1 p
    assume (q &&& Forall x p) $ do
        tellEx $ q &&& Forall x p --> Forall x p
        tellEx $ q &&& Forall x p
        tellEx $ Forall x p
        tellEx $ Forall x p --> px1
        tellEx $ px1
        tellEx $ q &&& Forall x p --> q
        tellEx $ q
        tellEx $ q --> px1 --> q &&& px1
        tellEx $ px1 --> q &&& px1
        tellEx $ q &&& px1
    tellEx $ q &&& Forall x p --> Forall x1 (q &&& px1)
extractQ (And (Exist x p) q) = liftM getExpression $ do
    let x1 = chooseUnique x $ grabVars (Exist x p &&& q)
        px1 = substitute x x1 p
    tellEx $ p --> Exist x1 px1
    tellEx $ Exist x p --> Exist x1 px1
    assume (Exist x p &&& q) $ do
        tellEx $ Exist x p &&& q --> Exist x p
        tellEx $ Exist x p &&& q
        tellEx $ Exist x p
        tellEx $ Exist x p &&& q --> q
        tellEx $ q
        assume px1 $ do
            tellEx $ px1 --> q --> px1 &&& q
            tellEx $ px1
            tellEx $ q --> px1 &&& q
            tellEx $ q
            tellEx $ px1 &&& q
            tellEx $ px1 &&& q --> Exist x1 (px1 &&& q)
            tellEx $ Exist x1 (px1 &&& q)
        tellEx $ Exist x1 px1 --> Exist x1 (px1 &&& q)
        tellEx $ Exist x p --> Exist x1 px1
        tellEx $ Exist x1 px1
        tellEx $ Exist x1 (px1 &&& q)
extractQ (And q (Exist x p)) = liftM getExpression $ do
    let x1 = chooseUnique x $ grabVars (q &&& Exist x p)
        px1 = substitute x x1 p
    tellEx $ p --> Exist x1 px1
    tellEx $ Exist x p --> Exist x1 px1
    assume (q &&& Exist x p) $ do
        tellEx $ q &&& Exist x p --> Exist x p
        tellEx $ q &&& Exist x p
        tellEx $ Exist x p
        tellEx $ q &&& Exist x p --> q
        tellEx $ q
        tellEx $ q --> px1 --> q &&& px1
        tellEx $ px1 --> q &&& px1
        tellEx $ q &&& px1 --> Exist x1 (q &&& px1)
        proveBA px1 (q &&& px1 --> Exist x1 (q &&& px1))
        proveAG px1 (q &&& px1) (Exist x1 (q &&& px1))
        tellEx $ Exist x1 px1 --> Exist x1 (q &&& px1)
        tellEx $ Exist x p --> Exist x1 px1
        tellEx $ Exist x1 px1
        tellEx $ Exist x1 (q &&& px1)
extractQ (And l r) = liftM getExpression $ assume (l &&& r) $ do
    tellEx $ l &&& r
    tellEx $ l &&& r --> l
    tellEx $ l
    tellEx $ l &&& r --> r
    tellEx $ r
    let fromSide w ret = do
        Implication _ result <- extractQ l
        tellEx $ result
        let Implication a (Implication b c) = ret result
        tellEx $ a --> b --> c
        tellEx $ b --> c
        tellEx $ c
        Implication (And _ _) final <- extractQ c
        tellEx $ final
    fromSide l (\res -> res --> r --> res &&& r) <|> fromSide r (\res -> l --> res --> l &&& res)
extractQ (Or (Forall x p) q) = liftM getExpression $ do
    let x1 = chooseUnique x $ grabVars (Forall x p ||| q)
        px1 = substitute x x1 p
    assume (Forall x p) $ do
        tellEx $ Forall x p --> px1
        tellEx $ Forall x p
        tellEx $ px1
        tellEx $ px1 --> px1 ||| q
        tellEx $ px1 ||| q
    tellEx $ Forall x p --> Forall x1 (px1 ||| q)
    tellEx $ q --> px1 ||| q
    tellEx $ q --> Forall x1 (px1 ||| q)
    tellEx $ (Forall x p --> Forall x1 (px1 ||| q)) --> (q --> Forall x1 (px1 ||| q)) --> Forall x p ||| q --> Forall x1 (px1 ||| q)
    tellEx $ (q --> Forall x1 (px1 ||| q)) --> Forall x p ||| q --> Forall x1 (px1 ||| q)
    tellEx $ Forall x p ||| q --> Forall x1 (px1 ||| q)
extractQ (Or q (Forall x p)) = liftM getExpression $ do
    let x1 = chooseUnique x $ grabVars (q ||| Forall x p)
        px1 = substitute x x1 p
    assume (Forall x p) $ do
        tellEx $ Forall x p --> px1
        tellEx $ Forall x p
        tellEx $ px1
        tellEx $ px1 --> q ||| px1
        tellEx $ q ||| px1
    tellEx $ Forall x p --> Forall x1 (q ||| px1)
    tellEx $ q --> q ||| px1
    tellEx $ q --> Forall x1 (q ||| px1)
    tellEx $ (q --> Forall x1 (q ||| px1)) --> (Forall x p --> Forall x1 (q ||| px1)) --> q ||| Forall x p --> Forall x1 (q ||| px1)
    tellEx $ (Forall x p --> Forall x1 (q ||| px1)) --> q ||| Forall x p --> Forall x1 (q ||| px1)
    tellEx $ q ||| Forall x p --> Forall x1 (q ||| px1)
extractQ (Or (Exist x p) q) = liftM getExpression $ do
    let x1 = chooseUnique x $ grabVars (Exist x p ||| q)
        px1 = substitute x x1 p
    assume (Exist x p) $ do
        tellEx $ px1 --> px1 ||| q
        tellEx $ px1 ||| q --> Exist x1 (px1 ||| q)
        proveBA px1 (px1 ||| q --> Exist x1 (px1 ||| q))
        proveAG px1 (px1 ||| q) (Exist x1 (px1 ||| q))
        tellEx $ Exist x1 px1 --> Exist x1 (px1 ||| q)
        tellEx $ p --> Exist x p
        tellEx $ Exist x p --> Exist x1 px1
        tellEx $ Exist x p
        tellEx $ Exist x1 px1
        tellEx $ Exist x1 (px1 ||| q)
    tellEx $ q --> px1 ||| q
    tellEx $ px1 ||| q --> Exist x1 (px1 ||| q)
    proveBA q (px1 ||| q --> Exist x1 (px1 ||| q))
    proveAG q (px1 ||| q) (Exist x1 (px1 ||| q))
    tellEx $ (Exist x p --> Exist x1 (px1 ||| q)) --> (q --> Exist x1 (px1 ||| q)) --> Exist x p ||| q --> Exist x1 (px1 ||| q)
    tellEx $ (q --> Exist x1 (px1 ||| q)) --> Exist x p ||| q --> Exist x1 (px1 ||| q)
    tellEx $ Exist x p ||| q --> Exist x1 (px1 ||| q)
extractQ (Or q (Exist x p)) = liftM getExpression $ do
    let x1 = chooseUnique x $ grabVars (q ||| Exist x p)
        px1 = substitute x x1 p
    assume (Exist x p) $ do
        tellEx $ px1 --> q ||| px1
        tellEx $ q ||| px1 --> Exist x1 (q ||| px1)
        proveBA px1 (q ||| px1 --> Exist x1 (q ||| px1))
        proveAG px1 (q ||| px1) (Exist x1 (q ||| px1))
        tellEx $ Exist x1 px1 --> Exist x1 (q ||| px1)
        tellEx $ p --> Exist x p
        tellEx $ Exist x p --> Exist x1 px1
        tellEx $ Exist x p
        tellEx $ Exist x1 px1
        tellEx $ Exist x1 (q ||| px1)
    tellEx $ q --> q ||| px1
    tellEx $ q ||| px1 --> Exist x1 (q ||| px1)
    proveBA q (q ||| px1 --> Exist x1 (q ||| px1))
    proveAG q (q ||| px1) (Exist x1 (q ||| px1))
    tellEx $ (q --> Exist x1 (q ||| px1)) --> (Exist x p --> Exist x1 (q ||| px1)) --> q ||| Exist x p --> Exist x1 (q ||| px1)
    tellEx $ (Exist x p --> Exist x1 (q ||| px1)) --> q ||| Exist x p --> Exist x1 (q ||| px1)
    tellEx $ q ||| Exist x p --> Exist x1 (q ||| px1)
extractQ (Or l r) = liftM getExpression $ assume (l ||| r) $ fromSide l r (||| r) <|> fromSide r l (l |||)
    where
        fromSide w o ret = do
            Implication _ result <- extractQ w
            tellEx $ result --> ret result
            proveBA w (result --> ret result)
            proveAG w result (ret result)
            tellEx $ o --> ret result
            tellEx $ (l --> ret result) --> (r --> ret result) --> l ||| r --> ret result
            tellEx $ (r --> ret result) --> l ||| r --> ret result
            tellEx $ l ||| r --> ret result
            tellEx $ ret result
            Implication (Or _ _) final <- extractQ $ ret result
            tellEx $ final
extractQ (Implication l r) = liftM getExpression $ assume (l --> r) $ do
    implicationIsOr l r
    tellEx $ l --> r
    tellEx $ Not l ||| r
    Implication (Or (Not _) _) result <- extractQ $ Not l ||| r
    tellEx $ result
    let (ctr, x, l, r) = case result of
            Exist x (Or (Not l) r) -> (Exist, x, l, r)
            Forall x (Or (Not l) r) -> (Forall, x, l, r)
    orIsImplication l r
    proveBA result (Not l ||| r --> l --> r)
    tellEx $ result --> Forall x (Not l ||| r --> l --> r)
    tellEx $ Forall x (Not l ||| r --> l --> r)
    mapQ result (l --> r)
    tellEx $ result --> ctr x (l --> r)
    tellEx $ ctr x (l --> r)
extractQ (Forall x e) = liftM getExpression $ assume (Forall x e) $ do
    Implication _ result <- extractQ e
    proveBA (Forall x e) (e --> result)
    tellEx $ Forall x e --> Forall x (e --> result)
    tellEx $ Forall x e
    tellEx $ Forall x (e --> result)
    mapQ (Forall x e) result
    tellEx $ Forall x e --> Forall x result
    tellEx $ Forall x result
extractQ (Exist x e) = liftM getExpression $ assume (Exist x e) $ do
    Implication _ result <- extractQ e
    proveBA (Exist x e) (e --> result)
    tellEx $ Exist x e --> Forall x (e --> result)
    tellEx $ Exist x e
    tellEx $ Forall x (e --> result)
    mapQ (Exist x e) result
    tellEx $ Exist x e --> Exist x result
    tellEx $ Exist x result
extractQ _ = empty
