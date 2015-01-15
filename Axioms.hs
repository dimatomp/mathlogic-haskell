module Axioms where

import Expression
import Data.Maybe

import Control.Monad (guard)

type Axiom = Expression -> Bool

classicAxioms = map matches [
    Gap "A" --> Gap "B" --> Gap "A",
    (Gap "A" --> Gap "B") --> (Gap "A" --> Gap "B" --> Gap "C") --> (Gap "A" --> Gap "C"),
    Gap "A" --> Gap "B" --> Gap "A" &&& Gap "B",
    Gap "A" &&& Gap "B" --> Gap "A",
    Gap "A" &&& Gap "B" --> Gap "B",
    Gap "A" --> Gap "A" ||| Gap "B",
    Gap "B" --> Gap "A" ||| Gap "B",
    (Gap "A" --> Gap "C") --> (Gap "B" --> Gap "C") --> (Gap "A" ||| Gap "B" --> Gap "C"),
    (Gap "A" --> Gap "B") --> (Gap "A" --> Not (Gap "B")) --> Not (Gap "A"),
    Not (Not (Gap "A")) --> Gap "A"
    ]

predAxioms = [forAll, exists]
    where
        forAll (Implication (Forall x a) b) = isJust $ do
            (expr, func) <- matchWith a b
            guard $ all (\(k, v) -> v == Gap k) expr
            guard $ all (\(k, v) -> if k == x then freeForSubst v a x else v == Var k) func
        forAll _ = False
        exists (Implication a (Exist x b)) = isJust $ do
            (expr, func) <- matchWith b a
            guard $ all (\(k, v) -> v == Gap k) expr
            guard $ all (\(k, v) -> if k == x then freeForSubst v a x else v == Var k) func
        exists _ = False

arithAxioms = map matches [
    Var "a" === Var "b" --> Stroke (Var "a") === Stroke (Var "b"),
    Var "a" === Var "b" --> Var "a" === Var "c" --> Var "b" === Var "c",
    Stroke (Var "a") === Stroke (Var "b") --> Var "a" === Var "b",
    Not (Stroke (Var "a") === Zero),
    Var "a" +++ Stroke (Var "b") === Stroke (Var "a" +++ Var "b"),
    Var "a" +++ Zero === Var "a",
    Var "a" *** Zero === Zero,
    Var "a" *** Stroke (Var "b") === Var "a" *** Var "b" +++ Var "a"
    ] ++ [lastScheme]
    where
        lastScheme (Implication (And a (Forall x (Implication b c))) b') = isJust $ do
            guard $ b == b'
            (expr, func) <- matchWith b a
            guard $ all (\(k, v) -> v == Gap k) expr
            guard $ all (\(k, v) -> v == if k == x then Zero else Var k) func
            (expr, func) <- matchWith b c
            guard $ all (\(k, v) -> v == Gap k) expr
            guard $ all (\(k, v) -> v == if k == x then Stroke (Var x) else Var k) func
        lastScheme _ = False
