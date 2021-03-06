{-# LANGUAGE OverloadedStrings, FlexibleInstances #-}

module Axioms where

import Expression
import Data.Maybe
import Control.Monad

type ErrorReport = Maybe ErrorMessage

type Axiom = Expression -> Either ErrorReport ()

supposition :: Expression -> Axiom
supposition supp expr = if expr == supp then Right () else Left Nothing

justMatch patt expr = if patt `matches` expr then Right () else Left Nothing

basicAxioms :: [Axiom]
basicAxioms = map justMatch [
    Gap "A" --> Gap "B" --> Gap "A",
    (Gap "A" --> Gap "B") --> (Gap "A" --> Gap "B" --> Gap "C") --> (Gap "A" --> Gap "C"),
    Gap "A" --> Gap "B" --> Gap "A" &&& Gap "B",
    Gap "A" &&& Gap "B" --> Gap "A",
    Gap "A" &&& Gap "B" --> Gap "B",
    Gap "A" --> Gap "A" ||| Gap "B",
    Gap "B" --> Gap "A" ||| Gap "B",
    (Gap "A" --> Gap "C") --> (Gap "B" --> Gap "C") --> (Gap "A" ||| Gap "B" --> Gap "C"),
    (Gap "A" --> Gap "B") --> (Gap "A" --> Not (Gap "B")) --> Not (Gap "A")
    ]

classicAxiom :: Axiom
classicAxiom = justMatch $ Not (Not (Gap "A")) --> Gap "A"

intuitAxiom :: Axiom
intuitAxiom = justMatch $ Gap "A" --> Not (Gap "A") --> Gap "B"

guardU True = Right ()
guardU False = Left Nothing

eitherMatch a b = case matchWith a b of
    Just res -> Right res
    _ -> Left Nothing

predAxioms :: [Axiom]
predAxioms = [forAll, exists]
    where
        forAll (Implication (Forall x a) b) = do
            ((expr, func), err) <- eitherMatch a b
            guardU $ all (\(k, v) -> v == Gap k) expr
            guardU $ all (\(k, v) -> k == x || v == Var k) func
            when (isJust err) $ Left err
        forAll _ = Left Nothing
        exists (Implication a (Exist x b)) = do
            ((expr, func), err) <- eitherMatch b a
            guardU $ all (\(k, v) -> v == Gap k) expr
            guardU $ all (\(k, v) -> k == x || v == Var k) func
            when (isJust err) $ Left err
        exists _ = Left Nothing

arithAxioms :: [Axiom]
arithAxioms = map justMatch [
    Var "a" === Var "b" --> Stroke (Var "a") === Stroke (Var "b"),
    Var "a" === Var "b" --> Var "a" === Var "c" --> Var "b" === Var "c",
    Stroke (Var "a") === Stroke (Var "b") --> Var "a" === Var "b",
    Not (Stroke (Var "a") === zero),
    Var "a" +++ Stroke (Var "b") === Stroke (Var "a" +++ Var "b"),
    Var "a" +++ zero === Var "a",
    Var "a" *** zero === zero,
    Var "a" *** Stroke (Var "b") === Var "a" *** Var "b" +++ Var "a"
    ] ++ [lastScheme]
    where
        lastScheme input@(Implication (And a (Forall x (Implication b c))) b') = do
            guardU $ b == b'
            ((expr, func), err) <- eitherMatch b a
            guardU $ isNothing err
            guardU $ all (\(k, v) -> v == Gap k) expr
            guardU $ (x, zero) `elem` func
            guardU $ all (\(k, v) -> k == x || v == Var k) func
            ((expr, func), err) <- eitherMatch b c
            guardU $ isNothing err
            guardU $ all (\(k, v) -> v == Gap k) expr
            guardU $ (x, Stroke (Var x)) `elem` func
            guardU $ all (\(k, v) -> k == x || v == Var k) func
        lastScheme _ = Left Nothing
