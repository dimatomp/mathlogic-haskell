module Axioms where

import Control.Monad (guard)
import Expression
import Data.Maybe

axiomABA = Gap 0 --> Gap 1 --> Gap 0
axiomABABGAG = (Gap 0 --> Gap 1) --> (Gap 0 --> Gap 1 --> Gap 2) --> (Gap 0 --> Gap 2)
axiomABA_AND_B = Gap 0 --> Gap 1 --> Gap 0 &&& Gap 1
axiomA_AND_BA = Gap 0 &&& Gap 1 --> Gap 0
axiomA_AND_BB = Gap 0 &&& Gap 1 --> Gap 1
axiomAA_OR_B = Gap 0 --> Gap 0 ||| Gap 1
axiomBA_OR_B = Gap 1 --> Gap 0 ||| Gap 1
axiomAGBGA_OR_BG = (Gap 0 --> Gap 2) --> (Gap 1 --> Gap 2) --> (Gap 0 ||| Gap 1 --> Gap 2)
axiomABA_NOT_B_NOT_A = (Gap 0 --> Gap 1) --> (Gap 0 --> Not (Gap 1)) --> Not (Gap 0)
axiomNOT_NOT_AA = Not (Not (Gap 0)) --> Gap 0

getClassicAxiom :: Expression -> Maybe Int
getClassicAxiom expr = if nonMatching < length classicAxioms then Just $ nonMatching + 1 else Nothing
    where
        classicAxioms = [axiomABA, axiomABABGAG, axiomABA_AND_B, axiomA_AND_BA, axiomA_AND_BB, axiomAA_OR_B, axiomBA_OR_B, axiomAGBGA_OR_BG, axiomABA_NOT_B_NOT_A, axiomNOT_NOT_AA]
        nonMatching = length $ takeWhile (isNothing . (`matches` expr)) classicAxioms
