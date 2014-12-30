{-# LANGUAGE NoImplicitPrelude #-}

import Prelude hiding (readFile, null)

import Data.List hiding (null)
import Data.Char
import Data.ByteString.Char8 (readFile, splitWith, null)
import Data.Maybe

import System.Environment

import Control.Monad
import Control.Monad.ST

import ExpressionParser
import Proof
import ProofUtils

main = do
    [fin, fout] <- getArgs
    heading:body <- liftM (filter (not . null) . splitWith isSpace) $ readFile fin
    let Just (supp, _) = parseHead heading
        assumeAll = foldr (\s f -> assume s . f) id supp
        inputData = map (fromJust . parseExpr) body
        output = getLoggedProof $ runST $ getLog $ liftM last $ assumeAll $ forM inputData tellEx
    writeFile fout $ concatMap (++ "\n") $ map show output
