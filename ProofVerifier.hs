{-# LANGUAGE NoImplicitPrelude #-}

import Prelude hiding (readFile, lines, null)
import ExpressionParser
import Proof
import Data.List hiding (lines, null)
import Data.Char
import Data.ByteString.Char8 hiding (last, writeFile, map, intercalate, filter)
import System.Environment
import Control.Monad
import Data.Maybe

main = do
    builder <- newBuilder
    [fin, fout] <- getArgs
    inputData <- liftM (filter (not . null) . splitWith isSpace) $ readFile fin
    mapM_ (nextSt builder . fromJust . parseExpr) inputData
    result <- liftM (intercalate "\n" . map show) $ (findProof builder $ fromJust $ parseExpr $ last inputData) >>= getNumberedProof
    writeFile fout $ result ++ "\n"
