{-# LANGUAGE NoImplicitPrelude #-}

import Prelude hiding (readFile, lines)
import ExpressionParser
import Proof
import Data.List hiding (lines)
import Data.ByteString.Char8 hiding (last, writeFile, map, intercalate)
import System.Environment
import Control.Monad
import Data.Maybe

main = do
    builder <- newBuilder
    [fin, fout] <- getArgs
    inputData <- liftM lines $ readFile fin
    mapM_ (nextSt builder . fromJust . parseExpr) inputData
    result <- liftM (intercalate "\n" . map show) $ getNumberedProof builder $ fromJust $ parseExpr $ last inputData
    writeFile fout $ result ++ "\n"
