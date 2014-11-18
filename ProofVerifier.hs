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
    inputData <- liftM (map (fromJust . parseExpr) . filter (not . null) . splitWith isSpace) $ readFile fin
    mapM_ (nextSt builder) inputData
    --theProof <- findProof builder $ last inputData
    --result <- liftM (intercalate "\n" . map show) $ getNumberedProof theProof
    result <- liftM (intercalate "\n" . map show) $ getFixedProof builder inputData
    writeFile fout $ result ++ "\n"
