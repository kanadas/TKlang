module Main where

import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )
import System.Exit ( exitFailure, exitSuccess )
import Control.Monad (when)
import Data.Map (Map)
import Control.Monad.Trans
import Control.Monad.Trans.State
import qualified Data.Map as Map

import LexGrammar
import ParGrammar
import ComputeGrammar
import PrintGrammar
import AbsGrammar
import ErrM

type ParseFun a = [Token] -> Err a

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

runFile :: Verbosity -> ParseFun Expr -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run :: Verbosity -> ParseFun Expr -> String -> IO ()
run v p s = 
    let ts = myLexer s in case p ts of
        Bad s -> do 
            putStrLn "\nParse              Failed...\n"
            --putStrV v "Tokens:"
            --putStrV v $ show ts
            putStrLn s
            exitFailure
        Ok tree -> do 
            case evalStateT (compExpr tree) Map.empty of
                Right v -> putStrLn (show v) >> exitSuccess
                Left err -> putStrLn ("Error: " ++ err) >> showTree v tree >> exitFailure

showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    , "  -s (files)      Silent mode. Parse content of files silently."
    ]
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    [] -> getContents >>= run 2 pExpr
    "-s":fs -> mapM_ (runFile 0 pExpr) fs
    fs -> mapM_ (runFile 2 pExpr) fs





