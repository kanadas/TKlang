module Main where

import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )
import System.Exit ( exitFailure, exitSuccess )
import Control.Monad (when)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Trans
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Except
import Control.Monad.RWS hiding (gets)

import CheckTypes
import LexGrammar
import ParGrammar
import ComputeGrammar
import PrintGrammar
import AbsGrammar
import ErrM

type ParseFun a = [Token] -> Err a

type Verbosity = Int

inputType :: TStream
inputType = TStream [] (Map.singleton (Ident "read") (Con TChar))

startInferEnv :: Env
startInferEnv = Env Map.empty Map.empty Map.empty (Map.singleton (Ident "Input") inputType)

runInputNode :: Char -> StreamNode -> RunStream
runInputNode c this = do


    --liftIO $ putStrLn $ "Running input with char: " ++ [c]
    --liftIO $ putStrLn $ "Inputs: " ++ show (inputs this)
    --liftIO $ putStrLn $ "Outs: " ++ show (outs this)


    s <- gets sstate
    let ident = (Ident "Input")
    updateGraph ident this (Map.insert (ident, (Ident "read")) (VChar c) s)

inputNode :: StreamNode
inputNode = StreamNode (Ident "Input") [] [] (runInputNode '\0')

startCompEnv :: IEnv
startCompEnv = IEnv Map.empty Map.empty (Map.singleton (Ident "Input") inputNode)

runOutputNode :: StreamNode -> RunStream
runOutputNode this = do
    s <- gets sstate
    case Map.lookup (Ident "main", Ident "print") s of
        Just (VChar c) -> liftIO $ putChar c
        _ -> throwError WrongMain
    updateGraph (Ident "Output") this s

outputNode :: StreamNode
outputNode = StreamNode (Ident "Output") [Ident "main"] [] runOutputNode 

processIO :: VEnv -> Map (Ident, Ident) Value -> Map Ident Int -> Map Ident StreamNode -> IO ()
processIO svenv st_sstate scounts sgraph = do

    --putStrLn $ "Starting state: \n" ++ show st_sstate

    input <- getContents
    let result = foldM (\acc c -> fmap sstate $ execStateT (runInputNode c (sgraph Map.! (Ident "Input"))) (REnv svenv acc scounts Map.empty sgraph [])) st_sstate input
    res <- runExceptT result  
    case res of
        Left err -> (putStrLn $ "Runtime error:" ++ show err) >> exitFailure
        Right _ -> exitSuccess

runProgram :: Program -> IO ()
runProgram program =
    case runComp $ runStateT (compProgram program) startCompEnv of
        Left err -> putStrLn ("Error: " ++ (show err)) >> showTree 0 program >> exitFailure
        Right (st_sstate, compEnv) -> case Map.lookup (Ident "main") (graph compEnv) of
            Nothing -> putStrLn ("No main stream. Nothing to do...") >> exitFailure
            Just _ -> 
                let ngraph = Map.update (\n  -> Just n{outs = (Ident "Output"):(outs n)}) (Ident "main") (graph compEnv) in
                let ngraph2 = Map.insert (Ident "Output") outputNode ngraph in
                let scounts = foldl (\acc nod -> Map.insert (name nod) (length $ inputs nod) acc) Map.empty ngraph2 in
                processIO (st_venv compEnv) st_sstate scounts ngraph2

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

runFile :: Verbosity -> ParseFun Program -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= runTree v p

runTree :: Verbosity -> ParseFun Program -> String -> IO ()
runTree v p s = 
    let ts = myLexer s in case p ts of
        Bad s -> do 
            putStrLn "\nParse              Failed...\n"
            --putStrV v "Tokens:"
            --putStrV v $ show ts
            putStrLn s
            exitFailure
        Ok tree ->
            case runExcept $ evalRWST (inferProgram tree) startInferEnv 0 of
                Left e -> putStrLn (show e) >> exitFailure
                Right _ -> runProgram tree

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
--    [] -> getContents >>= runTree 2 pProgram
    [] -> usage
    "-s":fs -> mapM_ (runFile 0 pProgram) fs
    fs -> mapM_ (runFile 2 pProgram) fs





