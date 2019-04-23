--v0.0.1 just basic types, dynamic typing

module ComputeGrammar where

import AbsGrammar
--import Data.Maybe
import Data.Map (Map)
import Control.Monad.Trans
import Control.Monad.Trans.State
import qualified Data.Map as Map

data Value = VInt Integer | VChar Char | VBool Bool | VVoid | VFun (Value -> Either String Value)

instance Show Value where
    show v = case v of
        VInt i -> show i
        VChar c -> show c
        VBool b -> show b
        VVoid -> "()"
        VFun _ -> "Function"

type Env = Map Ident Value

type Result = StateT Env (Either String) Value

failure :: Show a => a -> Result
failure x = lift $ Left $ "Undefined case: " ++ show x

compIdent :: Ident -> String
compIdent x = case x of
  Ident string -> string
compRelOp :: RelOp -> String
compRelOp x = case x of
  RelOp string -> string
compBasic :: Basic -> String
compBasic x = case x of
  Basic string -> string

compExpr :: Expr -> Result
compExpr x = case x of
  EInt integer -> return $ VInt integer
  EChar char -> return $ VChar char
  EString string -> failure x
  EIdent ident -> do
    s <- get
    case Map.lookup ident s of
        Just v -> lift $ Right v
        Nothing -> lift $ Left $ "Unknown identifier: " ++ compIdent ident ++ "\n" ++ show x
  ETrue -> return $ VBool True
  EFalse -> return $ VBool False
  EVoid -> return $ VVoid
  EEmpty -> failure x
  ENot expr -> do
    e <- compExpr expr
    case e of
        VBool b -> lift $ Right $ VBool $ not b
        _ -> lift $ Left $ "Not boolean value: " ++ show e ++ "\n" ++ show x
  ETuple expr exprs -> failure x
  EList exprs -> failure x
  ELambda idents expr -> do
    s <- get
    case idents of
        [ident] -> lift $ Right $ VFun (\v -> evalStateT (compExpr expr) (Map.insert ident v s))
        ident:rest -> lift $ Right $ VFun (\v -> evalStateT (compExpr (ELambda rest expr)) (Map.insert ident v s))
        [] -> lift $ Left $ "Zero parameter lambda" ++ show x

  EApp expr1 expr2 -> do
    e1 <- compExpr expr1
    e2 <- compExpr expr2
    case e1 of
        VFun f -> lift $ f e2
        _ -> lift $ Left $ "Not function: " ++ show e1 ++ "\n" ++ show x
  EMul expr1 expr2 -> do
    e1 <- compExpr expr1
    e2 <- compExpr expr2
    case (e1, e2) of
        (VInt i1, VInt i2) -> lift $ Right $ VInt $ i1 * i2
        _ -> lift $ Left $ "Not integer value: " ++ show (e1, e2) ++ "\n" ++ show x
  EDiv expr1 expr2 -> do
    e1 <- compExpr expr1
    e2 <- compExpr expr2
    case (e1, e2) of
        (VInt i1, VInt i2) -> if i2 /= 0 then lift $ Right $ VInt $ div i1 i2 else lift $ Left $ "Division by 0" ++ show x
        _ -> lift $ Left $ "Not integer value: " ++ show (e1, e2) ++ "\n" ++ show x
  EAdd expr1 expr2 -> do
    e1 <- compExpr expr1
    e2 <- compExpr expr2
    case (e1, e2) of
        (VInt i1, VInt i2) -> lift $ Right $ VInt $ i1 + i2 
        _ -> lift $ Left $ "Not integer value: " ++ show (e1,e2) ++ "\n" ++ show x
  ESub expr1 expr2 -> do
    e1 <- compExpr expr1
    e2 <- compExpr expr2
    case (e1, e2) of
        (VInt i1, VInt i2) -> lift $ Right $ VInt $ i1 - i2
        _ -> lift $ Left $ "Not integer value: " ++ show (e1,e2) ++ "\n" ++ show x
  EConcat expr1 expr2 -> failure x
  ENeg expr -> do
    e <- compExpr expr
    case e of
        VInt i -> lift $ Right $ VInt (-i)
        _ -> lift $ Left $ "Not integer value: " ++ show e ++ "\n" ++ show x
  ERel expr1 relop expr2 -> do
    e1 <- compExpr expr1
    e2 <- compExpr expr2
    case (e1, e2) of
        (VInt i1, VInt i2) -> lift $ Right $ VBool (case compRelOp relop of
            ">" -> i1 > i2
            "<" -> i1 < i2
            "<=" -> i1 <= i2
            ">=" -> i1 >= i2
            "==" -> i1 == i2
            "!=" -> i1 /= i2 )
        _ -> lift $ Left $ "Not integer value: " ++ show (e1,e2) ++ "\n" ++ show x
  EAnd expr1 expr2 -> do
    e1 <- compExpr expr1
    e2 <- compExpr expr2
    case (e1, e2) of
        (VBool b1, VBool b2) -> lift $ Right $ VBool $ b1 && b2
        _ -> lift $ Left $ "Not boolean value: " ++ show (e1,e2) ++ "\n" ++ show x
  EOr expr1 expr2 -> do
    e1 <- compExpr expr1
    e2 <- compExpr expr2
    case (e1, e2) of
        (VBool b1, VBool b2) -> lift $ Right $ VBool $ b1 || b2
        _ -> lift $ Left $ "Not integer value: " ++ show (e1,e2) ++ "\n" ++ show x
  EAppend expr1 expr2 -> failure x
  EUnion expr1 expr2 -> failure x
  EIf expr1 expr2 expr3 -> do
    e1 <- compExpr expr1
    case e1 of
        VBool i1 -> if i1 then compExpr expr2 else compExpr expr3
        _ -> lift $ Left $ "Not boolean value: " ++ show e1 ++ "\n" ++ show x
  ELet ident expr1 expr2 -> do --TODO recursion
    e1 <- compExpr expr1
    modify (Map.insert ident e1)
    compExpr expr2
  EType expr type_ -> failure x

compType :: Type -> Result
compType x = case x of
  TBasic basic -> failure x
  TIdent ident -> failure x
  TProduct type_1 type_2 -> failure x
  TUnion type_1 type_2 -> failure x
  TFun type_1 type_2 -> failure x
  TList type_ -> failure x

