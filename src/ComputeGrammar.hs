--v0.0.1 just basic types, dynamic typing

module ComputeGrammar where

import AbsGrammar
import PrintGrammar
--import Data.Maybe
import Data.Map (Map)
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Except
import Control.Monad.Fail
import qualified Data.Map as Map


data CompError = DivisionByZero Expr | Undefined Expr | Bug String

instance Show CompError where
    show ce = case ce of
        DivisionByZero e -> "Division by zero in: " ++ (render $ prt 0 e)
        Undefined e -> "Undefined expression: " ++ (render $ prt 0 e)
        Bug s -> "!!!BUG!!!: " ++ s

data CompExcept a = CompExcept {runComp :: Either CompError a}

instance Monad CompExcept where
    return a = CompExcept $ return a
    (>>=) (CompExcept m) f = CompExcept $ m >>= runComp.f

instance Functor CompExcept where
  fmap = liftM

instance Applicative CompExcept where
  pure = return 
  (<*>) = ap

throw :: CompError -> CompExcept a
throw = CompExcept . throwError

instance MonadFail CompExcept where
    fail s = throw $ Bug s

data Value = VInt Integer 
            | VChar Char 
            | VBool Bool 
            | VVoid 
            | VFun (Value -> CompExcept Value)
            | VTuple [Value]
            | VUnion Integer Value

instance Eq Value where
    v1 == v2 = case (v1, v2) of
        (VInt a, VInt b) -> a == b
        (VChar a, VChar b) -> a == b
        (VBool a, VBool b) -> a == b
        (VVoid, VVoid) -> True
        (VTuple a, VTuple b) -> a == b
        (VUnion i1 a, VUnion i2 b) -> i1 == i2 && a == b
        (_, _) -> False

instance Show Value where
    show vv = case vv of
        VInt i -> show i
        VChar c -> show c
        VBool b -> show b
        VVoid -> "()"
        VFun _ -> "Function"
        VTuple vl -> "(" ++ foldl (\s v -> s ++ show v ++ ", ") "" vl ++ ")"
        VUnion n v -> show n ++ "@" ++ show v

type Env = Map Ident Value

type Result = StateT Env CompExcept Value

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
    EString string -> lift $ throw $ Undefined x
    EIdent ident -> do
        s <- get
        return $ s Map.! ident
    ETrue -> return $ VBool True
    EFalse -> return $ VBool False
    EVoid -> return $ VVoid
    EEmpty -> lift $ throw $ Undefined x
    ENot expr -> do
        (VBool b) <- compExpr expr
        return $ VBool $ not b
    ETuple expr exprs -> VTuple <$> mapM compExpr (expr:exprs) 
    EList exprs -> lift $ throw $ Undefined x
    ELambda idents expr -> do
        s <- get
        case idents of
            [ident] -> return $ VFun (\v -> evalStateT (compExpr expr) (Map.insert ident v s))
            ident:rest -> return $ 
                VFun (\v -> evalStateT (compExpr (ELambda rest expr)) (Map.insert ident v s))
    EApp expr1 expr2 -> do
        (VFun f) <- compExpr expr1
        e2 <- compExpr expr2
        lift $ f e2
    EMul expr1 expr2 -> do
        (VInt i1) <- compExpr expr1
        (VInt i2) <- compExpr expr2
        return $ VInt $ i1 * i2
    EDiv expr1 expr2 -> do
        (VInt i1) <- compExpr expr1
        (VInt i2) <- compExpr expr2
        if i2 /= 0 then return $ VInt $ div i1 i2 else lift $ throw $ DivisionByZero x
    EAdd expr1 expr2 -> do
        (VInt i1) <- compExpr expr1
        (VInt i2) <- compExpr expr2
        return $ VInt $ i1 + i2 
    ESub expr1 expr2 -> do
        (VInt i1) <- compExpr expr1
        (VInt i2) <- compExpr expr2
        return $ VInt $ i1 - i2
    EConcat expr1 expr2 -> lift $ throw $ Undefined x
    ENeg expr -> do
        (VInt i) <- compExpr expr
        return $ VInt (-i)
    ERel expr1 (RelOp o) expr2 
        | o `elem` ["==", "!="] -> do
            e1 <- compExpr expr1
            e2 <- compExpr expr2
            if o == "==" then return $ VBool (e1 == e2) else return $ VBool (e1 /= e2)
        | otherwise -> do
            (VInt i1) <- compExpr expr1
            (VInt i2) <- compExpr expr2
            return $ VBool ( case o of
                ">" -> i1 > i2
                "<" -> i1 < i2
                ">=" -> i1 <= i2
                "<=" -> i1 >= i2 ) 
    EAnd expr1 expr2 -> do
        (VBool b1) <- compExpr expr1
        (VBool b2) <- compExpr expr2
        return $ VBool $ b1 && b2
    EOr expr1 expr2 -> do
        (VBool b1) <- compExpr expr1
        (VBool b2) <- compExpr expr2
        return $ VBool $ b1 || b2
    EAppend expr1 expr2 -> lift $ throw $ Undefined x
    EUnion expr1 expr2 -> do
        (VInt i1) <- compExpr expr1
        v2 <- compExpr expr2
        return $ VUnion i1 v2
    EIf expr1 expr2 expr3 -> do
        (VBool b) <- compExpr expr1
        if b then compExpr expr2 else compExpr expr3
    ELet ident expr1 expr2 -> do --TODO recursion
        e1 <- compExpr expr1
        modify (Map.insert ident e1)
        compExpr expr2
    EType expr _ -> compExpr expr

