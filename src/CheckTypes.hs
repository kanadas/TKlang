--v0.1 just basic types, static typing
--TODO Unions should be commpatible with longer (but not shorter) ones with the same prefix
{-# LANGUAGE FlexibleContexts #-} --for fresh
module CheckTypes(
     TypeError
    ,TAlg
    ,solveExp
    ) where

import AbsGrammar
import PrintGrammar
--import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Trans
import Control.Monad.RWS
import Control.Monad.Except
import Control.Monad.State

data TypeError = Undefined Expr | TypeError [TAlg] [TAlg] [Expr] | WrongExpression Expr | UnboundVariable Ident | NotConcreteType TAlg | UnsupportedType Type

instance Show TypeError where
    show te = case te of
        Undefined e -> "Undefined expression: " ++ (render $ prt 0 e)
        TypeError t1 t2 [] -> "Type mismatch: " ++ show t1 ++ " and " ++ show t2 
        TypeError t1 t2 e -> "Type mismatch: " ++ show t1 ++ " and " ++ show t2 ++ " in expression:\n" ++ (render $ prt 0 e)
        WrongExpression e -> "Wrong expression: " ++ (render $ prt 0 e) ++ "\n" ++ show e
        UnboundVariable (Ident ident) -> "Unbound variable " ++ ident
        NotConcreteType t -> "Not concrete type: " ++ show t
        UnsupportedType t -> "Unsupported type: " ++ (render $ prt 0 t)

newtype TVar = TV Integer deriving (Show, Eq, Ord)

data TAlg = Con TBasic 
        | Var TVar
        | Prod [TAlg] 
        | Union [TAlg]
        | Fun TAlg TAlg
        | Rec TVar TAlg --TVar needs to be fresh
        deriving Eq

instance Show TAlg where
    show tt = case tt of
        Con b -> show b
        Var (TV n) -> "#" ++ show n
        Prod l -> "(" ++ (init $ foldl (\s t -> s ++ (show t) ++ "*") "" l) ++ ")"
        Union l -> "(" ++ (init $ foldl (\s t -> s ++ (show t) ++ "+") "" l) ++ ")"
        Fun a b -> show a ++ "->" ++ show b
        Rec v t -> "(" ++ show v ++ "." ++ show t ++ ")"

type Env = Map Ident TAlg

type Constraint = (TAlg, TAlg, Expr) --To debug

type Infer a = RWST Env [Constraint] Integer (Except TypeError) a

freshV :: (MonadState Integer m) => m TVar
freshV = do
    s <- get
    put $ s + 1
    return $ TV $ s

--fresh :: Infer TAlg
fresh :: (MonadState Integer m) => m TAlg
fresh = Var <$> freshV 

withVal :: Ident -> TAlg -> Infer a -> Infer a
withVal ident t e = do
    let nenv env = Map.insert ident t (Map.delete ident env)
    local nenv e

getEnv :: Ident -> Infer TAlg
getEnv ident = do
    env <- ask
    case Map.lookup ident env of
        Just v -> return v
        Nothing -> throwError $ UnboundVariable ident

addCon :: Expr -> TAlg -> TAlg -> Infer ()
addCon e a b = tell [(a,b,e)]

emptyUnion :: Integer -> Infer [TAlg]
emptyUnion n
    | n > 2 = do
        v <- fresh
        l <- emptyUnion (n-1)
        return $ (v:l)
    | n == 2 = do
        v1 <- fresh
        v2 <- fresh
        return $ [v1, v2]

inferExpr :: Expr -> Infer TAlg
inferExpr x = case x of
    EInt _ -> return $ Con TInt
    EChar _ -> return $ Con TChar
    EString _ -> throwError $ Undefined x
    EIdent ident -> getEnv ident
    ETrue -> return $ Con TBool
    EFalse -> return $ Con TBool
    EVoid -> return $ Con TVoid
    EEmpty -> throwError $ Undefined x
    ENot expr -> do
        t <- inferExpr expr
        addCon x t (Con TBool)
        return $ Con TBool
    ETuple _ [] -> throwError $ WrongExpression x 
    ETuple expr exprs -> do
        l <- sequence $ map inferExpr (expr:exprs)
        return $ Prod l
    EList exprs -> throwError $ Undefined x
    ELambda [] _ -> throwError $ WrongExpression x
    ELambda (ident:rest) expr -> do
        v <- fresh 
        let e2 = if rest == [] then inferExpr expr else inferExpr $ ELambda rest expr
        t <- withVal ident v e2
        return $ Fun v t
    EApp expr1 expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        v <- fresh
        addCon x t1 (Fun t2 v)
        return v
    EMul expr1 expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        addCon x t1 (Con TInt)
        addCon x t2 (Con TInt)
        return $ Con TInt
    EDiv expr1 expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        addCon x t1 (Con TInt)
        addCon x t2 (Con TInt)
        return $ Con TInt
    EAdd expr1 expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        addCon x t1 (Con TInt)
        addCon x t2 (Con TInt)
        return $ Con TInt
    ESub expr1 expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        addCon x t1 (Con TInt)
        addCon x t2 (Con TInt)
        return $ Con TInt
    EConcat expr1 expr2 -> throwError $ Undefined x
    ENeg expr -> do
        t <- inferExpr expr
        addCon x t (Con TInt)
        return $ Con TInt
    ERel expr1 relop expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        if relop /= eq then
            addCon x t1 (Con TInt) >>
            addCon x t2 (Con TInt)
        else addCon x t1 t2
        return $ Con TBool
    EAnd expr1 expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        addCon x t1 (Con TBool)
        addCon x t2 (Con TBool)
        return $ Con TBool
    EOr expr1 expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        addCon x t1 (Con TBool)
        addCon x t2 (Con TBool)
        return $ Con TBool
    EAppend expr1 expr2 -> throwError $ Undefined x
    EUnion (EInt n) expr2 
        | n <= 0 -> throwError $ WrongExpression x
        | n > 2 -> do
            l <- emptyUnion (n - 1)
            t <- inferExpr expr2
            return $ Union (l ++ [t]) 
        | otherwise -> do
            t1 <- inferExpr expr2
            t2 <- fresh
            if n == 1 then return $ Union [t1, t2] else return $ Union [t2, t1]
    EUnion _ _ -> throwError $ WrongExpression x
    EIf expr1 expr2 expr3 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        t3 <- inferExpr expr3
        addCon x t1 (Con TBool)
        addCon x t2 t3
        return t3
    ELet ident expr1 expr2 -> do 
        v <- fresh
        t <- withVal ident v (inferExpr expr1)
        addCon x v t
        withVal ident v (inferExpr expr2)
    EType expr type_ -> do
        t1 <- inferExpr expr
        t2 <- inferType type_
        addCon x t1 t2
        return t2

--Assuming parsing is left-recursive
inferType :: Type -> Infer TAlg
inferType x = case x of
    TBasic basic -> return $ Con $ matchBasic basic
    TIdent ident -> throwError $ UnsupportedType x
    TProduct type_1 type_2 -> do 
        t1 <- inferType type_1
        t2 <- inferType type_2
        case t1 of
            Prod l -> return $ Prod $ l ++ [t2]
            _ -> return $ Prod [t1, t2]
    TUnion type_1 type_2 -> do
        t1 <- inferType type_1
        t2 <- inferType type_2
        case t1 of
            Union l -> return $ Union $ l ++ [t1]
            _ -> return $ Union [t1, t2]
    TFun type_1 type_2 -> do
        t1 <- inferType type_1
        t2 <- inferType type_2
        return $ Fun t1 t2
    TList type_ -> throwError $ UnsupportedType x

type Subst = Map TVar TAlg

type Solve a = StateT Integer (Except TypeError) a

class Substitutable a where
    apply :: Subst -> a -> a
    ftv   :: a -> Set TVar

instance Substitutable TAlg where
    apply _ (Con a) = Con a
    apply s t@(Var a) = Map.findWithDefault t a s
    apply s (Prod l) = Prod $ apply s l
    apply s (Union l) = Union $ apply s l
    apply s (Fun t1 t2) = Fun (apply s t1) (apply s t2)
    apply s (Rec x t) = Rec x (apply s t)

    ftv (Con _) = Set.empty
    ftv (Var a) = Set.singleton a
    ftv (Prod l) = ftv l
    ftv (Union l) = ftv l
    ftv (Fun t1 t2) = Set.union (ftv t1) (ftv t2)
    ftv (Rec v t) = Set.delete v (ftv t)

instance Substitutable a => Substitutable [a] where
    apply = fmap . apply
    ftv = foldr (Set.union . ftv) Set.empty

--Assuming arguments doesn't have the same keys
compose :: Subst -> Subst -> Subst
compose s1 s2 = Map.map (apply s1) s2 `Map.union` s1

unify :: TAlg -> TAlg -> Expr -> Solve Subst
unify (Prod l1) (Prod l2) e = unifyMany l1 l2 (replicate (length l2) e) 
unify (Union l1) (Union l2) e = unifyMany l1 l2 (replicate (length l2) e)
unify (Fun l1 r1) (Fun l2 r2) e = unifyMany [l1, r1] [l2, r2] [e, e]
unify (Var a) t _ = bind a t
unify t (Var a) _ = bind a t
unify (Con a) (Con b) _ | a == b = return $ Map.empty
unify t1@(Rec _ _) t2@(Con _) e = throwError $ TypeError [t2] [t1] [e]
unify (Rec v1 t1) (Rec v2 t2) e = unify t1 (apply (Map.singleton v2 (Var v1)) t2) e
unify t1 t2@(Rec v t) e = unify t1 (apply (Map.singleton v t2) t) e
unify t2@(Rec v t) t1 e = unify t1 (apply (Map.singleton v t2) t) e
unify t1 t2 e = throwError $ TypeError [t1] [t2] [e]

unifyMany :: [TAlg] -> [TAlg] -> [Expr] -> Solve Subst
unifyMany [] [] _ = return $ Map.empty
unifyMany (t1 : r1) (t2 : r2) (e : et) = do
    s1 <- unify t1 t2 e
    s2 <- unifyMany (apply s1 r1) (apply s1 r2) et
    return (compose s2 s1)
unifyMany t1 t2 e = throwError $ TypeError t1 t2 e

bind :: TVar -> TAlg -> Solve Subst
bind a t | t == Var a = return $ Map.empty
         | occursCheck a t = do
            v <- freshV
            let nt = Rec v (apply (Map.singleton a (Var v)) t)
            return $ Map.singleton a nt
         | otherwise = return $ Map.singleton a t

occursCheck ::  Substitutable a => TVar -> a -> Bool
occursCheck a t = a `Set.member` ftv t

concreteType :: TAlg -> Bool
concreteType = Set.null . ftv

solveExp :: Expr -> Except TypeError ()
solveExp expr = do
    (s, cons) <- execRWST (inferExpr expr) Map.empty 0
    sub <- evalStateT (unifyMany (map (\(x,_,_) -> x) cons) (map (\(_,y,_) -> y) cons) (map (\(_,_,z) -> z) cons)) s
    foldM (\_ t -> if concreteType t then return () else throwError $ NotConcreteType t) () sub

