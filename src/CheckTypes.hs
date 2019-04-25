--v0.1 just basic types, static typing
--TODO Type unions and products should be lists
module CheckTypes where

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

data TypeError = Undefined Expr | TypeError Expr TAlg TAlg | WrongExpression Expr | UnboundVariable Ident | UnsupportedType Type

instance Show TypeError where
    show t = case t of
        Undefined e -> "Undefined expression: " ++ render $ prt 0 e
        TypeError e t1 t2 -> "Type mismatch: " ++ show t1 ++ " and " ++ show t2 ++ " in: " ++ render $ prt 0 e
        WrongExpression e -> "Wrong expression: " ++ render $ prt 0 e
        UnboundVariable (Ident id) -> "Unbound variable " ++ id ++ " in " ++ render $ prt 0 e
        UnsupportedType t -> "Unsupported type: " + render $ prt 0 t

data ArrOp = Union | Prod | Fun deriving Eq

instance Show ArrOp where
    show x = case x of
        Union -> "+"
        Prod -> "*"
        Fun -> "->"

newtype TVar = TV Int

data TAlg = TCon TBasic | TArr TAlg ArrOp TAlg | TVar TVar 

instance Show TAlg where
    show t = case t of
        TCon b -> show b
        TArr t1 o t2 -> "(" ++ show t1 ++ ")" ++ show o ++ "(" ++ show t2 ++ ")"
        TVar (TV n)-> "#" ++ show n

type Env = Map Ident TVar

type Constraint = (TAlg, TAlg)

type Infer a = RWST Env [Constraint] Int (Except TypeError) a

fresh :: Infer TAlg
fresh = do
    s <- get
    put $ s + 1
    return $ TVar $ TV $ s

withVal :: Ident -> TAlg -> Infer a -> Infer a
withVal id t e = do
    let nenv env = Map.insert id e (Map.delete id env)
    local nenv e

getEnv :: Env -> Indent -> Infer TAlg
getEnv env id = do
    case Map.lookup id env of
        Just v -> return $ TVar v
        Nothing -> lift $ throw $ UnboundVariable id

addCon :: TAlg -> TAlg -> Infer ()
addCon a b = tell [(a,b)]

emptyUnion :: Int -> Infer TAlg
emptyUnion n = do
    v1 <- if n == 2 then fresh else emptyUnion $ n - 1
    v2 <- fresh
    return $ TArr v1 Union v2 

inferExpr :: Expr -> Infer TAlg
inferExpr x = case x of
    EInt _ -> return $ TCon TInt
    EChar char -> return $ TCon TChar
    EString string -> lift $ throw $ Undefined x
    EIdent ident -> getEnv ident
    ETrue -> return $ TCon TBool
    EFalse -> return $ TCon TBool
    EVoid -> return $ TCon TVoid
    EEmpty -> lift $ throw $ Undefined x
    ENot expr -> do
        t <- inferExpr expr
        addCon t (TCon TBool)
        return $ TCon TBool
    ETuple expr exprs -> do
        t1 <- inferExpr expr
        t2 <- case exprs of
            [expr2] -> inferExpr expr2
            expr2:xs -> inferExpr $ ETuple expr2 xs
            [] -> lift $ throw $ WrongExpression x
        return $ TArr t1 Prod t2
    EList exprs -> lift $ throw $ Undefined x
    ELambda [] _ -> lift $ throw $ WrongExpression x
    ELambda (id:rest) expr -> do
        v <- fresh 
        let e2 = if rest == [] then inferExpr expr else inferExpr $ ELambda rest expr
        t <- withVal id v e2
        return $ TArr v Fun t
    EApp expr1 expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        v <- fresh
        addCon t1 (TArr t2 Fun v)
        return v
    EMul expr1 expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        addCon t1 (TCon TInt)
        addCon t2 (TCon TInt)
        return $ TCon TInt
    EDiv expr1 expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        addCon t1 (TCon TInt)
        addCon t2 (TCon TInt)
        return $ TCon TInt
    EAdd expr1 expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        addCon t1 (TCon TInt)
        addCon t2 (TCon TInt)
        return $ TCon TInt
    ESub expr1 expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        addCon t1 (TCon TInt)
        addCon t2 (TCon TInt)
        return $ TCon TInt
    EConcat expr1 expr2 -> lift $ throw $ Undefined x
    ENeg expr -> do
        t <- inferExpr expr
        addCon t (TCon TInt)
        return $ TCon TInt
    ERel expr1 relop expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        addCon t1 (TCon TInt)
        addCon t2 (TCon TInt)
        return $ TCon TBool
    EAnd expr1 expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        addCon t1 (TCon TBool)
        addCon t2 (TCon TBool)
        return $ TCon TBool
    EOr expr1 expr2 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        addCon t1 (TCon TBool)
        addCon t2 (TCon TBool)
        return $ TCon TBool
    EAppend expr1 expr2 -> lift $ throw $ Undefined x
    EUnion (EInt n) expr2 | n <= 0 -> lift $ throw $ WrongExpression x
                          | otherwise -> do
        t1 <- if n > 2 then emptyUnion (n - 1) else fresh
        t2 <- inferExpr expr2
        return $ if n > 1 then TArr t1 Union t2 else TArr t2 Union t1
    EUnion _ _ -> lift $ throw $ WrongExpression x
    EIf expr1 expr2 expr3 -> do
        t1 <- inferExpr expr1
        t2 <- inferExpr expr2
        t3 <- inferExpr expr3
        addCon t1 (TCon TBool)
        addCon t2 t3
        return t3
    ELet ident expr1 expr2 -> do 
        t <- inferExpr expr1
        --v <- fresh
        --addCon v t1
        withVal ident t (inferExpr expr2)
    EType expr type_ -> do
        t1 <- inferExpr expr
        t2 <- inferType type_
        addCon t1 t2
        return t2

inferType :: Type -> Infer TAlg
inferType x = case x of
    TBasic basic -> return $ TCon basic
    TIdent ident -> lift $ throw $ UnsupportedType x
    TProduct type_1 type_2 -> do
        t1 <- inferType type_1
        t2 <- inferType type_2
        return $ TArr t1 Prod t2
    TUnion type_1 type_2 -> do
        t1 <- inferType type_1
        t2 <- inferType type_2
        return $ TArr t1 Union t2
    TFun type_1 type_2 -> do
        t1 <- inferType type_1
        t2 <- inferType type_2
        return $ TArr t1 Fun t2
    TList type_ -> lift $ throw $ UnsupportedType x


--class Substitutable a where
--    apply :: Subst -> a -> a
--    ftv   :: a -> Set TAlg
--
--instance Substitutable TAlg where
--    apply _ (TCon a) = TCon a
--    apply s t@(TVar a) = Map.findWithDefault t a s
--    apply s (TArr o t1 t2) = TArr o (apply s t1) (apply s t2)
--
--    ftv TCon = Set.empty
--    ftv (TVar a) = Set.singleton a
--    ftv (TArr _ t1 t2) = Set.union (ftv t1)  (ftv t2)
--
--compose :: Subst -> Subst -> Subst
--compose s1 s2 = Map.map (apply s1) s2 `Map.union` s1
--
--unify :: TAlg -> TAlg -> Result
--unify a@(TArr o l r) b@(TArr o' l' r') = 
--    if o == o' then do
--        s1 <- unify l l'
--        s2 <- unify (apply s1 r) (apply s1 r')
--        return (compose s2 s1)
--    else 
--        failure $ "Cannot unify " ++ show a ++ " and " ++ show b
--unify (TVar a) t = bind a t
--unify t (TVar a) = bind a t
--unify (TCon a) (TCon b) | a == b = return nullSubst
--unify t1 t2 = failure $ "Cannot unify " ++ show t1 ++ " and " ++ show t2
--
--bind ::  TVar -> TAlg -> Result
--bind a t | t == TVar a     = return nullSubst
--         | occursCheck a t = failure $ "Infinite type: " ++ show a ++ " = " ++ show t
--         | otherwise       = return $ Map.singleton a t
--
--occursCheck ::  Substitutable a => TVar -> a -> Bool
--occursCheck a t = a `Set.member` ftv t


