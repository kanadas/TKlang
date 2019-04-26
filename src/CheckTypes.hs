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

throw :: TypeError -> Except TypeError a
throw = throwError

data TypeError = Undefined Expr | TypeError [TAlg] [TAlg] | WrongExpression Expr | UnboundVariable Ident | NotConcreteType TAlg | UnsupportedType Type

instance Show TypeError where
    show te = case te of
        Undefined e -> "Undefined expression: " ++ (render $ prt 0 e)
        TypeError t1 t2 -> "Type mismatch: " ++ show t1 ++ " and " ++ show t2
        WrongExpression e -> "Wrong expression: " ++ (render $ prt 0 e)
        UnboundVariable (Ident ident) -> "Unbound variable " ++ ident
        NotConcreteType t -> "Not concrete type: " ++ show t
        UnsupportedType t -> "Unsupported type: " ++ (render $ prt 0 t)

data ArrOp = Union | Prod | Fun deriving Eq

instance Show ArrOp where
    show x = case x of
        Union -> "+"
        Prod -> "*"
        Fun -> "->"

newtype TVar = TV Integer deriving (Show, Eq, Ord)

data TAlg = TCon TBasic | TArr TAlg ArrOp TAlg | TVar TVar  deriving Eq

instance Show TAlg where
    show t = case t of
        TCon b -> show b
        TArr t1 o t2 -> "(" ++ show t1 ++ ")" ++ show o ++ "(" ++ show t2 ++ ")"
        TVar (TV n)-> "#" ++ show n

type Env = Map Ident TAlg

type Constraint = (TAlg, TAlg)

type Infer a = RWST Env [Constraint] Integer (Except TypeError) a

fresh :: Infer TAlg
fresh = do
    s <- get
    put $ s + 1
    return $ TVar $ TV $ s

withVal :: Ident -> TAlg -> Infer a -> Infer a
withVal ident t e = do
    let nenv env = Map.insert ident t (Map.delete ident env)
    local nenv e

getEnv :: Ident -> Infer TAlg
getEnv ident = do
    env <- ask
    case Map.lookup ident env of
        Just v -> return v
        Nothing -> lift $ throw $ UnboundVariable ident

addCon :: TAlg -> TAlg -> Infer ()
addCon a b = tell [(a,b)]

emptyUnion :: Integer -> Infer TAlg
emptyUnion n = do
    v1 <- if n == 2 then fresh else emptyUnion $ n - 1
    v2 <- fresh
    return $ TArr v1 Union v2 

inferExpr :: Expr -> Infer TAlg
inferExpr x = case x of
    EInt _ -> return $ TCon TInt
    EChar _ -> return $ TCon TChar
    EString _ -> lift $ throw $ Undefined x
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
    ELambda (ident:rest) expr -> do
        v <- fresh 
        let e2 = if rest == [] then inferExpr expr else inferExpr $ ELambda rest expr
        t <- withVal ident v e2
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
        v <- fresh
        addCon v t
        withVal ident v (inferExpr expr2)
    EType expr type_ -> do
        t1 <- inferExpr expr
        t2 <- inferType type_
        addCon t1 t2
        return t2

inferType :: Type -> Infer TAlg
inferType x = case x of
    TBasic basic -> return $ TCon $ matchBasic basic
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

type Subst = Map TVar TAlg

type Solve a = Except TypeError a

class Substitutable a where
    apply :: Subst -> a -> a
    ftv   :: a -> Set TVar

instance Substitutable TAlg where
    apply _ (TCon a) = TCon a
    apply s t@(TVar a) = Map.findWithDefault t a s
    apply s (TArr t1 o t2) = TArr (apply s t1) o (apply s t2)

    ftv (TCon _) = Set.empty
    ftv (TVar a) = Set.singleton a
    ftv (TArr t1 _ t2) = Set.union (ftv t1)  (ftv t2)

instance Substitutable a => Substitutable [a] where
    apply = fmap . apply
    ftv = foldr (Set.union . ftv) Set.empty

--Assuming arguments doesn't have the same keys
compose :: Subst -> Subst -> Subst
compose s1 s2 = Map.map (apply s1) s2 `Map.union` s1

unify :: TAlg -> TAlg -> Solve Subst
unify (TArr l o r) (TArr l' o' r') | o == o' = unifyMany [l, r] [l', r'] 
unify (TVar a) t = bind a t
unify t (TVar a) = bind a t
unify (TCon a) (TCon b) | a == b = return $ Map.empty
unify t1 t2 = throw $ TypeError [t1] [t2]

unifyMany :: [TAlg] -> [TAlg] -> Solve Subst
unifyMany [] [] = return $ Map.empty
unifyMany (t1 : r1) (t2 : r2) = do
        s1 <- unify t1 t2
        s2 <- unifyMany (apply s1 r1) (apply s1 r2)
        return (compose s2 s1)
unifyMany t1 t2 = throw $ TypeError t1 t2

bind ::  TVar -> TAlg -> Solve Subst
bind a t | t == TVar a     = return $ Map.empty
         | occursCheck a t = throw $ TypeError [TVar a] [t]
         | otherwise       = return $ Map.singleton a t

occursCheck ::  Substitutable a => TVar -> a -> Bool
occursCheck a t = a `Set.member` ftv t

concreteType :: TAlg -> Bool
concreteType t = case t of
    TCon _ -> True
    TArr t1 _ t2 -> concreteType t1 && concreteType t2
    _ -> False

solveExp :: Expr -> Except TypeError ()
solveExp expr = do
    (_, cons) <- evalRWST (inferExpr expr) Map.empty 0
    sub <- unifyMany (map fst cons) (map snd cons)
    foldM (\_ t -> if concreteType t then return () else throw $ NotConcreteType t) () sub

