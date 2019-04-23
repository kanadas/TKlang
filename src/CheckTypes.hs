--v0.1 just basic types, static typing

module CheckTypes where

import AbsGrammar
--import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Trans
import Control.Monad.Trans.State

data ArrOp = Sum | Prod | Fun deriving Eq

newtype TVar = TV Int

data TAlg = TCon TBasic | TArr ArrOp TAlg TAlg | TVar TVar deriving Show

type Subst = Map TVar TAlg

type TCM s a = StateT s (Either String) a

type Result = TCM Int Subst

newtype IState = IState {count :: Int, subst :: Subst, idmap :: Map Ident TVar}

failure :: Show a => a -> TCM b
failure x = lift $ Left $ show x

undef :: Show a => a -> TCM b
undef x = lift $ Left $ "Undefined case: " ++ show x

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set TAlg

instance Substitutable TAlg where
  apply _ (TCon a) = TCon a
  apply s t@(TVar a) = Map.findWithDefault t a s
  apply s (TArr o t1 t2) = TArr o (apply s t1) (apply s t2)

  ftv TCon = Set.empty
  ftv (TVar a) = Set.singleton a
  ftv (TArr _ t1 t2) = Set.union (ftv t1)  (ftv t2)

compose :: Subst -> Subst -> Subst
compose s1 s2 = Map.map (apply s1) s2 `Map.union` s1

unify :: TAlg -> TAlg -> Result
unify a@(TArr o l r) b@(TArr o' l' r') = 
    if o == o' then do
        s1 <- unify l l'
        s2 <- unify (apply s1 r) (apply s1 r')
        return (compose s2 s1)
    else 
        failure $ "Cannot unify " ++ show a ++ " and " ++ show b
unify (TVar a) t = bind a t
unify t (TVar a) = bind a t
unify (TCon a) (TCon b) | a == b = return nullSubst
unify t1 t2 = failure $ "Cannot unify " ++ show t1 ++ " and " ++ show t2

bind ::  TVar -> TAlg -> Result
bind a t | t == TVar a     = return nullSubst
         | occursCheck a t = failure $ "Infinite type: " ++ show a ++ " = " ++ show t
         | otherwise       = return $ Map.singleton a t

occursCheck ::  Substitutable a => TVar -> a -> Bool
occursCheck a t = a `Set.member` ftv t

fresh :: TCM IState TAlg
fresh = do
  s <- get
  put $ s{count = count s + 1}
  return $ TVar $ TV $ count s

putSubst :: TAlg -> TCM IState TAlg
putSubst e = do
   v <- fresh
   s <- get
   put $ s{subst = Map.insert v e (subst s)}
   return $ TCon v

typeExpr :: Expr -> TCM IState TAlg
typeExpr x = case x of
  EInt _ -> return $ TCon TInt
  EChar char -> return $ TCon TChar
  EString string -> undef x
  EIdent ident -> do
    s <- get
    case Map.lookup ident (idmap s) of
        Just v -> return $ TVar v
        Nothing -> do
            v <- fresh
            return $ TVar v
  ETrue -> return $ TCon TBool
  EFalse -> return $ TCon TBool
  EVoid -> return $ TCon TVoid
  EEmpty -> undef x
  ENot expr -> do
    e <- typeExpr expr
    return $ putSubst e --TODO not sure
  ETuple expr exprs -> do
    e1 <- typeExpr expr
    e2 <- case exprs of
        [expr2] -> typeExpr expr2
        expr2:xs -> typeExpr $ ETuple expr2 xs
        [] -> failure $ "One element in tuple: " ++ show x
    return $ putSubst $ TArr Prod e1 e2
  EList exprs -> undef x
  --TODO from here
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

