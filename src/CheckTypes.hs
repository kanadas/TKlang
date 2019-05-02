--v0.1 just basic types, static typing
--TODO Unions should be commpatible with longer (but not shorter) ones with the same prefix
{-# LANGUAGE FlexibleContexts #-} --for fresh
module CheckTypes(
     TypeError
    ,TAlg
    ,solveExpr
    ,TBasic
    ,matchBasic
    ,inferProgram
    ) where


--TODO stream application

import AbsGrammar
import PrintGrammar
--import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
--import Control.Monad.Trans
import Control.Monad.RWS
import Control.Monad.Except
import Control.Monad.State

data TypeError = 
      Undefined String 
    | TypeError [TAlg] [TAlg] [Expr] 
    | WrongExpression Expr 
    | UnboundVariable Ident 
    | NotConcreteType TAlg 
    | UnsupportedType Type 
    | UndefinedType Ident
    | NotAStream Ident Expr
    | NotStreamField Ident Ident Expr
    | Bug String

instance Show TypeError where
    show te = case te of
        Undefined e -> "Undefined expression: " ++ e
        TypeError t1 t2 [] -> "Type mismatch: " ++ show t1 ++ " and " ++ show t2 
        TypeError t1 t2 e -> "Type mismatch: " ++ show t1 ++ " and " ++ show t2 ++ " in expression:\n" ++ (render $ prt 0 e)
        WrongExpression e -> "Wrong expression: " ++ (render $ prt 0 e) ++ "\n" ++ show e
        UnboundVariable (Ident ident) -> "Unbound variable " ++ ident
        NotConcreteType t -> "Not concrete type: " ++ show t
        UnsupportedType t -> "Unsupported type: " ++ (render $ prt 0 t)
        UndefinedType ident -> "Undefined type: " ++ show ident
        NotAStream ident e -> show ident ++ " is not a stream in: " ++ (render $ prt 0 e)
        NotStreamField id1 id2 e -> show id2 ++ " is not field of " ++ show id1 ++ " in: " ++ (render $ prt 0 e)
        Bug s -> "!!!BUG!!! " ++ s

newtype TVar = TV Integer deriving (Show, Eq, Ord)

data TBasic = TInt | TChar | TBool | TVoid deriving Eq

instance Show TBasic where
    show t = case t of
        TInt -> "int"
        TChar -> "char"
        TBool -> "bool"
        TVoid -> "void"

matchBasic :: Basic -> TBasic
matchBasic (Basic s) = case s of
    "int" -> TInt
    "char" -> TChar
    "bool" -> TBool
    "void" -> TVoid

type Mapping = Map Ident TAlg

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

data TStream = TStream [Ident] (Map Ident TAlg)

data Env = Env {venv :: Mapping, tenv :: Mapping, denv :: Mapping, senv :: Map Ident TStream}

type Constraint = (TAlg, TAlg, Expr) 

type Infer a = RWST Env [Constraint] Integer (Except TypeError) a

freshV :: (MonadState Integer m) => m TVar
freshV = do
    s <- get
    put $ s + 1
    return $ TV $ s

fresh :: (MonadState Integer m) => m TAlg
fresh = Var <$> freshV 

liftVal :: (Mapping -> Mapping) -> Env -> Env
liftVal f (Env ve te de se) = Env (f ve) te de se

liftType :: (Mapping -> Mapping) -> Env -> Env
liftType f (Env ve te de se) = Env ve (f te) de se

liftDecl :: (Mapping -> Mapping) -> Env -> Env
liftDecl f (Env ve te de se) = Env ve te (f de) se

liftStream :: (Map Ident TStream -> Map Ident TStream) -> Env -> Env
liftStream f (Env ve te de se) = Env ve te de (f se)

insertVal :: Ident -> TAlg -> Infer Env
insertVal ident t = asks $ liftVal (Map.insert ident t)

insertDecl :: Ident -> TAlg -> Infer Env
insertDecl ident t = asks $ liftDecl (Map.insert ident t)

insertType :: Ident -> TAlg -> Infer Env
insertType ident t = asks $ liftType (Map.insert ident t)

insertStream :: Ident -> TStream -> Infer Env
insertStream ident t = asks $ liftStream (Map.insert ident t)

withVal :: Ident -> TAlg -> Infer a -> Infer a
withVal ident t e = local (liftVal (Map.insert ident t)) e

--withType :: Ident -> TAlg -> Infer a -> Infer a
--withType ident t e = do
--    let nenv (Env env tenv) = Env env (Map.insert ident t tenv)
--    local nenv e

getEnv :: (Env -> Map Ident a) -> Ident -> Infer a
getEnv f ident = do
    env <- asks f
    case Map.lookup ident env of
        Just v -> return v
        Nothing -> throwError $ UnboundVariable ident

emptyUnion :: Integer -> Infer [TAlg]
emptyUnion n
    | n >= 2 = do
        v <- fresh
        l <- emptyUnion (n-1)
        return $ (v:l)
    | otherwise = sequence [fresh]

listT :: TAlg -> Infer TAlg
listT t = do
    v <- freshV
    return $ Rec v (Union [Prod [t, Var v], Con TVoid])

inferProgram :: Program -> Infer ()
inferProgram x = case x of
    Prog tops -> do
        env <- ask
        foldM_ (\acc top -> local (\_ -> acc) (inferTop top)) env tops

inferTop :: Top -> Infer Env
inferTop x = case x of
  TopVDecl vdecl -> inferVDecl vdecl
  TopTDecl tdecl -> inferTDecl tdecl
  TopDef def -> inferDef def
  TopStream stream -> inferStream stream

inferVDecl :: VDecl -> Infer Env
inferVDecl x = case x of
    DVDecl ident type_ -> do
        t <- inferType type_
        insertDecl ident t

inferTDecl :: TDecl -> Infer Env
inferTDecl x = case x of
    DTDecl ident type_ -> do
        t <- if recursiveType ident type_ then do
                v <- freshV
                t1 <- local (liftType (Map.insert ident (Var v))) (inferType type_)
                return $ Rec v t1
            else inferType type_
        insertType ident t

inferDef :: Def -> Infer Env
inferDef x = case x of
    DDef ident idents expr -> do
        te <- asks denv
        v <- case Map.lookup ident te of
            Just t -> return t
            Nothing -> fresh
        t <- if idents == [] then withVal ident v $ solveExpr expr
            else withVal ident v $ solveExpr (ELambda idents expr)
        insertVal ident t

inferSStmt :: SStmt -> Infer Env
inferSStmt x = case x of
    SDecl vdecl -> inferVDecl vdecl
    SDef (DDef ident idents expr) -> do
        te <- asks denv
        v <- case Map.lookup ident te of
            Just t -> return t
            Nothing -> fresh
        t <- if idents == [] then withVal ident v $ inferExpr expr
            else withVal ident v $ inferExpr (ELambda idents expr)
        insertVal ident t

inferStream :: Stream -> Infer Env
inferStream x = case x of
    DStream ident idents sstmts1 sstmts2 defs -> do
        (env, cons) <- censor (\_ -> []) $ listen $ do 
            e0 <- asks (liftStream (\_ -> Map.empty))
            _ <- foldM (\acc def -> local (\_ -> acc) (inferSStmt (SDef def))) e0 defs
            e1 <- foldM (\acc ident -> getEnv senv ident >>= (\s -> return acc{senv = Map.insert ident s (senv acc)})) e0  idents
            e2 <- foldM (\acc top -> local (\_ -> acc) (inferSStmt top)) e1 sstmts1
            foldM (\acc top -> local (\_ -> acc) (inferSStmt top)) e2 sstmts2
        s <- get
        sub <- lift $ evalStateT (unifyMany (map (\(x,_,_) -> x) cons) (map (\(_,y,_) -> y) cons) (map (\(_,_,z) -> z) cons)) s
        foldM (\_ t -> if concreteType t then return () else throwError $ NotConcreteType t) () sub
        let nenv = apply sub (venv env)
        let out = foldl (\acc sstmt -> case sstmt of {
            SDef (DDef ident _ _) -> Map.insert ident (nenv Map.! ident) acc;
            _ -> acc}) Map.empty sstmts2
        insertStream ident (TStream idents out)


inferExpr :: Expr -> Infer TAlg
inferExpr x = 
    let addCon a b = tell [(a, b, x)] in
    case x of
        EInt _ -> return $ Con TInt
        EChar _ -> return $ Con TChar
        EString _ -> listT $ Con TChar
        EIdent ident -> getEnv venv ident
        EQual (Qual id1 id2) -> do
            (TStream _ v) <- getEnv senv id1
            case Map.lookup id2 v of
                Just t -> return t
                Nothing -> throwError $ NotStreamField id1 id2 x
        ETrue -> return $ Con TBool
        EFalse -> return $ Con TBool
        EVoid -> return $ Con TVoid
        EEmpty -> do
            v <- fresh
            listT v
        ENot expr -> do
            t <- inferExpr expr
            addCon t (Con TBool)
            return $ Con TBool
        ETuple _ [] -> throwError $ WrongExpression x 
        ETuple expr exprs -> do
            l <- sequence $ map inferExpr (expr:exprs)
            return $ Prod l
        EList exprs -> do
            v <- fresh
            mapM_ ((addCon v) <=< inferExpr) exprs
            listT v
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
            addCon t1 (Fun t2 v)
            return v
        EMul expr1 expr2 -> do
            t1 <- inferExpr expr1
            t2 <- inferExpr expr2
            addCon t1 (Con TInt)
            addCon t2 (Con TInt)
            return $ Con TInt
        EDiv expr1 expr2 -> do
            t1 <- inferExpr expr1
            t2 <- inferExpr expr2
            addCon t1 (Con TInt)
            addCon t2 (Con TInt)
            return $ Con TInt
        EAdd expr1 expr2 -> do
            t1 <- inferExpr expr1
            t2 <- inferExpr expr2
            addCon t1 (Con TInt)
            addCon t2 (Con TInt)
            return $ Con TInt
        ESub expr1 expr2 -> do
            t1 <- inferExpr expr1
            t2 <- inferExpr expr2
            addCon t1 (Con TInt)
            addCon t2 (Con TInt)
            return $ Con TInt
        EConcat expr1 expr2 -> do
            v <- fresh
            l <- listT v
            t1 <- inferExpr expr1
            t2 <- inferExpr expr2
            addCon l t1
            addCon l t2
            return l
        ENeg expr -> do
            t <- inferExpr expr
            addCon t (Con TInt)
            return $ Con TInt
        ERel expr1 relop expr2 -> do
            t1 <- inferExpr expr1
            t2 <- inferExpr expr2
            if relop /= eq then
                addCon t1 (Con TInt) >>
                addCon t2 (Con TInt)
            else addCon t1 t2
            return $ Con TBool
        EAnd expr1 expr2 -> do
            t1 <- inferExpr expr1
            t2 <- inferExpr expr2
            addCon t1 (Con TBool)
            addCon t2 (Con TBool)
            return $ Con TBool
        EOr expr1 expr2 -> do
            t1 <- inferExpr expr1
            t2 <- inferExpr expr2
            addCon t1 (Con TBool)
            addCon t2 (Con TBool)
            return $ Con TBool
        EAppend expr1 expr2 -> do
            t1 <- inferExpr expr1
            t2 <- inferExpr expr2
            l <- listT t1
            addCon l t2
            return $ l
        EUnion n expr2 
            | n <= 0 -> throwError $ WrongExpression x
            | otherwise -> do
                l <- emptyUnion (n - 1)
                t <- inferExpr expr2
                if n == 1 then return $ Union (t : l) else return $ Union $ l ++ [t]
        EIf expr1 expr2 expr3 -> do
            t1 <- inferExpr expr1
            t2 <- inferExpr expr2
            t3 <- inferExpr expr3
            addCon t1 (Con TBool)
            addCon t2 t3
            return t3
        ELet ident expr1 expr2 -> do 
            v <- fresh
            t <- withVal ident v (inferExpr expr1)
            addCon v t
            withVal ident v (inferExpr expr2)
        EMatch expr alts -> do
            t <- inferExpr expr
            v <- fresh
            foldM (\_ alt -> do
                (t1, t2) <- inferAlternative alt
                addCon t t1
                addCon v t2) () alts
            return v
        EType expr type_ -> do
            t1 <- inferExpr expr
            t2 <- inferType type_
            addCon t1 t2
            return t2

recursiveType :: Ident -> Type -> Bool
recursiveType ident x = case x of
    TBasic _ -> False
    TIdent ident2 -> ident == ident2
    TProduct t1 t2 -> recursiveType ident t1 || recursiveType ident t2
    TUnion t1 t2 -> recursiveType ident t1 || recursiveType ident t2
    TFun t1 t2 -> recursiveType ident t1 || recursiveType ident t2
    TList t -> recursiveType ident t

--Assuming parsing is left-recursive
inferType :: Type -> Infer TAlg
inferType x = case x of
    TBasic basic -> return $ Con $ matchBasic basic
    TIdent ident -> do
        s <- asks tenv
        case Map.lookup ident s of
            Just v -> return $ v
            Nothing -> throwError $ UndefinedType ident
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
    TList type_ -> inferType type_ >>= listT

inferAlternative :: Alternative -> Infer (TAlg, TAlg)
inferAlternative x = case x of
    MAlternative pattern expr -> do
        (e, t1) <- inferPattern expr pattern
        t2 <- local (liftVal (Map.union e)) (inferExpr expr)
        return (t1, t2)

concatEnv :: Expr -> Map Ident TAlg -> Map Ident TAlg -> Infer (Map Ident TAlg)
concatEnv e e1 e2 = 
    sequence (Map.intersectionWith (\a b -> tell [(a, b, e)]) e1 e2) >> (return $ Map.union e1 e2)

inferPattern :: Expr -> Pattern -> Infer (Map Ident TAlg, TAlg)
inferPattern expr x = let addCon a b = tell [(a, b, expr)] in case x of
    PIdent ident -> do
        v <- fresh
        return (Map.singleton ident v, v)
    PAny -> do
        v <- fresh
        return (Map.empty, v)
    PTuple pattern patterns ->
        foldM (\(env, Prod l) p -> do 
            (e, t) <- inferPattern expr p
            ne <- concatEnv expr e env
            return $ (ne, Prod (t: l)) ) (Map.empty, Prod []) (reverse $ pattern:patterns) 
    PList patterns -> do
        v <- fresh
        l <- listT v
        e <- foldM (\env p -> do
            (e, t) <- inferPattern expr p
            ne <- concatEnv expr e env
            addCon v t
            return ne) Map.empty patterns
        return (e, l)
    PString _ -> do 
        l <- listT $ Con TChar 
        return (Map.empty, l)
    PInt _ -> return (Map.empty, Con TInt)
    PChar _ -> return (Map.empty, Con TChar)
    PTrue -> return (Map.empty, Con TBool)
    PFalse -> return (Map.empty, Con TBool)
    PVoid -> return (Map.empty, Con TVoid)
    PEmpty -> do
        v <- fresh
        l <- listT v
        return (Map.empty, l)
    PListHT pattern1 pattern2 -> do
        (e1, t1) <- inferPattern expr pattern1
        (e2, t2) <- inferPattern expr pattern2
        e3 <- concatEnv expr e1 e2
        l <- listT t1
        addCon l t2
        return (e3, l)
    PUnion n pattern 
        | n <= 0 -> throwError $ WrongExpression expr
        | otherwise -> do
            l <- emptyUnion (n - 1)
            (e, t) <- inferPattern expr pattern
            if n == 1 then return (e, Union (t : l)) else return (e, Union $ l ++ [t])

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

instance Substitutable a => Substitutable (Map b a) where
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

solveExpr :: Expr -> Infer TAlg
solveExpr expr = do
    (v, cons) <- censor (\_ -> []) $ listen $ inferExpr expr 
    s <- get
    sub <- lift $ evalStateT (unifyMany (map (\(x,_,_) -> x) cons) (map (\(_,y,_) -> y) cons) (map (\(_,_,z) -> z) cons)) s
    foldM (\_ t -> if concreteType t then return () else throwError $ NotConcreteType t) () sub
    return $ apply sub v

