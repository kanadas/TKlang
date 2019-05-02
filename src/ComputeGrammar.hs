--v0.0.1 just basic types, dynamic typing
{-# LANGUAGE MultiParamTypeClasses #-}
module ComputeGrammar where

--import Debug.Trace

import AbsGrammar
import PrintGrammar
--import Data.Maybe
import Data.Map (Map)
--import Control.Applicative hiding (Alternative)
import Control.Monad.Trans
import Control.Monad.Except
import Control.Monad.Trans.State
import Control.Monad.Trans.Reader
--import Control.Monad.Except
import Control.Monad.Fail
import qualified Data.Map as Map

data CompError = 
      DivisionByZero Expr 
    | Undefined String 
    | NotMatched
    | NoMatch Expr Value
    | Bug String
    deriving Eq

instance Show CompError where
    show ce = case ce of
        DivisionByZero e -> "Division by zero in: " ++ (render $ prt 0 e)
        Undefined e -> "Undefined expression: " ++ e
        NotMatched -> "Not matched"
        NoMatch e v -> "No match for " ++ show v ++ " in: \n" ++ (render $ prt 0 e)
        Bug s -> "!!!BUG!!!: " ++ s

data CompExcept a = CompExcept {runComp :: Either CompError a} deriving Show

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

instance Eq a => Eq (CompExcept a) where
    (==) a b = case (runComp a, runComp b) of
        (Right x, Right y) -> x == y
        _ -> False

instance MonadError CompError CompExcept  where
    throwError = CompExcept . throwError
    catchError x f = CompExcept $ catchError (runComp x) (runComp . f)

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

type VEnv = Map Ident (CompExcept Value)

data Env = Env {venv :: VEnv, sstate :: Map (Ident, Ident) Value, graph :: StreamNode}

liftEnv :: (Map Ident (CompExcept Value) -> Map Ident (CompExcept Value)) -> Env -> Env
liftEnv f e = Env {venv = f (venv e)}

insertEnv :: Ident -> CompExcept Value -> Env -> Env
insertEnv i v = liftEnv $ Map.insert i v

type Compute a = ReaderT Env CompExcept a

type ComputeEnv a = StateT Env CompExcept a

data StreamNode = StreamNode {name :: Ident, inputs :: [StreamNode], count :: Integer, outs :: [StreamNode], run :: StateT Env CompExcept Value}

type Result = Compute Value

compIdent :: Ident -> String
compIdent x = case x of
    Ident string -> string
compRelOp :: RelOp -> String
compRelOp x = case x of
    RelOp string -> string
compBasic :: Basic -> String
compBasic x = case x of
    Basic string -> string

compProgram :: Program -> ComputeEnv ()
compProgram x = case x of
    Prog tops -> foldM (\_ top -> compTop top) () tops

compTop :: Top -> ComputeEnv ()
compTop x = case x of
    TopVDecl _ -> return ()
    TopTDecl _ -> return ()
    TopDef def -> compDef def
    TopStream stream -> compStream stream

compDef :: Def -> ComputeEnv ()
compDef x = case x of
    DDef ident idents expr -> do
        s <- get
        let e = if idents == [] then expr else ELambda idents expr
        let f val = runReaderT (compExpr e) (insertEnv ident (f val) s)
        v <- lift $ f $ throw $ Bug "recursion"
        put $ insertEnv ident (return v) s

compSStmt :: SStmt -> ComputeEnv ()
compSStmt x = case x of
    SDecl _ -> return ()
    SDef def -> compDef def

compStream :: Stream -> ComputeEnv ()
compStream x = case x of
    DStream ident idents sstmts1 sstmts2 defs -> throwError $ Undefined $ show x

compExpr :: Expr -> Result
compExpr x = do
    {-s <- get
    trace ("Expression: " ++ show x ++ "\nState: \n" ++ show s) $ -}
    case x of
        EInt integer -> return $ VInt integer
        EChar char -> return $ VChar char
        EString string -> return $ 
            foldr (\e acc -> VUnion 1 (VTuple [VChar e, acc])) (VUnion 2 VVoid) string
        EIdent ident -> do
            s <- asks venv
            lift $ s Map.! ident
        EQual (Qual id1 id2) -> do
            s <- asks sstate
            return $ s Map.! (id1, id2)
        ETrue -> return $ VBool True
        EFalse -> return $ VBool False
        EVoid -> return $ VVoid
        EEmpty -> return $ (VUnion 2 VVoid)
        ENot expr -> do
            (VBool b) <- compExpr expr
            return $ VBool $ not b
        ETuple expr exprs -> VTuple <$> mapM compExpr (expr:exprs) 
        EList exprs -> foldM (\acc expr -> do e <- compExpr expr; return $ VUnion 1 (VTuple [e, acc])) (VUnion 2 VVoid) (reverse exprs)
        ELambda idents expr -> do
            s <- ask
            case idents of
                [ident] -> return $ VFun (\v -> runReaderT (compExpr expr) (insertEnv ident (return v) s))
                ident:rest -> return $
                    VFun (\v -> runReaderT (compExpr (ELambda rest expr)) (insertEnv ident (return v) s))
                [] -> lift $ throw $ Bug $ "Empty lambda not found on type infering: " ++ show x
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
        EConcat expr1 expr2 -> do
            e1 <- compExpr expr1
            e2 <- compExpr expr2
            let con a b = case a of { 
                (VUnion 1 (VTuple [e, t])) -> VUnion 1 (VTuple [e, con t b]); 
                (VUnion 2 VVoid) -> b }
            return $ con e1 e2
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
        EAppend expr1 expr2 -> do
            e1 <- compExpr expr1
            e2 <- compExpr expr2
            return $ VUnion 1 (VTuple [e1, e2])
        EUnion n expr2 -> do
            v2 <- compExpr expr2
            return $ VUnion n v2
        EIf expr1 expr2 expr3 -> do
            (VBool b) <- compExpr expr1
            if b then compExpr expr2 else compExpr expr3
        ELet ident expr1 expr2 -> do
            s <- ask
            let f val = runReaderT (compExpr expr1) (insertEnv ident (f val) s)
            local (insertEnv ident (f $ throw $ Bug "recursion")) (compExpr expr2)
        EMatch expr alts -> do
            v <- compExpr expr
            let f l = case l of {
                h:t -> catchError (compAlternative v h) 
                    (\e -> if e == NotMatched then f t else throwError e); 
                [] -> throwError $ NoMatch x v}
            f alts
        EType expr _ -> compExpr expr

compAlternative :: Value -> Alternative -> Result
compAlternative v x = case x of
    MAlternative pattern expr -> do
        e <- compPattern v pattern
        local (liftEnv (Map.union e)) (compExpr expr)

concatEnv :: VEnv -> VEnv -> Compute VEnv
concatEnv e1 e2 = sequence 
    (Map.intersectionWith (\a b -> if a /= b then lift $ throw NotMatched else return ()) e1 e2) >>
    (return $ Map.union e1 e2)

compPattern :: Value -> Pattern -> Compute VEnv
compPattern (VInt i1) (PInt i2) | i1 == i2 = return Map.empty
compPattern (VBool b1) (PTrue) | b1 = return Map.empty
compPattern (VBool b1) (PFalse) | not b1 = return Map.empty
compPattern (VChar c1) (PChar c2) | c1 == c2 = return Map.empty
compPattern VVoid PVoid = return Map.empty
compPattern (VUnion 2 VVoid) PEmpty = return Map.empty
compPattern (VTuple l1) (PTuple pat ps) = 
    foldM (\acc (v, p) -> compPattern v p >>= concatEnv acc) (Map.empty) (zip l1 (pat:ps))
compPattern (VUnion n1 p1) (PUnion n2 p2) | n1 == n2 = compPattern p1 p2
compPattern (VUnion 1 (VTuple [h1,t1])) (PList (h2:t2)) = do
    e1 <- compPattern h1 h2
    e2 <- if t2 == [] then compPattern t1 (PUnion 2 PVoid) else compPattern t1 (PList t2)
    concatEnv e1 e2
compPattern (VUnion 2 (VVoid)) (PString "") = return Map.empty
compPattern (VUnion 1 (VTuple [c1, t1])) (PString (c2:t2)) | c1 == VChar c2 = 
    compPattern t1 (PString t2)
compPattern v (PIdent ident) = return $ Map.singleton ident (return v)
compPattern _ PAny = return $ Map.empty
compPattern _ _ = lift $ throw NotMatched


