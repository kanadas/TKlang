module SkelGrammar where

-- Haskell module generated by the BNF converter

import AbsGrammar
import ErrM
type Result = Err String

failure :: Show a => a -> Result
failure x = Bad $ "Undefined case: " ++ show x

transIdent :: Ident -> Result
transIdent x = case x of
  Ident string -> failure x
transRelOp :: RelOp -> Result
transRelOp x = case x of
  RelOp string -> failure x
transBasic :: Basic -> Result
transBasic x = case x of
  Basic string -> failure x
transProgram :: Program -> Result
transProgram x = case x of
  Prog tops -> failure x
transTop :: Top -> Result
transTop x = case x of
  TopVDecl vdecl -> failure x
  TopTDecl tdecl -> failure x
  TopDef def -> failure x
  TopStream stream -> failure x
transVDecl :: VDecl -> Result
transVDecl x = case x of
  DVDecl ident type_ -> failure x
transTDecl :: TDecl -> Result
transTDecl x = case x of
  DTDecl ident type_ -> failure x
transDef :: Def -> Result
transDef x = case x of
  DDef ident idents expr -> failure x
transExpr :: Expr -> Result
transExpr x = case x of
  EInt integer -> failure x
  EChar char -> failure x
  EString string -> failure x
  EIdent ident -> failure x
  EQual qident -> failure x
  ETrue -> failure x
  EFalse -> failure x
  EUnit -> failure x
  EEmpty -> failure x
  ENot expr -> failure x
  ETuple expr exprs -> failure x
  EList exprs -> failure x
  ELambda idents expr -> failure x
  EApp expr1 expr2 -> failure x
  EMul expr1 expr2 -> failure x
  EDiv expr1 expr2 -> failure x
  EAdd expr1 expr2 -> failure x
  ESub expr1 expr2 -> failure x
  EConcat expr1 expr2 -> failure x
  ENeg expr -> failure x
  EUnion integer expr -> failure x
  ERel expr1 relop expr2 -> failure x
  EAnd expr1 expr2 -> failure x
  EOr expr1 expr2 -> failure x
  EAppend expr1 expr2 -> failure x
  EIf expr1 expr2 expr3 -> failure x
  ELet ident expr1 expr2 -> failure x
  EMatch expr alternatives -> failure x
  EType expr type_ -> failure x
transType :: Type -> Result
transType x = case x of
  TBasic basic -> failure x
  TIdent ident -> failure x
  TList type_ -> failure x
  TProduct type_1 type_2 -> failure x
  TUnion type_1 type_2 -> failure x
  TFun type_1 type_2 -> failure x
transAlternative :: Alternative -> Result
transAlternative x = case x of
  MAlternative pattern expr -> failure x
transPattern :: Pattern -> Result
transPattern x = case x of
  PIdent ident -> failure x
  PAny -> failure x
  PTuple pattern patterns -> failure x
  PList patterns -> failure x
  PString string -> failure x
  PInt integer -> failure x
  PChar char -> failure x
  PTrue -> failure x
  PFalse -> failure x
  PEmpty -> failure x
  PUnit -> failure x
  PListHT pattern1 pattern2 -> failure x
  PUnion integer pattern -> failure x
transQIdent :: QIdent -> Result
transQIdent x = case x of
  Qual ident1 ident2 -> failure x
transSStmt :: SStmt -> Result
transSStmt x = case x of
  SDecl vdecl -> failure x
  SDef def -> failure x
transStream :: Stream -> Result
transStream x = case x of
  DStream ident idents sstmts1 sstmts2 defs -> failure x

