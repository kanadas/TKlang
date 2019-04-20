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
transLit :: Lit -> Result
transLit x = case x of
  LitInteger integer -> failure x
  LitChar char -> failure x
  LitString string -> failure x
  LitIdent ident -> failure x
  Lit_true -> failure x
  Lit_false -> failure x
  Lit1 -> failure x
  Lit2 -> failure x
transExpr :: Expr -> Result
transExpr x = case x of
  ELit lit -> failure x
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
  ERel expr1 relop expr2 -> failure x
  EAnd expr1 expr2 -> failure x
  EOr expr1 expr2 -> failure x
  EAppend expr1 expr2 -> failure x
  EUnion expr1 expr2 -> failure x
  EIf expr1 expr2 expr3 -> failure x
  EType expr type_ -> failure x
transBasic :: Basic -> Result
transBasic x = case x of
  Basic_int -> failure x
  Basic_bool -> failure x
  Basic_char -> failure x
  Basic_void -> failure x
  BasicIdent ident -> failure x
transType :: Type -> Result
transType x = case x of
  TBasic basic -> failure x
  TProduct type_1 type_2 -> failure x
  TUnion type_1 type_2 -> failure x
  TFun type_1 type_2 -> failure x
  TList type_ -> failure x

