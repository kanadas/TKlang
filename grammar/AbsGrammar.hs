

module AbsGrammar where

-- Haskell module generated by the BNF converter




newtype Ident = Ident String deriving (Eq, Ord, Show, Read)
newtype RelOp = RelOp String deriving (Eq, Ord, Show, Read)
data Lit
    = LitInteger Integer
    | LitChar Char
    | LitString String
    | LitIdent Ident
    | Lit_true
    | Lit_false
    | Lit1
    | Lit2
  deriving (Eq, Ord, Show, Read)

data Expr
    = ELit Lit
    | ENot Expr
    | ETuple Expr [Expr]
    | EList [Expr]
    | ELambda [Ident] Expr
    | EApp Expr Expr
    | EMul Expr Expr
    | EDiv Expr Expr
    | EAdd Expr Expr
    | ESub Expr Expr
    | EConcat Expr Expr
    | ENeg Expr
    | ERel Expr RelOp Expr
    | EAnd Expr Expr
    | EOr Expr Expr
    | EAppend Expr Expr
    | EUnion Expr Expr
    | EIf Expr Expr Expr
    | EType Expr Type
  deriving (Eq, Ord, Show, Read)

data Basic
    = Basic_int
    | Basic_bool
    | Basic_char
    | Basic_void
    | BasicIdent Ident
  deriving (Eq, Ord, Show, Read)

data Type
    = TBasic Basic
    | TProduct Type Type
    | TUnion Type Type
    | TFun Type Type
    | TList Type
  deriving (Eq, Ord, Show, Read)

