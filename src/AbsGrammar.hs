

module AbsGrammar where

-- Haskell module generated by the BNF converter




newtype Ident = Ident String deriving (Eq, Ord, Show, Read)
newtype RelOp = RelOp String deriving (Eq, Ord, Show, Read)
newtype Basic = Basic String deriving (Eq, Ord, Show, Read)
data Program = Prog [Top]
  deriving (Eq, Ord, Show, Read)

data Top
    = TopVDecl VDecl | TopTDecl TDecl | TopDef Def | TopStream Stream
  deriving (Eq, Ord, Show, Read)

data VDecl = DVDecl Ident Type
  deriving (Eq, Ord, Show, Read)

data TDecl = DTDecl Ident Type
  deriving (Eq, Ord, Show, Read)

data Def = DDef Ident [Ident] Expr
  deriving (Eq, Ord, Show, Read)

data Expr
    = EInt Integer
    | EChar Char
    | EString String
    | EIdent Ident
    | EQual QIdent
    | ETrue
    | EFalse
    | EUnit
    | EEmpty
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
    | EUnion Integer Expr
    | EIf Expr Expr Expr
    | ELet Ident Expr Expr
    | EMatch Expr [Alternative]
    | EType Expr Type
  deriving (Eq, Ord, Show, Read)

gt, lt, ge, le, eq, neq :: RelOp
gt = RelOp ">"
lt = RelOp "<"
ge = RelOp ">="
le = RelOp "<="
eq = RelOp "=="
neq = RelOp "!="

data Type
    = TBasic Basic
    | TIdent Ident
    | TList Type
    | TProduct Type Type
    | TUnion Type Type
    | TFun Type Type
  deriving (Eq, Ord, Show, Read)

data Alternative = MAlternative Pattern Expr
  deriving (Eq, Ord, Show, Read)

data Pattern
    = PIdent Ident
    | PAny
    | PTuple Pattern [Pattern]
    | PList [Pattern]
    | PString String
    | PInt Integer
    | PChar Char
    | PTrue
    | PFalse
    | PEmpty
    | PUnit
    | PListHT Pattern Pattern
    | PUnion Integer Pattern
  deriving (Eq, Ord, Show, Read)

data QIdent = Qual Ident Ident
  deriving (Eq, Ord, Show, Read)

data SStmt = SDecl VDecl | SDef Def
  deriving (Eq, Ord, Show, Read)

data Stream = DStream Ident [Ident] [SStmt] [SStmt] [Def]
  deriving (Eq, Ord, Show, Read)

