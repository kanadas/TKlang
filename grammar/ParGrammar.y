-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module ParGrammar where
import AbsGrammar
import LexGrammar
import ErrM

}

%name pProgram Program
-- no lexer declaration
%monad { Err } { thenM } { returnM }
%tokentype {Token}
%token
  '!' { PT _ (TS _ 1) }
  '&' { PT _ (TS _ 2) }
  '(' { PT _ (TS _ 3) }
  '()' { PT _ (TS _ 4) }
  '(\\' { PT _ (TS _ 5) }
  ')' { PT _ (TS _ 6) }
  '*' { PT _ (TS _ 7) }
  '+' { PT _ (TS _ 8) }
  '++' { PT _ (TS _ 9) }
  ',' { PT _ (TS _ 10) }
  '-' { PT _ (TS _ 11) }
  '->' { PT _ (TS _ 12) }
  '.' { PT _ (TS _ 13) }
  '/' { PT _ (TS _ 14) }
  ':' { PT _ (TS _ 15) }
  '::' { PT _ (TS _ 16) }
  ';' { PT _ (TS _ 17) }
  '=' { PT _ (TS _ 18) }
  '@' { PT _ (TS _ 19) }
  '[' { PT _ (TS _ 20) }
  '[]' { PT _ (TS _ 21) }
  ']' { PT _ (TS _ 22) }
  '_' { PT _ (TS _ 23) }
  'else' { PT _ (TS _ 24) }
  'false' { PT _ (TS _ 25) }
  'if' { PT _ (TS _ 26) }
  'in' { PT _ (TS _ 27) }
  'initial' { PT _ (TS _ 28) }
  'input' { PT _ (TS _ 29) }
  'is' { PT _ (TS _ 30) }
  'let' { PT _ (TS _ 31) }
  'match' { PT _ (TS _ 32) }
  'output' { PT _ (TS _ 33) }
  'state' { PT _ (TS _ 34) }
  'stream' { PT _ (TS _ 35) }
  'then' { PT _ (TS _ 36) }
  'true' { PT _ (TS _ 37) }
  'type' { PT _ (TS _ 38) }
  'with' { PT _ (TS _ 39) }
  '{' { PT _ (TS _ 40) }
  '|' { PT _ (TS _ 41) }
  '}' { PT _ (TS _ 42) }

L_ident  { PT _ (TV $$) }
L_integ  { PT _ (TI $$) }
L_charac { PT _ (TC $$) }
L_quoted { PT _ (TL $$) }
L_RelOp { PT _ (T_RelOp $$) }
L_Basic { PT _ (T_Basic $$) }


%%

Ident   :: { Ident }   : L_ident  { Ident $1 }
Integer :: { Integer } : L_integ  { (read ( $1)) :: Integer }
Char    :: { Char }    : L_charac { (read ( $1)) :: Char }
String  :: { String }  : L_quoted {  $1 }
RelOp    :: { RelOp} : L_RelOp { RelOp ($1)}
Basic    :: { Basic} : L_Basic { Basic ($1)}

Program :: { Program }
Program : ListTop { AbsGrammar.Prog $1 }
ListTop :: { [Top] }
ListTop : Top { (:[]) $1 } | Top ';' ListTop { (:) $1 $3 }
Top :: { Top }
Top : VDecl { AbsGrammar.TopVDecl $1 }
    | TDecl { AbsGrammar.TopTDecl $1 }
    | Def { AbsGrammar.TopDef $1 }
    | Stream { AbsGrammar.TopStream $1 }
VDecl :: { VDecl }
VDecl : Ident '::' Type { AbsGrammar.DVDecl $1 $3 }
TDecl :: { TDecl }
TDecl : 'type' Ident 'is' Type { AbsGrammar.DTDecl $2 $4 }
Def :: { Def }
Def : Ident ListIdent '=' Expr { AbsGrammar.DDef $1 $2 $4 }
Expr11 :: { Expr }
Expr11 : Integer { AbsGrammar.EInt $1 }
       | Char { AbsGrammar.EChar $1 }
       | String { AbsGrammar.EString $1 }
       | Ident { AbsGrammar.EIdent $1 }
       | QIdent { AbsGrammar.EQual $1 }
       | 'true' { AbsGrammar.ETrue }
       | 'false' { AbsGrammar.EFalse }
       | '()' { AbsGrammar.EVoid }
       | '[]' { AbsGrammar.EEmpty }
       | '!' Expr11 { AbsGrammar.ENot $2 }
       | '(' Expr ',' ListExpr ')' { AbsGrammar.ETuple $2 $4 }
       | '[' ListExpr ']' { AbsGrammar.EList $2 }
       | '(\\' ListIdent '->' Expr ')' { AbsGrammar.ELambda $2 $4 }
       | '(' Expr ')' { $2 }
Expr10 :: { Expr }
Expr10 : Expr10 Expr11 { AbsGrammar.EApp $1 $2 } | Expr11 { $1 }
Expr9 :: { Expr }
Expr9 : Expr9 '*' Expr10 { AbsGrammar.EMul $1 $3 }
      | Expr9 '/' Expr10 { AbsGrammar.EDiv $1 $3 }
      | Expr10 { $1 }
Expr8 :: { Expr }
Expr8 : Expr8 '+' Expr9 { AbsGrammar.EAdd $1 $3 }
      | Expr8 '-' Expr9 { AbsGrammar.ESub $1 $3 }
      | Expr8 '++' Expr9 { AbsGrammar.EConcat $1 $3 }
      | Expr9 { $1 }
Expr7 :: { Expr }
Expr7 : '-' Expr7 { AbsGrammar.ENeg $2 } | Expr8 { $1 }
Expr6 :: { Expr }
Expr6 : Expr6 RelOp Expr7 { AbsGrammar.ERel $1 $2 $3 }
      | Expr7 { $1 }
Expr5 :: { Expr }
Expr5 : Expr5 '&' Expr6 { AbsGrammar.EAnd $1 $3 } | Expr6 { $1 }
Expr4 :: { Expr }
Expr4 : Expr4 '|' Expr5 { AbsGrammar.EOr $1 $3 } | Expr5 { $1 }
Expr3 :: { Expr }
Expr3 : Expr3 ':' Expr4 { AbsGrammar.EAppend $1 $3 } | Expr4 { $1 }
Expr2 :: { Expr }
Expr2 : Integer '@' Expr3 { AbsGrammar.EUnion $1 $3 }
      | Expr3 { $1 }
Expr1 :: { Expr }
Expr1 : 'if' Expr 'then' Expr 'else' Expr1 { AbsGrammar.EIf $2 $4 $6 }
      | 'let' Ident '=' Expr 'in' Expr1 { AbsGrammar.ELet $2 $4 $6 }
      | 'match' Expr 'with' '{' ListAlternative '}' { AbsGrammar.EMatch $2 $5 }
      | Expr2 { $1 }
Expr :: { Expr }
Expr : Expr1 '::' Type { AbsGrammar.EType $1 $3 } | Expr1 { $1 }
ListExpr :: { [Expr] }
ListExpr : Expr { (:[]) $1 } | Expr ',' ListExpr { (:) $1 $3 }
ListIdent :: { [Ident] }
ListIdent : {- empty -} { [] } | Ident ListIdent { (:) $1 $2 }
Type3 :: { Type }
Type3 : Basic { AbsGrammar.TBasic $1 }
      | Ident { AbsGrammar.TIdent $1 }
      | '[' Type ']' { AbsGrammar.TList $2 }
      | '(' Type ')' { $2 }
Type2 :: { Type }
Type2 : Type2 '*' Type3 { AbsGrammar.TProduct $1 $3 }
      | Type3 { $1 }
Type1 :: { Type }
Type1 : Type1 '+' Type2 { AbsGrammar.TUnion $1 $3 } | Type2 { $1 }
Type :: { Type }
Type : Type1 '->' Type { AbsGrammar.TFun $1 $3 } | Type1 { $1 }
Alternative :: { Alternative }
Alternative : Pattern '->' Expr { AbsGrammar.MAlternative $1 $3 }
ListAlternative :: { [Alternative] }
ListAlternative : Alternative { (:[]) $1 }
                | Alternative ';' ListAlternative { (:) $1 $3 }
Pattern2 :: { Pattern }
Pattern2 : Ident { AbsGrammar.PIdent $1 }
         | '_' { AbsGrammar.PAny }
         | '(' Pattern ',' ListPattern ')' { AbsGrammar.PTuple $2 $4 }
         | '[' ListPattern ']' { AbsGrammar.PList $2 }
         | String { AbsGrammar.PString $1 }
         | Integer { AbsGrammar.PInt $1 }
         | Char { AbsGrammar.PChar $1 }
         | 'true' { AbsGrammar.PTrue }
         | 'false' { AbsGrammar.PFalse }
         | '[]' { AbsGrammar.PEmpty }
         | '()' { AbsGrammar.PVoid }
         | '(' Pattern ')' { $2 }
Pattern1 :: { Pattern }
Pattern1 : Pattern1 ':' Pattern2 { AbsGrammar.PListHT $1 $3 }
         | Pattern2 { $1 }
Pattern :: { Pattern }
Pattern : Integer '@' Pattern { AbsGrammar.PUnion $1 $3 }
        | Pattern1 { $1 }
ListPattern :: { [Pattern] }
ListPattern : Pattern { (:[]) $1 }
            | Pattern ',' ListPattern { (:) $1 $3 }
QIdent :: { QIdent }
QIdent : Ident '.' Ident { AbsGrammar.Qual $1 $3 }
SStmt :: { SStmt }
SStmt : VDecl { AbsGrammar.SDecl $1 } | Def { AbsGrammar.SDef $1 }
Stream :: { Stream }
Stream : 'stream' Ident 'input' ListIdent 'state' ListSStmt 'output' ListSStmt 'initial' ListDef { AbsGrammar.DStream $2 $4 $6 $8 $10 }
ListSStmt :: { [SStmt] }
ListSStmt : {- empty -} { [] }
          | SStmt { (:[]) $1 }
          | SStmt ';' ListSStmt { (:) $1 $3 }
ListDef :: { [Def] }
ListDef : {- empty -} { [] }
        | Def { (:[]) $1 }
        | Def ',' ListDef { (:) $1 $3 }
{

returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    t:_ -> " before `" ++ id(prToken t) ++ "'"

myLexer = tokens
}

