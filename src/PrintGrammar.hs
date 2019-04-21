{-# LANGUAGE FlexibleInstances, OverlappingInstances #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-- | Pretty-printer for PrintGrammar.
--   Generated by the BNF converter.

module PrintGrammar where

import AbsGrammar
import Data.Char

-- | The top-level printing method.

printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : ts@(p:_) | closingOrPunctuation p -> showString t . rend i ts
    t        :ts -> space t . rend i ts
    _            -> id
  new i   = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t = showString t . (\s -> if null s then "" else ' ':s)

  closingOrPunctuation :: String -> Bool
  closingOrPunctuation [c] = c `elem` closerOrPunct
  closingOrPunctuation _   = False

  closerOrPunct :: String
  closerOrPunct = ")],;"

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- | The printer class does the job.

class Print a where
  prt :: Int -> a -> Doc
  prtList :: Int -> [a] -> Doc
  prtList i = concatD . map (prt i)

instance Print a => Print [a] where
  prt = prtList

instance Print Char where
  prt _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList _ s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q s = case s of
  _ | s == q -> showChar '\\' . showChar s
  '\\'-> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  _ -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print Ident where
  prt _ (Ident i) = doc (showString i)
  prtList _ [] = concatD []
  prtList _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print RelOp where
  prt _ (RelOp i) = doc (showString i)

instance Print Basic where
  prt _ (Basic i) = doc (showString i)

instance Print Expr where
  prt i e = case e of
    EInt n -> prPrec i 11 (concatD [prt 0 n])
    EChar c -> prPrec i 11 (concatD [prt 0 c])
    EString str -> prPrec i 11 (concatD [prt 0 str])
    EIdent id -> prPrec i 11 (concatD [prt 0 id])
    ETrue -> prPrec i 11 (concatD [doc (showString "true")])
    EFalse -> prPrec i 11 (concatD [doc (showString "false")])
    EVoid -> prPrec i 11 (concatD [doc (showString "()")])
    EEmpty -> prPrec i 11 (concatD [doc (showString "[]")])
    ENot expr -> prPrec i 11 (concatD [doc (showString "!"), prt 11 expr])
    ETuple expr exprs -> prPrec i 11 (concatD [doc (showString "("), prt 0 expr, doc (showString ","), prt 0 exprs, doc (showString ")")])
    EList exprs -> prPrec i 11 (concatD [doc (showString "["), prt 0 exprs, doc (showString "]")])
    ELambda ids expr -> prPrec i 11 (concatD [doc (showString "(\\"), prt 0 ids, doc (showString "->"), prt 0 expr, doc (showString ")")])
    EApp expr1 expr2 -> prPrec i 10 (concatD [prt 10 expr1, prt 11 expr2])
    EMul expr1 expr2 -> prPrec i 9 (concatD [prt 9 expr1, doc (showString "*"), prt 10 expr2])
    EDiv expr1 expr2 -> prPrec i 9 (concatD [prt 9 expr1, doc (showString "/"), prt 10 expr2])
    EAdd expr1 expr2 -> prPrec i 8 (concatD [prt 8 expr1, doc (showString "+"), prt 9 expr2])
    ESub expr1 expr2 -> prPrec i 8 (concatD [prt 8 expr1, doc (showString "-"), prt 9 expr2])
    EConcat expr1 expr2 -> prPrec i 8 (concatD [prt 8 expr1, doc (showString "++"), prt 9 expr2])
    ENeg expr -> prPrec i 7 (concatD [doc (showString "-"), prt 7 expr])
    ERel expr1 relop expr2 -> prPrec i 6 (concatD [prt 6 expr1, prt 0 relop, prt 7 expr2])
    EAnd expr1 expr2 -> prPrec i 5 (concatD [prt 5 expr1, doc (showString "&"), prt 6 expr2])
    EOr expr1 expr2 -> prPrec i 4 (concatD [prt 4 expr1, doc (showString "|"), prt 5 expr2])
    EAppend expr1 expr2 -> prPrec i 3 (concatD [prt 3 expr1, doc (showString ":"), prt 4 expr2])
    EUnion expr1 expr2 -> prPrec i 2 (concatD [prt 2 expr1, doc (showString "@"), prt 3 expr2])
    EIf expr1 expr2 expr3 -> prPrec i 1 (concatD [doc (showString "if"), prt 0 expr1, doc (showString "then"), prt 0 expr2, doc (showString "else"), prt 1 expr3])
    ELet id expr1 expr2 -> prPrec i 1 (concatD [doc (showString "let"), prt 0 id, doc (showString "="), prt 0 expr1, doc (showString "in"), prt 1 expr2])
    EType expr type_ -> prPrec i 0 (concatD [prt 1 expr, doc (showString "::"), prt 0 type_])
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print [Expr] where
  prt = prtList

instance Print [Ident] where
  prt = prtList

instance Print Type where
  prt i e = case e of
    TBasic basic -> prPrec i 3 (concatD [prt 0 basic])
    TIdent id -> prPrec i 3 (concatD [prt 0 id])
    TProduct type_1 type_2 -> prPrec i 2 (concatD [prt 2 type_1, doc (showString "*"), prt 3 type_2])
    TUnion type_1 type_2 -> prPrec i 1 (concatD [prt 1 type_1, doc (showString "+"), prt 2 type_2])
    TFun type_1 type_2 -> prPrec i 0 (concatD [prt 1 type_1, doc (showString "->"), prt 0 type_2])
    TList type_ -> prPrec i 0 (concatD [doc (showString "["), prt 0 type_, doc (showString "]")])
