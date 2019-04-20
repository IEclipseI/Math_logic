{
module Parser where

import Grammar
import Lexer
}

%name      parse
%tokentype { Token }
%error     { parseError }

%token VAR          { VarL $$ }
%token "->"         { ImplicationL }
%token '|'          { OrL }
%token '&'          { AndL }
%token '!'          { NotL }
%token '('          { LeftBracketL }
%token ')'          { RightBracketL }

%%

Expr
  : Disj                { $1 }
  | Disj "->" Expr      { Binary Impl $1 $3 }

Disj
  : Conj                { $1 }
  | Disj '|' Conj       { Binary Or $1 $3 }

Conj
  : Neg                 { $1 }
  | Conj '&' Neg        { Binary And $1 $3 }

Neg
  : '!' Neg             { Not $2 }
  | Term                { $1 }
  | '(' Expr ')'        { $2 }

Term
  : VAR                 { Var $1 }

{
parseError = fail "Parse error"
}