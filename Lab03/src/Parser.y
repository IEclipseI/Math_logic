{
module Parser where

import Grammar
import Lexer
}

%name      parse
%tokentype { Token }
%error     { parseError }

%token VAR          { VarL $$ }
%token IMPL         { ImplicationL }
%token OR          { OrL }
%token AND          { AndL }
%token NOT          { NotL }
%token LEFTB          { LeftBracketL }
%token RIGHTB          { RightBracketL }

%%

Expr
  : Disj               { $1 }
  | Disj IMPL Expr     { Binary Impl $1 $3 }

Disj
  : Conj               { $1 }
  | Disj OR Conj       { Binary Or $1 $3 }

Conj
  : Neg               { $1 }
  | Conj AND Neg      { Binary And $1 $3 }

Neg
  : NOT Neg            { Not $2 }
  | Term               { $1 }
  | LEFTB Expr RIGHTB  { $2 }

Term
  : VAR                { Var $1 }

{
parseError = fail "Parse error"
}