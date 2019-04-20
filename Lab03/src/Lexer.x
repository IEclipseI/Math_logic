{
module Lexer where
}

%wrapper "basic"

$digit = 0-9
$alpha = [A-Z]
$tilda = [']

tokens :-

  $white+                    ;
  \(                         { \_ -> LeftBracketL }
  \)                         { \_ -> RightBracketL }
  \|                         { \_ -> OrL }
  &                          { \_ -> AndL }
  "->"                       { \_ -> ImplicationL }
  !                          { \_ -> NotL }
  $alpha [$alpha $digit $tilda]*    { \s -> VarL s }

{

data Token = AndL
           | OrL
           | ImplicationL
           | NotL
           | LeftBracketL
           | RightBracketL
           | VarL String
           deriving (Show, Eq, Ord)

}