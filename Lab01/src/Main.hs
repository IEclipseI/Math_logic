module Main where
import Grammar (Expr (..))
import Lexer (alexScanTokens)
import Parser (parse)

main :: IO ()
main = do
  input <- getLine
  putStrLn $ show $ parse $ alexScanTokens $ input