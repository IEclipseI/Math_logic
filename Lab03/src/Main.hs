module Main where

import           Data.List
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set
import           Grammar
import           Lexer           (alexScanTokens)
import           Parser          (parse)
import           ProofsGenerator
import           System.IO       (isEOF)

parseContext :: String -> Int -> [(Expr, Int)] -> [(Expr, Int)]
parseContext "" num exprs = exprs
parseContext (',' : a) num exprs = parseContext (dropWhile (/= ',') a) (num + 1) (expr1 : exprs) where
    expr1 = (parse $! alexScanTokens $! takeWhile (/= ',') a, num)
parseContext a num exprs = parseContext (dropWhile (/= ',') a) (num + 1) (expr1 : exprs) where
    expr1 = (parse $! alexScanTokens $! takeWhile (/= ',') a, num)

getContextLen :: String -> Int
getContextLen s = helper (filter (\a -> (a /= ' '))s) 0  where
    helper ('|':'-':xs) n = n
    helper (x : xs) n     = helper xs (n + 1)
    helper [] n           = n

parseExpr :: String -> Expr
parseExpr = parse . alexScanTokens

showProof :: [Expr] -> IO ()
showProof [] = putStr ""
showProof (a : part) = do
    putStrLn $ show $ a
    showProof part

sol :: Map.Map Expr Int -> Map.Map Expr [Expr] -> Set.Set Expr -> IO ()
sol hyp rToAll proofed = do
    done <- isEOF
    if not done
        then do
            inp <- getLine
            let line = parseExpr inp
            let lineProof = genProof line hyp rToAll proofed
            let newMap = hh where
                hh = case line of
                    (Binary Impl a b) -> Map.insertWith (++) b [line] rToAll
                    _ -> rToAll

            showProof lineProof
            sol hyp newMap (Set.insert line proofed)
        else return ()

main :: IO ()
main = do
    inpu <- getLine
    let input = filter (\a -> a /= ' ') inpu
    let term = parseExpr $! term' where term' = drop (getContextLen input + 2) input
    let hyp = Map.fromList $! ((parseContext $! (take (getContextLen input) input)) $! 1) []
    let sum = res where
        term' = drop (getContextLen input + 2) input
        h = take (getContextLen input) input
        res = h ++"|- !!(" ++  term' ++ ")"
    putStrLn sum
    sol (hyp) (Map.fromList []) (Set.fromList [])
