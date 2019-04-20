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

isImpl :: Expr -> Bool
isImpl (Binary Impl a b) = True
isImpl _                 = False

showProof :: [Expr] -> IO ()
showProof [] = putStr ""
showProof (a : part) = do
    putStrLn $ show $ a
    showProof part


appendAllrToAll :: [Expr] -> Map.Map Expr [Expr] -> Map.Map Expr [Expr]
appendAllrToAll (e : part) m =
    case e of
        (Not(Not(Binary Impl a b))) -> appendAllrToAll part (Map.insertWith (++) b [Binary Impl a b] m)  
        _                 -> appendAllrToAll part m
appendAllrToAll [] m = m

sol :: Map.Map Expr Int -> Map.Map Expr [Expr] -> Set.Set Expr -> IO ()
sol hyp rToAll proofed = do
    done <- isEOF
    if not done
        then do
            -- putStrLn "-------------------------------------------------------------------------------------------------------"
            -- putStrLn $ show $ rToAll
            -- putStrLn $ show $ proofed
            inp <- getLine
            let line = parseExpr inp
            let lineProof = genProof line hyp rToAll proofed
            -- let newProofed = Set.union proofed (Set.fromList lineProof)
            let newMap = hh where
                hh = case line of
                    (Binary Impl a b) -> Map.insertWith (++) b [line] rToAll
                    _ -> rToAll

            showProof lineProof
            -- putStrLn $ show $ newMap
            sol hyp newMap (Set.insert line proofed)
        else return ()

    -- putStrLn ""

-- A -> A -> A
-- A
-- A
-- A

main :: IO ()
main = do
    inpu <- getLine
    let input = filter (\a -> a /= ' ') inpu
    let term = parseExpr $! term' where term' = drop (getContextLen input + 2) input
    let hyp = Map.fromList $! ((parseContext $! (take (getContextLen input) input)) $! 1) []
    -- showProof (cpProof (Var "A") (Var "B"))
    -- showProof (genDed [(Var "A"), (Var "A"), (Var "A")] [(Var "A")])
    -- showProof (genDed [(Var "A"), (Var "A"), (Var "A")] [(Var "A")])
    -- showProof (genDed'' (Set.fromList [(Var "A")]) (Var "B") [(Var "A")] (Map.empty) (Set.empty) [])
    -- putStrLn ""
    -- showProof (proofAx10 (Binary Impl (Not(Not (Var "A"))) (Var "A")))
    -- showProof (genDed [(Var "A"), (Var "B"), (Var "C")] [(Var "A")])
    let sum = res where
        term' = drop (getContextLen input + 2) input
        h = take (getContextLen input) input
        res = h ++"|- !!(" ++  term' ++ ")"
    putStrLn sum
    -- putStrLn "------------------------"
    sol (hyp) (Map.fromList []) (Set.fromList [])
    -- putStrLn $ show $ hyp

    -- do
    --     (tmp, lastChecked, fstTerm) <- getCorrectStatements term (Map.fromList $! ((parseContext $! (take (getContextLen input) input)) $! 1) []) Map.empty Map.empty 1 (Var "***") 0
    --     let res = dropWhile (\ (_, e) -> getIndex e /= fstTerm) $! sortBy cmprtr (Map.toList $! tmp)
    --     if (null res || (lastChecked /= term))
    --         then proofIsIncorrect
    --         else do
    --             let (e, inf) = head res
    --             let ind = getIndex inf
    --             putStrLn input
    --             displayRes $! makeDependency res (Set.fromList [ind]) 0 Map.empty []
