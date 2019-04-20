module Main where

import System.IO (isEOF)
import Grammar
import Lexer (alexScanTokens)
import Parser (parse)
import Data.List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
    
parseContext :: String -> Int -> [(Expr, Int)] -> [(Expr, Int)]
parseContext "" num exprs = exprs
parseContext (',' : a) num exprs = parseContext (dropWhile (/= ',') a) (num + 1) (expr1 : exprs) where
    expr1 = (parse $! alexScanTokens $! takeWhile (/= ',') a, num)
parseContext a num exprs = parseContext (dropWhile (/= ',') a) (num + 1) (expr1 : exprs) where
    expr1 = (parse $! alexScanTokens $! takeWhile (/= ',') a, num)

getContextLen :: String -> Int
getContextLen s = helper s 0 where
    helper ('|':'-':xs) n = n
    helper (x : xs) n = helper xs (n + 1)
    helper [] n = n

parseExpr :: String -> Expr
parseExpr = parse . alexScanTokens


getExpressions :: [(Expr, Int)] -> Int -> IO [(Expr, Int)]
getExpressions exprs n = 
    do 
        done <- isEOF
        if done 
            then return $! reverse exprs
            else do inp <- getLine
                    getExpressions ((parseExpr inp,  n) : exprs) (n + 1)


proofIsIncorrect :: IO ()
proofIsIncorrect = putStrLn "Proof is incorrect"

data ExprInfo = Axiom Int Int | Hyp Int Int | Mp Int Int Int deriving Show

getIndex :: ExprInfo -> Int
getIndex (Axiom a _) = a
getIndex (Hyp a _) = a
getIndex (Mp a _ _) = a

canBeMPonused :: Expr -> Maybe [(Expr, Int)] -> Map.Map Expr ExprInfo -> (Bool, Int, Int)
canBeMPonused _ Nothing _ = (False, 0, 0)
canBeMPonused e (Just []) good = (False, 0, 0)
canBeMPonused e (Just ((front, ind) : end)) good 
    = if a `Map.member` good 
        then (True, ind, getIndex $! (good Map.! a))
        else canBeMPonused e (Just end) good where
            (Binary Impl a b) = front
        
isImpl :: Expr -> Bool
isImpl (Binary Impl a b) = True
isImpl _ = False       

insertToMap :: Expr -> Expr -> Int -> Map.Map Expr [(Expr, Int)] -> Map.Map Expr [(Expr, Int)]
insertToMap b e num exprsFromRightParts = Map.insertWith (++) b [(e, num)] exprsFromRightParts

-- fakeGetCorrectStatements :: Expr -> Map.Map Expr Int -> Map.Map Expr ExprInfo -> Map.Map Expr [(Expr, Int)] -> Int -> Expr-> IO ((Map.Map Expr ExprInfo), Expr)
-- fakeGetCorrectStatements term hyps good exprsFromRightParts num lastChecked= 

getCorrectStatements :: Expr -> Map.Map Expr Int -> Map.Map Expr ExprInfo -> Map.Map Expr [(Expr, Int)] 
                            -> Int -> Expr -> Int -> IO ((Map.Map Expr ExprInfo), Expr, Int)
getCorrectStatements term hyps good exprsFromRightParts num lastChecked fstTerm = 
    do 
        done <- isEOF
        if done 
            then return (good, lastChecked, fstTerm)
            else do inp <- getLine
                    let e = parseExpr inp
                    let (isAx, axNum) = isAxiom e
                    let (canBeMP, impl, leftImpl) = canBeMPonused e (Map.lookup e exprsFromRightParts) good 
                    if term /= e
                        then if e `Map.member` good 
                            then getCorrectStatements term hyps good exprsFromRightParts (num + 1) e fstTerm 
                            else if isAx 
                                then getCorrectStatements term hyps (Map.insert e (Axiom num axNum) good) 
                                    (let (Binary Impl a b) = e in (insertToMap b e num exprsFromRightParts)) (num + 1) e fstTerm
                                else if e `Map.member` hyps
                                    then if isImpl e
                                        then getCorrectStatements term hyps (Map.insert e (Hyp num (hyps Map.! e)) good) 
                                            (let (Binary Impl a b) = e in (insertToMap b e num exprsFromRightParts)) (num + 1) e fstTerm
                                        else getCorrectStatements term  hyps (Map.insert e (Hyp num (hyps Map.! e)) good) exprsFromRightParts (num + 1) e fstTerm
                                    else if canBeMP 
                                        then if isImpl e
                                            then let (Binary Impl a b) = e in getCorrectStatements term hyps (Map.insert e (Mp num impl leftImpl) good) 
                                                (insertToMap b e num exprsFromRightParts) (num + 1) e fstTerm
                                            else getCorrectStatements term hyps (Map.insert e (Mp num impl leftImpl) good) exprsFromRightParts (num + 1) e fstTerm
                                        else return  (Map.empty, e, 0)
                        else if e `Map.member` good 
                            then getCorrectStatements term hyps good exprsFromRightParts (num + 1) e fstTerm 
                            else if isAx 
                                then getCorrectStatements term hyps (Map.insert e (Axiom num axNum) good) 
                                    (let (Binary Impl a b) = e in (insertToMap b e num exprsFromRightParts)) (num + 1) e num
                                else if e `Map.member` hyps
                                    then if isImpl e
                                        then getCorrectStatements term hyps (Map.insert e (Hyp num (hyps Map.! e)) good) 
                                            (let (Binary Impl a b) = e in (insertToMap b e num exprsFromRightParts)) (num + 1) e num
                                        else getCorrectStatements term  hyps (Map.insert e (Hyp num (hyps Map.! e)) good) exprsFromRightParts (num + 1) e num
                                    else if canBeMP 
                                        then if isImpl e
                                            then let (Binary Impl a b) = e in getCorrectStatements term hyps (Map.insert e (Mp num impl leftImpl) good) 
                                                (insertToMap b e num exprsFromRightParts) (num + 1) e num
                                            else getCorrectStatements term hyps (Map.insert e (Mp num impl leftImpl) good) exprsFromRightParts (num + 1) e num
                                        else return (Map.empty, e, 0) 
                                            

cmprtr :: (Expr, ExprInfo) -> (Expr, ExprInfo) -> Ordering
cmprtr (_, ii1) (_, ii2) 
    = if i1 > i2 
        then LT
        else if i1 == i2 
            then EQ
            else GT where 
                i1 = getIndex ii1
                i2 = getIndex ii2

resolveInfo :: ExprInfo -> Int -> Int -> Map.Map Int Int -> ExprInfo
resolveInfo (Axiom a b) size worked mirrow = Axiom (worked) b 
resolveInfo (Hyp a b) size worked mirrow = Hyp (worked) b 
resolveInfo (Mp a b c) size worked mirrow = Mp (worked) (size + 1 - (mirrow Map.! b)) (size + 1 - (mirrow Map.! c))

resolveDependencies :: Int -> Int -> Map.Map Int Int -> [(Expr, ExprInfo)] -> [(Expr, ExprInfo)] ->[(Expr, ExprInfo)]
resolveDependencies size resSize mirrow [] res = reverse res  
resolveDependencies size resSize mirrow ((e, inf) : left) res = resolveDependencies size (resSize + 1) mirrow left ((e, resolveInfo inf (size) (resSize) mirrow ) : res) 

makeDependency :: [(Expr, ExprInfo)] -> Set.Set Int -> Int -> Map.Map Int Int -> [(Expr, ExprInfo)] -> [(Expr, ExprInfo)]
makeDependency [] set count mirrow res = resolveDependencies (length res) 0 mirrow res []
makeDependency ((e, Mp a b c) : left) set count mirrow res 
    = if ind `Set.member` set
        then makeDependency left (Set.delete ind $! Set.insert c $! Set.insert b set) (count + 1) (Map.insert ind count mirrow) ((e, Mp a b c) : res)
        else makeDependency left set count mirrow res where
            ind = a
makeDependency ((e, inf) : left) set count mirrow res
    = if ind `Set.member` set 
        then makeDependency left (Set.delete ind set) (count + 1) (Map.insert ind count mirrow) ((e, inf) : res)
        else makeDependency left set count mirrow res where
        ind = getIndex inf 

parseInf :: ExprInfo -> String
parseInf (Axiom a b) = "["++ show (a + 1)++". Ax. sch. " ++ show b ++ "] " 
parseInf (Hyp a b) =  "["++ show (a + 1)++". Hypothesis " ++ show b ++ "] "
parseInf (Mp a b c) =  "["++ show (a + 1)++". M.P. " ++ show (b - 1) ++ ", " ++ show (c - 1) ++ "] "

displayRes :: [(Expr, ExprInfo)] -> IO ()
displayRes [] = putStr ""
displayRes ((e, inf) : left) 
    = do 
        putStrLn (parseInf inf ++ show e)
        displayRes left

main :: IO ()
main = do
    input <- getLine
    let term = parse $! alexScanTokens $! term' where term' = drop (getContextLen input + 2) input
    -- let hypotheses = Map.fromList $! ((parseContext $! (take (getContextLen input) input)) $! 1) []
    -- expressions <- getExpressions [] 1 -- numered list of all statements
    -- if (fst $! last $! expressions) /= term
        -- then proofIsIncorrect
        -- else 
    do
        (tmp, lastChecked, fstTerm) <-getCorrectStatements term (Map.fromList $! ((parseContext $! (take (getContextLen input) input)) $! 1) []) Map.empty Map.empty 1 (Var "***") 0
        let res = dropWhile (\ (_, e) -> getIndex e /= fstTerm) $! sortBy cmprtr (Map.toList $! tmp)
        -- putStrLn $ show $  res
        -- putStrLn $ show$ fstTerm
        if (null res || (lastChecked /= term))
            then proofIsIncorrect
            else do
                let (e, inf) = head res
                let ind = getIndex inf
                putStrLn input
                displayRes $! makeDependency res (Set.fromList [ind]) 0 Map.empty []
                                        
isAxiom :: Expr -> (Bool, Int)
isAxiom e = 
    if isAxiom1 e 
        then (True, 1) 
        else if isAxiom2 e 
            then (True, 2) 
            else if isAxiom3 e 
                then (True, 3) 
                else if isAxiom4 e 
                    then (True, 4) 
                    else if isAxiom5 e 
                        then (True, 5) 
                        else if isAxiom6 e
                            then (True, 6) 
                            else if isAxiom7 e 
                                then (True, 7) 
                                else if isAxiom8 e 
                                    then (True, 8) 
                                    else if isAxiom9 e 
                                        then (True, 9) 
                                        else if isAxiom10 e
                                            then (True, 10)
                                            else (False, 0)

isAxiom1 :: Expr -> Bool
isAxiom1 (Binary Impl a (Binary Impl b c))
    | a == c = True
    | otherwise = False
isAxiom1 _ = False

isAxiom2 :: Expr -> Bool
isAxiom2 (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl c (Binary Impl d e)) (Binary Impl f g )))
    | a == c && a == f && b == d && e == g = True
    | otherwise = False
isAxiom2 _ = False

isAxiom3 :: Expr -> Bool
isAxiom3 (Binary Impl a (Binary Impl b (Binary And c d)))
    | a == c && b == d = True
    | otherwise = False
isAxiom3 _ = False

isAxiom4 :: Expr -> Bool
isAxiom4 (Binary Impl (Binary And a b) c)
    | a == c = True
    | otherwise = False
isAxiom4 _ = False

isAxiom5 :: Expr -> Bool
isAxiom5 (Binary Impl (Binary And a b) c)
    | b == c = True
    | otherwise = False
isAxiom5 _ = False


isAxiom6 :: Expr -> Bool
isAxiom6 (Binary Impl a (Binary Or b c))
    | a == b = True
    | otherwise = False
isAxiom6 _ = False

isAxiom7 :: Expr -> Bool
isAxiom7 (Binary Impl a (Binary Or b c))
    | a == c = True
    | otherwise = False
isAxiom7 _ = False


isAxiom8 :: Expr -> Bool
isAxiom8 (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl c d) (Binary Impl (Binary Or e f) g)))
    | a == e && b == d && b == g && c == f = True
    | otherwise = False
isAxiom8 _ = False

isAxiom9 :: Expr -> Bool
isAxiom9 (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl c d) e))
    | a == c && Not b == d && Not a == e = True
    | otherwise = False
isAxiom9 _ = False

isAxiom10 :: Expr -> Bool
isAxiom10 (Binary Impl a b)
    | a == Not (Not b) = True
    | otherwise = False
isAxiom10 _ = False


