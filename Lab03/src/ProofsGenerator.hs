module ProofsGenerator where

import           Data.List
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set
import           Grammar
import Debug.Trace
-- import           Main

showProof' :: [Expr] -> IO ()
showProof' (a : part) = do
    putStr "Debug: "
    putStrLn $ show $ a
    showProof' part
showProof' [] = putStr ""

genProof :: Expr -> Map.Map Expr Int -> Map.Map Expr [Expr] -> Set.Set Expr -> [Expr]
genProof e hyps rToAll proofed = proof
    where
        isAx1_9 = case isAxiom1_9 e of
            Just _  -> True
            Nothing -> False
        isHypOrAx1_9 = isAx1_9 || (Map.member e hyps)
        proof = case isHypOrAx1_9 of
            True  -> proofAx1_9OrHyp e
            False -> case e of
                (Binary Impl (Not (Not a)) b) | a == b -> proofAx10 e
                _ -> proofMp e hyps rToAll proofed



proofMp :: Expr -> Map.Map Expr Int -> Map.Map Expr [Expr] -> Set.Set Expr -> [Expr]
proofMp e hyps rToAll proofed = proof where
    (a, (Binary Impl f b)) = findParts e ((Map.!) rToAll e) proofed
    na = Not a              -- !A
    nna = Not na            -- !!A
    ab = Binary Impl a b    -- A -> B
    nab = Not ab            -- !(A -> B)
    nnab= Not nab           -- !!(A -> B)
    nb = Not b              -- !B
    nnb = Not nb            -- !!B
    l1 =  ax2 nb nna nab     -- (!B -> !!A) -> (!B -> !!A -> !(A -> B)) -> (!B -> !(A -> B))
    l2 = ax1 nna nb         -- !!A -> !B -> !!A
    l3= mp l2               -- !B -> !!A
    l4 = mp l1              -- (!B -> !!A -> !(A -> B)) -> (!B -> !(A -> B))
    ----------------
    l5 = ax9 a b            -- (A -> B)-> (A -> !B) -> !A
    l6 = ab                 -- (A -> B)
    l7 = nb                 -- !B
    l8 = ax1 nb a           -- !B -> A -> !B
    l9 = mp l8              -- A -> !B
    l10 = mp l5             -- (A -> !B) -> !A
    l11 = mp l10            -- !A
    hyp1 = nb               -- !B
    hyp2 = ab               -- A -> B
    hhh = [hyp1, hyp2]
    ppp = l5 : l6 : l7 : l8 : l9 : l10 : l11 : []
    ---------
    l12 = genOneDed hhh ppp -- (A -> B) -> !A
    (Binary Impl l r) = last l12 --
    l13 = cpProof l r       -- !!A -> !(A -> B)
    l14 = mp $ last $  l13  -- !(A -> B)
    l15 = genDed [hyp1]  (l12 ++ l13 ++ [l14]) -- !B -> !(A -> B) ___ !B -> !!A -> !(A -> B)
    l16 = mp l4             -- (!B -> !(A -> B))
    l17 = cpProof ll rr where
        (Binary Impl ll rr) = l16  -- (!B -> !(A -> B)) -> (!!(A -> B) -> !!B)
    l18 = mp (last l17)     -- (!!(A -> B) -> !!B)
    l19 = mp l18            -- !!B
    proof = [l1 , l2 , l3 , l4] ++ l15 ++ [l16] ++ l17 ++ [l18, l19]

ax1 :: Expr -> Expr -> Expr
ax1 a b = Binary Impl a (Binary Impl b a)

ax2 :: Expr -> Expr -> Expr -> Expr
ax2 a b c = (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a (Binary Impl b c)) (Binary Impl a c)))

ax9 :: Expr -> Expr -> Expr
ax9 a b = Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl a (Not b)) (Not a))

mp :: Expr -> Expr
mp (Binary Impl a b) = b

-- fillData :: [Expr] -> Map.Map Expr [Expr] -> Map.Map Expr [Expr]
-- fillData [] p = p
-- fillData (e : part) m = case e of
--     (Binary Impl a b) -> fillData part (Map.insertWith (++) b m)
--     _ -> fillData part m

lemAtoA :: Expr -> [Expr]
lemAtoA a = proof where
    l1 = ax1 a a
    aToa = Binary Impl a a
    l2 = ax2 a aToa a
    l3 = mp l2
    l4 = ax1 a aToa
    l5 = mp l3
    proof = l1 : l2 : l3 : l4 : l5 : []

genOneDed :: [Expr] -> [Expr] -> [Expr]
genOneDed hyp proof = genDed'' (Set.fromList $ tail $ reverse $ hyp) (last hyp) proof (Map.empty) (Set.empty) []

genDed :: [Expr] -> [Expr] -> [Expr]
genDed hyp proof = genDed' (reverse hyp) proof

genDed' :: [Expr] -> [Expr] -> [Expr]
genDed' [] newProof = newProof
genDed' (h : hyp) newProof = genDed' hyp (genDed'' (Set.fromList hyp) h newProof (Map.empty) (Set.empty) [])

genDed'' :: Set.Set Expr -> Expr -> [Expr] -> Map.Map Expr [Expr] -> Set.Set Expr -> [Expr] -> [Expr]
genDed'' _ _ [] _ _ newProof = newProof
genDed'' hyps h (e : rest) rToAll was newProof = genDed'' hyps h rest newRToAll newWas t where
    prOfe = case e == h of
        True -> lemAtoA e
        False -> case isAx1_10 e of
            True -> axProof h e
            False -> case Set.member e hyps of
                True -> axProof h e
                False -> mpProof where
                    Just ff = (Map.lookup e rToAll)
                    (a, ab) = findParts e ff was
                    l1 = ax2 h a e
                    l2 = mp l1
                    l3 = mp l2
                    mpProof = l1 : l2 : l3 : []
    newWas = Set.insert e was
    newRToAll = case e of
        (Binary Impl a b) -> Map.insertWith (++) b [e] rToAll
        _                 -> rToAll
    t = newProof ++ prOfe


-- cra :: Expr -> Set.Set Expr -> IO String
-- cra e s = do
--     putStrLn ("00000 " ++ (show e) ++ " 00000") 
--     return $show$Set.member e s 


-- findParts :: Expr -> [Expr] -> Set.Set Expr -> (Expr, Expr)
-- findParts e ((Binary Impl a b) : rest) s = let r= extracr $ cra e s in case r of
--     "True"  -> (a, Binary Impl a b)
--     False -> findParts e rest s 


findParts :: Expr -> [Expr] -> Set.Set Expr -> (Expr, Expr)
-- findParts e [] s = (f, f) where f = Binary Impl e (Binary Impl e (Var "EBAT TI LOX"))
findParts e ((Binary Impl a b) : rest) s = case Set.member a s of
    True  -> (a, Binary Impl a b)
    False -> findParts e rest s


axProof :: Expr -> Expr -> [Expr]
axProof h e = proof where
    l1 = e
    l2 = ax1 e h
    l3 = mp l2
    proof = (l1 : l2 : l3 : [])


proofAx10 :: Expr -> [Expr]
proofAx10 (Binary Impl nna a) = proof where
    e = Binary Impl nna a
    ne = Not e
    na = Not a
    l1 = ax9 ne na
    l2 = Binary Impl a e
    l3 = cpProof a e
    l3' = cp a e
    l4 = mp l3'
    l5 = Binary Impl na (Binary Impl nna a)
    l6 = cpProof na e
    l6' = cp na e
    l7 = mp l6'
    l8 = mp l1
    l9 = mp l8
    -- cratch = Binary Impl ((()))
    proof = (l1:l2:l3) ++ (l4:l5:l6) ++ (l7:l8:l9:[])
    -- proof = [l5]

cpProof :: Expr -> Expr -> [Expr]
cpProof a b = proof where
    l1 = ax9 a b            -- (A -> B) -> (A -> !B) -> !A
    l2 = Binary Impl a b    -- (A->B)
    l3 = mp l1              -- (A -> !B) -> !A
    l4 = ax1 (Not b) a      -- !B -> A -> !B
    l5 = Not b              -- !B
    l6 = mp l4              -- A -> !B
    l7 = mp l3              -- !A
    hyp1 = Binary Impl a b  -- A -> B
    hyp2 = Not b            -- !B
    pr = l1: l2 : l3 : l4 : l5 : l6 : l7 :[]
    proof = genDed [hyp1, hyp2] pr

cp :: Expr -> Expr -> Expr
cp a b = Binary Impl (Binary Impl a b) (Binary Impl (Not b) (Not a))

proofAx1_9OrHyp :: Expr -> [Expr]
proofAx1_9OrHyp a = proof where
    na = (Not a)
    l1 = a
    l2 = ax1 a na
    l3 = mp l2
    l4 = ax1 na na
    l5 = ax2 na (Binary Impl na na) na
    l6 = mp l5
    l7 = ax1 na (Binary Impl na na)
    l8 = mp l6
    l9 = ax9 na a
    l10 = mp l9
    l11 = mp l10
    proof =  l1:l2:l3:l4:l5:l6:l7:l8:l9:l10:l11:[]

isAxiom1_9 :: Expr -> Maybe Int
isAxiom1_9 (Binary Impl a (Binary Impl b c))
    | a == c = Just 1
isAxiom1_9 (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl c (Binary Impl d e)) (Binary Impl f g )))
    | a == c && a == f && b == d && e == g = Just 2
isAxiom1_9 (Binary Impl a (Binary Impl b (Binary And c d)))
    | a == c && b == d = Just 3
isAxiom1_9 (Binary Impl (Binary And a b) c)
    | a == c = Just 4
isAxiom1_9 (Binary Impl (Binary And a b) c)
    | b == c = Just 5
isAxiom1_9 (Binary Impl a (Binary Or b c))
    | a == b = Just 6
isAxiom1_9 (Binary Impl a (Binary Or b c))
    | a == c = Just 7
isAxiom1_9 (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl c d) (Binary Impl (Binary Or e f) g)))
    | a == e && b == d && b == g && c == f = Just 8
isAxiom1_9 (Binary Impl (Binary Impl a b) (Binary Impl (Binary Impl c d) e))
    | a == c && Not b == d && Not a == e = Just 9
isAxiom1_9 _ = Nothing

isAx1_10 :: Expr -> Bool
isAx1_10 e = res where
    p = case isAxiom1_9 e of
        Just _  -> True
        Nothing -> False
    l = case e of
        (Binary Impl a (Binary Impl b c)) | (Not a) == b -> True
                                          | otherwise -> False
        _ -> False
    res = l || p
