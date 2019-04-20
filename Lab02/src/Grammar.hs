module Grammar where
    import Data.List (intercalate)
    
    data Binop = Impl | Or | And deriving (Eq, Ord)
    
    instance Show Binop where
      show Impl = "->"
      show Or   = "|"
      show And  = "&"
    
    data Expr = Binary Binop Expr Expr
              | Not Expr
              | Var String deriving (Eq, Ord)
    
    instance Show Expr where
      show (Binary op a b) = "(" ++ s2 ++ " "  ++ s1 ++ " " ++ s3 ++ ")" 
        where [s1, s2, s3] = [show op, show a, show b]
      show (Not e)         = "(!" ++ show e ++ ")"
      show (Var name)      = name