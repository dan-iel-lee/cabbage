{-# OPTIONS_GHC -W #-}

module Types () where


data Type =
    Univ
  | CustType String
  | Func Type Type
  | Dep Term
  deriving (Eq, Show)

data Term = 
    Var String Type
  | Const String Type
  | Abs String String Term Type
  | App Term Term
  | TypeTerm Type
  deriving (Eq, Show)


strEq :: String -> String -> Bool
strEq [] [] = True
strEq (x:xs) (y:ys) = x == y && strEq xs ys
strEq _ _ = False

natural :: Type 
natural = CustType "Nat"

zero :: Term 
zero = Const "zero" natural

successor :: Term 
successor = Const "succ" (Func natural natural)

plus1 :: Term 
plus1 = Abs "plus" "n" (App successor (App successor (Var "n" natural))) (Func natural natural)


-- Evaluation


subs :: Term -> String -> Term -> Term 
subs (Var x t) s tt = case strEq x s of
  True -> tt 
  False -> Var x t
subs (App f x) s tt = App (subs f s tt) (subs x s tt)
subs (Abs name var x t) s tt = case strEq var s of
  True -> (Abs name var x t)
  False -> Abs name var (subs x s tt) t
subs val _ _ = val

subsType :: Type -> String -> Term -> Type 
subsType (Dep term) s tt = Dep (subs term s tt)
subsType t _ _ = t


step :: Term -> Term
step (App (Abs _ var x _) y) = subs x var (step y)
step other = other

{-|
stepType :: Type -> Type
stepType (Dep term) = Dep (step term)
-}

checktype :: Term -> (Maybe Type)
checktype (Var _ ty) = Just ty
checktype (Const _ ty) = Just ty 
checktype (Abs _ _ _ ty) = Just ty -- TODO: type check functions
checktype (App t1 t2) = case (checktype t1, checktype t2) of 
  (Just (Func ty1 ty2), Just ty3) -> if ty1 == ty3 then Just ty2 else Nothing
  _ -> Nothing
checktype (TypeTerm Univ) = Nothing 
checktype (TypeTerm _) = Just Univ


-- Playing with dependent types
boolean = CustType "Bool"
true = Const "True" boolean
false = Const "False" boolean

identity = Abs "identity" "typevar" (Abs "" "x" (Var "x" (Dep (Var "typevar" Univ))) (Func (Dep $ Var "typevar" Univ) (Dep $ Var "typevar" Univ))) (Func Univ (Func (Dep $ Var "typevar" Univ) (Dep $ Var "typevar" Univ)))


boolToVehical = Abs "Vehicle" "b" (TypeTerm $ Dep (Var "b" boolean)) (Func boolean Univ)
bicycle = App boolToVehical true
car = App boolToVehical false