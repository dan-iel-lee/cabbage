{-# OPTIONS_GHC -W #-}

module DepTypes where

import Data.List
import Helpers

data Term = 
    Var String
  | Value String Term
  | Abs (String, Term) Term
  | App Term Term
  | Match Term [(Term, Term)]
  | Named String Term 
  
  | Func Term Term
  | Type0
  | Type1
  | Type2
  deriving (Eq, Show)


-- subs T s tt = T[s/tt]
subs :: Term -> String -> Term -> Term 
subs (Var x) s tt = case strEq x s of
  True -> tt 
  False -> Var x
subs (App f x) s tt = App (subs f s tt) (subs x s tt)
subs (Abs (var, t) x) s tt = case strEq var s of
  True -> Abs (var, (subs t s tt)) x
  False -> Abs (var, (subs t s tt)) (subs x s tt)
subs (Value x t) s tt = Value x (subs t s tt)
subs (Func l r) s tt = Func (subs l s tt) (subs r s tt)
subs (Match m arr) s tt = Match (subs m s tt) $ map (\(t1, t2) -> (t1, subs t2 s tt)) arr
subs val _ _ = val

-- # TODO: should this be Maybe?
-- perform one step
step :: Term -> Maybe Term 
step (Named _ t) = Just t
step (App (Abs (var, t) x) y) = step y >>= 
  (\r -> if r == y then
    (Just $ subs x var r) else
      Just $ App (Abs (var, t) x) r)
step (App x y) = step x >>=
  (\r -> if r == x then
    (Just $ App x y) else 
      step $ App r y)
-- step (App _ _) = Nothing -- first argument of Application must be an abstraction
step (Match m arr) = step m >>= \t -> stepMatch t arr
step other = Just other

stepMatch :: Term -> [(Term, Term)] -> Maybe Term 
stepMatch (Value s t) arr = fmap snd $ find (\(x, _) -> x == (Value s t)) arr -- find matching value
stepMatch (App t1 t2) arr = firstJust (matchApp (App t1 t2)) arr
stepMatch _ _ = Nothing -- I think it only works for Value and App?

matchApp :: Term -> (Term, Term) -> Maybe Term 
matchApp t (Var s, tt) = Just $ subs tt s t -- if down to a variable, then just substitute
matchApp (App f1 x1) (App f2 x2, tt) = -- if it's an Application, check we're applying the same things, then recurse
  if f1 == f2 then matchApp x1 (x2, tt) else Nothing 
matchApp _ _ = Nothing -- otherwise match fails


checkType :: Term -> Maybe Term 
checkType (Named _ t) = checkType t
checkType (Var _) = undefined -- # TODO make CONTEXT
checkType (Value _ t) = Just t 
checkType (Abs (_, t) tt) = checkType tt >>= Just . Func t
checkType (App t1 t2) = case (checkType t1, checkType t2) of
  (Just (Func ct1 rt), Just ct2) -> if ct1 == ct2 then Just rt else Nothing 
  _ -> Nothing 
checkType (Match m (x : xs)) = checkType m >>= \t1 -> foldl (\may -> \(l, r) -> 
  case may of
    Nothing -> Nothing 
    Just acc ->
      let ml = checkType l
          mr = checkType r
          in
        case (ml, mr) of
          (Just ctl, Just ctr) ->
            if t1 == ctl && acc == ctr then Just acc
            else Nothing
          _ -> Nothing) (checkType (snd x)) xs 
checkType (Match _ []) = Nothing 
checkType Type0 = Just Type1 
checkType Type1 = Just Type2
checkType Type2 = Nothing
checkType (Func t1 t2) = 
  do  { ct1 <- checkType t1 
      ; ct2 <- checkType t2 
      ; coverType ct1 ct2 }

-- helper function for calculating Func type
coverType :: Term -> Term -> Maybe Term 
coverType Type2 _ = Just Type2
coverType _ Type2 = Just Type2
coverType Type1 _ = Just Type1
coverType _ Type1 = Just Type1
coverType Type0 _ = Just Type0
coverType _ Type0 = Just Type0
coverType _ _ = Nothing 


-- Tests
prod = Value "Prod" (Func Type0 (Func Type0 Type0))
mkprod = Abs ("A", Type0) (Abs ("B", Type0) (Value "mkprod" (Func (Var "A") (Func (Var "B") (App (App prod (Var "A")) (Var "B"))))))

first = Abs ("x", App (App prod natural) natural) 

prod12 = App mkprod natural


natural :: Term
natural = Value "Nat" Type0
z = Value "Zero" natural 
s = Value "Succ" (Func natural natural) 

minusone = Abs ("n", natural) (Match (Var "n") [(z, z), (App s (Var "m"), Var "m")])