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

-- perform one step
step :: Term -> Term 
step (Named _ t) = t
step (App t1 t2) = if not $ isNormal t1 then App (step t1) t2 else -- if t1 can step, step it
  if not $ isNormal t2 then App t1 (step t2) else -- if t2 can step, step it
    case t1 of 
      Abs (var, _) x -> subs x var t2 -- if t1 is an abstraction, substitute
      _ -> (App t1 t2)
step (Match m arr) = if not $ isNormal m then Match (step m) arr else 
  stepMatch m arr 
step other = other

eval :: Term -> Term 
eval t = let st = step t in 
  if st == t then t else 
    eval st

isNormal :: Term -> Bool
isNormal t = step t == t

stepMatch :: Term -> [(Term, Term)] -> Term 
stepMatch tt arr = case find (not . isNormal . fst) arr of 
  Just (l, r) -> 
    let newArr = map (\(x, y) -> if x == l then (step l, r) else (x, y)) arr in -- if there is a non-normal term, then step it
      Match tt newArr
  Nothing -> case tt of 
    Value s t -> case fmap snd $ find (\(x, _) -> x == (Value s t)) arr of
                    Just j -> j -- find matching value
                    Nothing -> Match (Value s t) arr -- doesn't step
    App t1 t2 -> case firstJust (matchApp (App t1 t2)) arr of 
                    Just j -> j -- return matching value
                    Nothing -> Match (App t1 t2) arr -- doesn't step 
    _ -> Match tt arr -- doesn't step

-- apply match
matchApp :: Term -> (Term, Term) -> Maybe Term 
matchApp t (Var s, tt) = Just $ subs tt s t -- if down to a variable, then just substitute
matchApp (Value s1 t1) (Value s2 t2, tt) = if s1 /= s2 then Nothing else 
  matchApp t1 (t2, tt)
matchApp (App l1 r1) (App l2 r2, tt) = -- if it's an Application recursively check we're applying the same things
    do
  ml <- matchApp l1 (l2, tt) -- match first term
  matchApp r1 (r2, ml) -- then match second term
-- types
matchApp (Func l1 r1) (Func l2 r2, tt) = -- Func type similar to Application
    do
  ml <- matchApp l1 (l2, tt) -- match first term
  matchApp r1 (r2, ml) -- then match second term
matchApp Type0 (Type0, tt) = Just tt 
matchApp Type1 (Type1, tt) = Just tt 
matchApp Type2 (Type2, tt) = Just tt 
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