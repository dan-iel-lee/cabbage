{-# OPTIONS_GHC -W #-}

module DepTypes where

import Data.List
import Helpers
import Data.Maybe

data Term
  = Var String
  | Value String Term
  | Abs (String, Term) Term
  | App Term Term
  | Match Term [(Term, Term)]

  | Func (String, Term) Term
  | Type0
  | Type1
  | Type2
  deriving (Eq, Show)
{-
instance Eq Term where
  (==) (Var a1) (Var a2) = a1 == a2
  (==) (Value a1 b1) (Value a2 b2) = a1 == a2 && b1 == b2
  (==) (Abs a1 b1) (Abs a2 b2) = a1 == a2 && b1 == b2
  (==) (Match a1 b1) (Match a2 b2) = a1 == a2 && b1 == b2
  (==) Type0 Type0 = True
  (==) Type1 Type1 = True
  (==) Type2 Type2 = True
  -- custom equals for Func, name doesn't matter 
  (==) (Func (_, a1) b1) (Func (_, a2) b2) = a1 == a2 && b1 == b2
  (==) _ _ = False -}

data ContextElement = Elem
  { elName :: String,
    ty :: Term
  }
  deriving (Show)

-- used by Parser as well
data Identifier = Named { name :: String
                        , term :: Term} deriving (Show)

-- subs T s tt = T[s/tt]
subs :: Term -> String -> Term -> Term
subs (Var x) s tt = case x == s of
  True -> tt
  False -> Var x
subs (App f x) s tt = App (subs f s tt) (subs x s tt)
subs (Abs (var, t) x) s tt = case var == s of
  True -> Abs (var, (subs t s tt)) x
  False -> Abs (var, (subs t s tt)) (subs x s tt)
subs (Value x t) s tt = Value x (subs t s tt)
subs (Func (p, l) r) s tt = Func (p, if p == s then l else (subs l s tt)) (subs r s tt)
subs (Match m arr) s tt = Match (subs m s tt) $ map (\(t1, t2) -> (t1, subs t2 s tt)) arr
subs val _ _ = val

-- perform one step
step :: [Identifier] -> Term -> Term
step vars (Var s) = fromMaybe (Var s) $ fmap term $ find ((==) s . name) vars
step vars (App t1 t2) =
  if not $ isNormal vars t1
    then App (step vars t1) t2 -- if t1 can step, step it
    else
      if not $ isNormal vars t2
        then App t1 (step vars t2) -- if t2 can step, step it
        else case t1 of
          Abs (var, _) x -> subs x var t2 -- if t1 is an abstraction, substitute
          _ -> (App t1 t2)
step vars (Match m arr) =
  if not $ isNormal vars m
    then Match (step vars m) arr
    else stepMatch vars m arr
step _ other = other

-- helper for stepping on a Match
stepMatch :: [Identifier] -> Term -> [(Term, Term)] -> Term
stepMatch vars tt arr = case find (not . isNormal vars . fst) arr of
  Just (l, r) ->
    let newArr = map (\(x, y) -> if x == l then (step vars l, r) else (x, y)) arr -- if there is a non-normal term, then step it
     in Match tt newArr
  Nothing -> case tt of
    Value s t -> case fmap snd $ find (\(x, _) -> x == (Value s t)) arr of
      Just j -> j -- find matching value
      Nothing -> Match (Value s t) arr -- doesn't step
    App t1 t2 -> case firstJust (matchApp (App t1 t2)) arr of
      Just j -> j -- return matching value
      Nothing -> Match (App t1 t2) arr -- doesn't step
    _ -> Match tt arr -- doesn't step

-- apply match to one term
matchApp :: Term -> (Term, Term) -> Maybe Term
matchApp t (Var s, tt) = Just $ subs tt s t -- if down to a variable, then just substitute
matchApp (Value s1 t1) (Value s2 t2, tt) =
  if s1 /= s2
    then Nothing
    else matchApp t1 (t2, tt)
matchApp (App l1 r1) (App l2 r2, tt) =
  -- if it's an Application recursively check we're applying the same things
  do
    ml <- matchApp l1 (l2, tt) -- match first term
    matchApp r1 (r2, ml) -- then match second term
    -- types
matchApp (Func (_, l1) r1) (Func (_, l2) r2, tt) =
  -- Func type similar to Application
  do
    ml <- matchApp l1 (l2, tt) -- match first term
    matchApp r1 (r2, ml) -- then match second term
matchApp Type0 (Type0, tt) = Just tt
matchApp Type1 (Type1, tt) = Just tt
matchApp Type2 (Type2, tt) = Just tt
matchApp _ _ = Nothing -- otherwise match fails

-- eval = step until no more stepping
eval :: [Identifier] -> Term -> Term
eval vars t =
  let st = step vars t
   in if st == t
        then t
        else eval vars st

-- check if term can still step
isNormal :: [Identifier] -> Term -> Bool
isNormal vars t = step vars t == t

-- helper for inferTypes
checkFuncTypeEqualityModVar :: Term -> Term -> Bool
checkFuncTypeEqualityModVar (Func (_, l1) r1) (Func (_, l2) r2) =
  ( case (l1, l2) of
      (Var _, _) -> True
      (_, Var _) -> True
      (_, _) -> l1 == l2
  )
    && checkFuncTypeEqualityModVar r1 r2
checkFuncTypeEqualityModVar t1 t2 = t1 == t2

-- infer types in a match term
inferTypes :: Term -> Term -> Maybe (Term, [ContextElement])
inferTypes tt (Value _ t) = if (checkFuncTypeEqualityModVar t tt) then Just (t, []) else Nothing
inferTypes tt (App left (Var x)) =
  inferTypes (Func ("", (Var "")) tt) left
    >>= ( \(t, ctx) -> case t of
            Func (_, l) r -> if (checkFuncTypeEqualityModVar r tt) then Just (r, Elem x l : ctx) else Nothing
            _ -> Nothing
        )
inferTypes _ _ = Nothing -- nothing else allowed in Match term

-- Custom equals for terms, since we don't really care about parameter name
termEq :: Term -> Term -> Bool
termEq (Func (_, a1) b1) (Func (_, a2) b2) = a1 == a2 && b1 == b2
termEq t1 t2 = t1 == t2
infix 4 ?=
(?=) = termEq

checkType :: [ContextElement] -> Term -> Maybe Term
checkType ctx (Var x) = find (\e -> elName e == x) ctx >>= return . ty
checkType ctx (Value _ t) = do
  checkType ctx t
  return t -- it's just 't', as long as t itself is well typed
checkType ctx (Abs (x, t) tt) = checkType (Elem x t : ctx) tt >>= Just . Func (x, t)
checkType ctx (App t1 t2) = case (checkType ctx t1, checkType ctx t2) of
  (Just (Func (p, ct1) rt), Just ct2) -> if ct1 ?= ct2 then Just $ subs rt p t2 else Nothing
  _ -> Nothing
checkType ctx (Match m (x : xs)) =
  ( do
      -- first get the expected left hand side type
      ct <- checkType ctx m
      -- handle the first (term, term)
      (it1, ictx1) <- inferTypes ct (eval [] $ fst x) -- eval to ensure it's in normal form
      -- check that the infered type is correct, and return the right hand side type
      rt <- (if it1 ?= ct then checkType (ictx1 <> ctx) (snd x) else Nothing)
      -- fold over the rest of the list
      foldl
        ( \macc -> \(l, r) ->
            case macc of
              Nothing -> Nothing
              Just acc ->
                ( do
                    -- get (infered type, infered context) from left hand side
                    (it, ictx) <- inferTypes ct (eval [] l)
                    ctr <- checkType (ictx <> ctx) r
                    (if it ?= ct && acc ?= ctr
                        then Just acc
                        else Nothing
                      )
                )
        )
        (Just rt)
        xs
  )
checkType _ (Match _ []) = Nothing
checkType _ Type0 = Just Type1
checkType _ Type1 = Just Type2
checkType _ Type2 = Nothing
checkType ctx (Func (p, t1) t2) =
  do
    ct1 <- checkType ctx t1
    ct2 <- checkType (Elem p t1 : ctx) t2 -- add parameter to context
    coverType ct1 ct2

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
{-
prod = Value "Prod" (Func Type0 (Func Type0 Type0))
mkprod = Abs ("A", Type0) (Abs ("B", Type0) (Value "mkprod" (Func (Var "A") (Func (Var "B") (App (App prod (Var "A")) (Var "B"))))))

first = Abs ("x", App (App prod natural) natural)

prod12 = App mkprod natural

natural :: Term
natural = Value "Nat" Type0
z = Value "Zero" natural
s = Value "Succ" (Func natural natural)

minusone = Abs ("n", natural) (Match (Var "n") [(z, z), (App s (Var "m"), Var "m")])
-}