{-# OPTIONS_GHC -W #-}

module DepTypes where

import Data.List
import Data.Maybe
import Helpers

data Term
  = Var String
  | Const String Term
  | Abs (String, Term) Term
  | App Term Term
  | -- Match consists of a term to match, and a list of (matchee, result) pairs
    Match Term [(Term, Term)]
  | -- (String: Term) -> (Term)
    Func (String, Term) Term
  | -- Universes
    Type0
  | Type1
  | Type2
  deriving (Eq, Show)

{-
instance Show Term where
  show (Var s) = s
  show (Const s t) = s <> ": " <> show t
  show (Abs (s, tt) t) = "\\(" <> s <> ": " <> show tt <> "). " <> show t
  show (App t1 t2) = "(" <> show t1 <> ") " <> show t2
  show (Match m ts) = "match " <> show m <> " where\n" <> foldl (\acc -> \t -> acc <> "| " <> t <> "\n") "" (map show ts)

  show (Func t1 t2) = show t1 <> " -> " <> show t2
  show Type0 = "Type0"
  show Type1 = "Type1"
  show Type2 = "Type2"
-}

data ContextElement = Elem
  { elName :: String,
    ty :: Term
  }
  deriving (Show)

-- Named terms (a list of which is like a Heap)
data NamedTerm = Named
  { name :: String,
    term :: Term
  }
  deriving (Show)

-- subs T s e = T[s/e]
subs :: Term -> String -> Term -> Term
-- Variable: substitute if variable name is equal to s
subs (Var x) s e = case x == s of
  True -> e
  False -> Var x
-- Const: only substitute in the type
subs (Const x t) s e = Const x (subs t s e)
-- Application: substitute on each side
subs (App f x) s e = App (subs f s e) (subs x s e)
-- Abstraction: always substitute in the type; substitute in the body IF unbound (var != s)
subs (Abs (var, t) x) s e = case var == s of
  True -> Abs (var, (subs t s e)) x
  False -> Abs (var, (subs t s e)) (subs x s e)
subs (Func (p, l) r) s e = Func (p, subs l s e) (if p == s then r else subs r s e)
subs (Match m arr) s e = Match (subs m s e) $ map (\(t1, t2) -> (t1, subs t2 s e)) arr
subs univ _ _ = univ

-- perform one step
step :: [NamedTerm] -> Term -> Term
-- Var: replace with term on the HEAP!
step vars (Var s) = fromMaybe (Var s) $ fmap term $ find ((==) s . name) vars
step vars (App e1 e2) =
  if not $ isNormal vars e1
    then App (step vars e1) e2 -- if t1 can step, step it
    else
      if not $ isNormal vars e2
        then App e1 (step vars e2) -- if t2 can step, step it
        else case e1 of
          Abs (var, _) x -> subs x var e2 -- otherwise, if t1 is an abstraction, substitute
          _ -> (App e1 e2) -- and finally, leave it be if nothing steps
step vars (Match m arr) =
  if not $ isNormal vars m
    then Match (step vars m) arr
    else stepMatch vars m arr
step _ other = other

-- helper for stepping on a Match
stepMatch :: [NamedTerm] -> Term -> [(Term, Term)] -> Term
stepMatch vars m arr = case find (not . isNormal vars . fst) arr of
  Just (l, r) ->
    let newArr = map (\(x, y) -> if x == l then (step vars l, r) else (x, y)) arr -- if there is a non-normal term, then step it
     in Match m newArr
  Nothing -> fromMaybe (Match m arr) $ firstJust (matchApp m) arr -- done normalizing, now do the matching

-- apply match to one term
matchApp :: Term -> (Term, Term) -> Maybe Term
matchApp e (Var s, right) = Just $ subs right s e -- if down to a variable, then just substitute
matchApp (Const s1 _) (Const s2 _, right) =
  -- if down to constants, then just check if they're equal
  if s1 /= s2
    then Nothing
    else Just right -- matchApp t1 (t2, tt)
matchApp (App l1 r1) (App l2 r2, right) =
  -- if it's an Application recursively check we're applying the same things
  do
    ml <- matchApp l1 (l2, right) -- match first term
    matchApp r1 (r2, ml) -- then match second term
    -- only allow Applications of constants; anything else fails
matchApp _ _ = Nothing

-- eval = step until no more stepping
eval :: [NamedTerm] -> Term -> Term
eval vars t =
  -- start off by replacing
  let st = step vars t
   in if st == t
        then t
        else eval vars st

-- evaluates list of named terms in order, then evaluates final expression
-- IMPORTANT: only allows terms to reference terms defined before it
evalAll :: [NamedTerm] -> Term -> Term
evalAll terms = eval $ evalAllHelper (reverse terms)

-- helper which evaluates from first list, and when done, pushes to the second
-- takes the original list in REVERSE order
evalAllHelper :: [NamedTerm] -> [NamedTerm]
evalAllHelper [] = []
evalAllHelper (Named n x : xs) =
  let done = evalAllHelper xs
   in (Named n (eval done x)) : done

-- check if term can still step
isNormal :: [NamedTerm] -> Term -> Bool
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
checkFuncTypeEqualityModVar t1 t2 = t1 ?= t2

-- infer types in a match term
inferTypes :: Term -> Term -> Maybe (Term, [ContextElement])
inferTypes tt (Const _ t) = if (checkFuncTypeEqualityModVar t tt) then Just (t, []) else Nothing
inferTypes tt (App left (Var x)) =
  inferTypes (Func ("", (Var "")) tt) left
    >>= ( \(t, ctx) -> case t of
            Func (_, l) r -> if (checkFuncTypeEqualityModVar r tt) then Just (r, Elem x l : ctx) else Nothing
            _ -> Nothing
        )
inferTypes _ _ = Nothing -- nothing else allowed in Match term

-- Custom equals for terms, since we don't really care about parameter name
termEq :: Term -> Term -> Bool -- # TODO: do we need to eval beforer checking equality?
termEq (Func (_, a1) b1) (Func (_, a2) b2) = a1 == a2 && b1 `termEq` b2
termEq t1 t2 = t1 == t2

infix 4 ?=

(?=) = termEq

-- TO THINK ABOUT
-- - interpretting it as logic (for all ....)
-- - next consideration: how to get it to work with functions which evaluate types?

checkType :: [NamedTerm] -> [ContextElement] -> Term -> Maybe Term
checkType _ ctx (Var x) = find (\e -> elName e == x) ctx >>= return . ty
checkType terms ctx (Const _ t) = let evaled = eval terms t in 
    do
  checkType terms ctx evaled  
  return evaled -- return evaluate type, as long as the type itself is well typed
checkType terms ctx (Abs (x, t) tt) = checkType terms (Elem x t : ctx) tt >>= Just . Func (x, eval terms t)
checkType terms ctx (App t1 t2) =
  case (checkType terms ctx t1, checkType terms ctx t2) of
    (Just (Func (p, ct1) rt), Just ct2) -> if eval terms ct1 ?= eval terms ct2 then Just $ subs rt p t2 else Nothing
    _ -> Nothing
checkType terms ctx (Match m (x : xs)) =
  ( do
      -- first get the expected left hand side type
      ct <- fmap (eval terms) $ checkType terms ctx m
      -- handle the first (term, term)
      (it1, ictx1) <- inferTypes ct (eval terms $ fst x) -- eval to ensure it's in normal form
      -- check that the infered type is correct, and return the right hand side type
      rt <- (if it1 ?= ct then checkType terms (ictx1 <> ctx) (snd x) else Nothing)
      -- fold over the rest of the list
      foldl
        ( \macc -> \(l, r) ->
            case macc of
              Nothing -> Nothing
              Just acc ->
                ( do
                    -- get (infered type, infered context) from left hand side
                    (it, ictx) <- inferTypes ct (eval terms l)
                    ctr <- checkType terms (ictx <> ctx) r
                    ( if it ?= ct && acc ?= ctr
                        then Just acc
                        else Nothing
                      )
                )
        )
        (Just rt)
        xs
  )
checkType _ _ (Match _ []) = Nothing -- can't have empty match
checkType _ _ Type0 = Just Type1
checkType _ _ Type1 = Just Type2
checkType _ _ Type2 = Nothing
checkType terms ctx (Func (p, t1) t2) =
  do
    ct1 <- checkType terms ctx t1
    ct2 <- checkType terms (Elem p t1 : ctx) t2 -- add parameter to context
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



-- eval and checktype
evalAndCT :: [NamedTerm] -> [ContextElement] -> Term -> Maybe Term
evalAndCT terms ctx e = do
  checkType terms ctx e 
  return $ eval terms e

-- takes terms in REVERSE order
evalAndCTNamed :: [NamedTerm] -> [ContextElement] -> Either NamedTerm [NamedTerm]
evalAndCTNamed [] _ = Right []
evalAndCTNamed (x : xs) ctx = do 
  finTerms <- evalAndCTNamed xs ctx
  let subsCtx = map (\(Elem name e) -> Elem name (subsAll finTerms e)) ctx in
    let subsE = subsAll finTerms (term x) in
      case evalAndCT finTerms subsCtx subsE of
        Nothing -> Left (Named (name x) subsE)
        Just e -> Right (Named (name x) e : finTerms)

subsAll :: [NamedTerm] -> Term -> Term 
subsAll terms e = foldl (\acc -> \(Named name ne) -> subs acc name ne) e terms

evalFinal :: [NamedTerm] -> [ContextElement] -> Term -> Either NamedTerm Term 
evalFinal terms ctx e = do
  finTerms <- evalAndCTNamed (reverse terms) ctx
  return $ eval finTerms e