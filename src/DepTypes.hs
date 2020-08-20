{-# OPTIONS_GHC -W #-}

module DepTypes where

import Data.List
import Data.Maybe
import Helpers
import Lib
import Data.Bifunctor (first, Bifunctor(bimap))

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
checkTypeEqModVar :: Term -> Term -> Bool
checkTypeEqModVar (Var _) _ = True
checkTypeEqModVar _ (Var _) = True
checkTypeEqModVar (Func (_, l1) r1) (Func (_, l2) r2) =
  checkTypeEqModVar l1 l2 && checkTypeEqModVar r1 r2
checkTypeEqModVar (App l1 r1) (App l2 r2) = 
  checkTypeEqModVar l1 l2 && checkTypeEqModVar r1 r2
checkTypeEqModVar t1 t2 = t1 ?= t2

-- infer types in a match term
inferTypes :: Term -> Term -> Either String (Term, [ContextElement])
inferTypes tt (Const c t) = if (checkTypeEqModVar t tt) then Right (t, []) 
                            else Left $ "Expected type was " <> prettyPrint tt <>
                                        "But actual type was" <> prettyPrint t
inferTypes tt (App left right) = 
  let leftInfer = inferTypes (Func ("", (Var "")) tt) left in
    case leftInfer of 
      Left mess -> Left $ em <> mess
      Right (funcTy, ctx) ->
        case funcTy of
          Func (p, l) r -> case (checkTypeEqModVar r tt) of
            True -> case right of 
                      Var x -> Right (r, Elem x l : ctx)
                      Const c t -> if l ?= t then Right (subs r p (Const c t), ctx) 
                                    else Left $ "Types don't match " <> em <> "\n" <>
                                                "Expected was " <> prettyPrint l <> "\n" <>
                                                "Actual was " <> prettyPrint t
                      App left2 right2 -> do
                        (_, newCtx) <- inferTypes l (App left2 right2)
                        Right (r, newCtx <> ctx)
                      _ -> Left $ "Right side not Var or Const or App" <> em
            False -> Left $ "Types not equal " <> em
          _ -> Left $ prettyPrint funcTy <> "Not a function " <> em
    where em = errorMessage (App left right)
inferTypes _ _ = Left "" -- nothing else allowed in Match term

-- Custom equals for terms, since we don't really care about parameter name
termEq :: Term -> Term -> Bool
termEq (Func (_, a1) b1) (Func (_, a2) b2) = a1 == a2 && b1 `termEq` b2
termEq t1 t2 = t1 == t2

infix 4 ?=

(?=) = termEq

-- TO THINK ABOUT
-- - interpretting it as logic (for all ....)
-- - next consideration: how to get it to work with functions which evaluate types?

checkType :: [NamedTerm] -> [ContextElement] -> Term -> Either String Term
checkType _ ctx (Var x) = case find (\e -> elName e == x) ctx of
  Nothing -> Left $ errorMessage (Var x) -- error message
  Just t -> Right $ ty t
checkType terms ctx (Const c t) = 
  let evaled = eval terms t in 
    let ct = checkType terms ctx evaled in
      bimap ((<>) $ errorMessage (Const c t))
            (\_ -> evaled) -- return evaluated type, as long as the type itself is well typed
            ct 
checkType terms ctx (Abs (x, t) tt) = 
  let ct = checkType terms (Elem x t : ctx) tt in 
    bimap ((<>) $ errorMessage (Abs (x, t) tt))
          (\typ -> Func (x, eval terms t) typ)
          ct
checkType terms ctx (App e1 e2) =
  case checkType terms ctx e1 of 
    Left message -> Left $ em <> message 
    Right (Func (p, ct1) rt) -> 
      case checkType terms ctx e2 of
        Left message -> Left $ em <> message 
        Right ct2 -> if eval terms ct1 ?= eval terms ct2 then Right $ subs rt p e2 
                      else Left $ "Application types don't match " <> em
    Right _ -> Left $ "Left term is not a function type " <> em
  where em = errorMessage (App e1 e2)
checkType terms ctx (Match m (x : xs)) =
  ( do
      -- first get the expected left hand side type
      ct <- fmap (eval terms) $ checkType terms ctx m
      -- handle the first (term, term)
      (_, ictx1) <- first (\mess -> "Couldn't infer type at " <> errorMessage (fst x) <> 
                                     "Expected type was " <> prettyPrint ct <> " \n" <>
                                     mess)
                    $ inferTypes ct (eval terms $ fst x) -- eval to ensure it's in normal form
      -- check that the infered type is correct, and return the right hand side type
      -- rt <- (if it1 ?= ct then checkType terms (ictx1 <> ctx) (snd x) else Nothing)
      rt <- checkType terms (ictx1 <> ctx) (snd x)
      -- fold over the rest of the list
      foldl
        ( \eacc -> \(l, r) -> do
            acc <- eacc
            (do
                -- get (infered type, infered context) from left hand side
                (_, ictx) <- first (\mess -> "Couldn't infer type at " <> errorMessage l <> 
                                     "Expected type was " <> prettyPrint ct <> " \n" <>
                                     mess)
                              $ inferTypes ct (eval terms l)
                ctr <- checkType terms (ictx <> ctx) r
                if acc ?= ctr
                    then Right acc
                    else Left $ "Term with type " <> show ctr <> " doesn't match the other match terms type of "
                      <> show acc 
                      <> errorMessage r)
        )
        (Right rt)
        xs
  )
checkType _ _ (Match _ []) = Left "Empty match" -- can't have empty match
checkType _ _ Type0 = Right Type1
checkType _ _ Type1 = Right Type2
checkType _ _ Type2 = Left "You've reached the top of the universe"
checkType terms ctx (Func (p, t1) t2) =
  do
    ct1 <- checkType terms ctx t1
    ct2 <- checkType terms (Elem p t1 : ctx) t2 -- add parameter to context
    coverType ct1 ct2

-- helper function for calculating Func type
coverType :: Term -> Term -> Either String Term
coverType Type2 _ = Right Type2
coverType _ Type2 = Right Type2
coverType Type1 _ = Right Type1
coverType _ Type1 = Right Type1
coverType Type0 _ = Right Type0
coverType _ Type0 = Right Type0
coverType _ _ = Left $ "Bad function type"



-- eval and checktype
evalAndCT :: [NamedTerm] -> [ContextElement] -> Term -> Either String Term
evalAndCT terms ctx e = do
  checkType terms ctx e 
  return $ eval terms e

-- takes terms in REVERSE order
evalAndCTNamed :: [NamedTerm] -> [ContextElement] -> Either String [NamedTerm]
evalAndCTNamed [] _ = Right []
evalAndCTNamed (x : xs) ctx = do 
  finTerms <- evalAndCTNamed xs ctx
  let subsCtx = map (\(Elem name e) -> Elem name e) ctx in
    let e = term x in
      case evalAndCT finTerms subsCtx e of
        Left mess -> Left $ "Checktype failure in term named: " <> (name x) <> "\n" <> mess
        Right e -> Right (Named (name x) e : finTerms)

subsAll :: [NamedTerm] -> Term -> Term 
subsAll terms e = foldl (\acc -> \(Named name ne) -> subs acc name ne) e terms

subsAllInNamedList :: [NamedTerm] -> [NamedTerm]
subsAllInNamedList [] = []
subsAllInNamedList ((Named x e) : xs) = let subsedAbove = subsAllInNamedList xs in
  (Named x (subsAll subsedAbove e)) : subsedAbove

evalFinal :: [NamedTerm] -> [ContextElement] -> Term -> Either String (Term, Term)
evalFinal terms ctx e = let subsedTerms = subsAllInNamedList $ reverse terms in
  let subsedCtx = map (\(Elem name e) -> Elem name (subsAll subsedTerms e)) ctx in
      do
    finTerms <- evalAndCTNamed subsedTerms subsedCtx
    ct <- checkType subsedTerms subsedCtx (subsAll subsedTerms e)
    return $ (eval finTerms e, ct)