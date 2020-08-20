{-# OPTIONS_GHC -W #-}

module Helpers where 

import Lib

firstJust :: (a -> Maybe b) -> [a] -> Maybe b 
firstJust _ [] = Nothing 
firstJust f (x:xs) = case f x of
  Just y -> Just y
  Nothing -> firstJust f xs

consMaybe :: Maybe a -> [a] -> [a]
consMaybe Nothing = id
consMaybe (Just x) = (:) x

eitherFromMaybe :: a -> Maybe b -> Either a b
eitherFromMaybe _ (Just j) = Right j 
eitherFromMaybe x _ = Left x

errorMessage :: Term -> String 
errorMessage t = message t <> " \n"
  where 
    message (Var x) = "Variable " <> x <> " not defined"
    message (Const c _) = "Const " <> c <> " is ill typed"
    message (Abs (x, t) e) = "At abstraction \\(" <> x <> ":" 
      <> prettyPrint t <> "). " <> prettyPrint e
    message (App e1 e2) = "At application " <> prettyPrint (App e1 e2)
    message (Func t1 t2) = "In type " <> prettyPrint (Func t1 t2)
    message (Match m arr) = "In " <> prettyPrint (Match m arr)
    message _ = ""