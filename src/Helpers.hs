{-# OPTIONS_GHC -W #-}

module Helpers where 

firstJust :: (a -> Maybe b) -> [a] -> Maybe b 
firstJust _ [] = Nothing 
firstJust f (x:xs) = case f x of
  Just y -> Just y
  Nothing -> firstJust f xs


strEq :: String -> String -> Bool
strEq [] [] = True
strEq (x:xs) (y:ys) = x == y && strEq xs ys
strEq _ _ = False