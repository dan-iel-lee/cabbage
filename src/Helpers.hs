{-# OPTIONS_GHC -W #-}

module Helpers where 

firstJust :: (a -> Maybe b) -> [a] -> Maybe b 
firstJust _ [] = Nothing 
firstJust f (x:xs) = case f x of
  Just y -> Just y
  Nothing -> firstJust f xs
