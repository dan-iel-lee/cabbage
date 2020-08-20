module Main where

import Lib
import DepTypes 
import Parser
import Repl

main :: IO ()
main = do 
  putStrLn "Enter file path"
  fp <- getLine 
  parseResult <- parseExpFromFile fp
  case parseResult of 
    Left error -> putStrLn $ show error 
    Right (terms, ctx, e) -> 
      do
        putStrLn $ show ctx
        case evalFinal terms ctx e of 
          Left error -> putStrLn $ show error 
          Right final -> putStrLn $ prettyPrint final 
