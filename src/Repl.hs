
module Repl where 
  
import DepTypes

prettyPrint :: Term -> String 
prettyPrint (Var s) = s 
prettyPrint (Const s _) = s 
prettyPrint (App e1 e2) = "(" <> prettyPrint e1 <> " " <> prettyPrint e2 <> ")"
prettyPrint (Abs (s, _) e) = "\\" <> s <> ". " <> prettyPrint e 
prettyPrint (Match m arr) = "match " <> prettyPrint m <> " where\n" <> foldl (\acc -> \(le, re) -> acc <> "  | " <> prettyPrint le <> " -> " <> prettyPrint re <> "\n") "" arr
prettyPrint (Func (s, e1) e2) = "(" <> s <> ": " <> prettyPrint e1 <> ")" <> " -> " <> prettyPrint e2
prettyPrint Type0 = "Type0"
prettyPrint Type1 = "Type1"
prettyPrint Type2 = "Type2"