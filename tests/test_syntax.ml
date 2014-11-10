open List
open OUnit2

open AbsConcrete
open Abstract

let test_eq_desugar (name, d, expected) =
  name >:: fun _ -> (assert_equal (desugar d) expected)

let test_desugar = "desugar" >::: (map test_eq_desugar [
  ("1", ReplExpression (EArrow (EIdentifier (Ident "Nat"), EMatch (EIdentifier
  (Ident "x"), [CCase (PPair (PUnderscore, PIdentifier (Ident "y")),
  EUniverse)])), SEMISEMI ";;"), Expression (Pi (Underscore, Identifier "Nat",
  Application (Function [(PatternPair (PatternUnderscore, PatternIdentifier
  "y"), Universe)], Identifier "x"))))
])

let test_syntax = "syntax" >::: [test_desugar]
