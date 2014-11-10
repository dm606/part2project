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
  "y"), Universe)], Identifier "x"))));
  ("2", ReplExpression (EDeclaration ([ DSimpleType (Ident "Bool", [Constr
  (Ident "false", EIdentifier (Ident "Bool")); Constr (Ident "true", EIdentifier
  (Ident "Bool"))]); DLetRec (Ident "x", EUnitType, EUnit) ], EUnit), SEMISEMI
  ";;"), Expression (LocalDeclaration ([ Type ("Bool", [], Universe, [("false",
  Identifier "Bool"); ("true", Identifier "Bool")]); LetRec ("x", UnitType,
  Unit) ], Unit)));
  ("3", ReplExpression (ETimes (EUniverse, EUniverse), SEMISEMI ";;"),
  Expression (Sigma (Underscore, Universe, Universe)));
  ("4", ReplDeclaration ([DType (Ident "Vec", [Param (BName (Ident "A"),
  EUniverse)], EArrow (EIdentifier (Ident "Nat"), EUniverse), [ Constr (Ident
  "nil", EApplication (EApplication (EIdentifier (Ident "Vec"), EIdentifier
  (Ident "A")), EIdentifier (Ident "zero"))) ])], SEMISEMI ";;"), Declaration
  [Type ("Vec", [(Name "A", Universe)], Pi (Underscore, Identifier "Nat",
  Universe), [ ("nil", Application (Application (Identifier "Vec", Identifier
  "A"), Identifier "zero")) ])]);
  ("5", ReplExpression (ELambda ([BName (Ident "x"); BName (Ident "y")], EUnit),
  SEMISEMI ";;"), Expression (Lambda (Name "x", Lambda (Name "y", Unit))))
  ])

let test_eq_resugar (name, d, expected) =
  name >:: fun _ -> (assert_equal (resugar d) expected)

let test_resugar = "resugar" >::: (map test_eq_resugar [
  ("1", Expression (Pi (Underscore, Identifier "Nat", Application (Function
  [(PatternPair (PatternUnderscore, PatternIdentifier "y"), Universe)],
  Identifier "x"))), ReplExpression (EArrow (EIdentifier (Ident "Nat"), EMatch
  (EIdentifier (Ident "x"), [CCase (PPair (PUnderscore, PIdentifier (Ident
  "y")), EUniverse)])), SEMISEMI ";;"));
  ("2", Expression (LocalDeclaration ([ Type ("Bool", [], Universe, [("false",
  Identifier "Bool"); ("true", Identifier "Bool")]); LetRec ("x", UnitType,
  Unit) ], Unit)), ReplExpression (EDeclaration ([ DSimpleType (Ident "Bool",
  [Constr (Ident "false", EIdentifier (Ident "Bool")); Constr (Ident "true",
  EIdentifier (Ident "Bool"))]); DLetRec (Ident "x", EUnitType, EUnit) ],
  EUnit), SEMISEMI ";;"));
  ("3", Expression (Sigma (Underscore, Universe, Universe)), ReplExpression
  (ETimes (EUniverse, EUniverse), SEMISEMI ";;"));
  ("4", Declaration [Type ("Vec", [(Name "A", Universe)], Pi (Underscore,
  Identifier "Nat", Universe), [ ("nil", Application (Application (Identifier
  "Vec", Identifier "A"), Identifier "zero")) ])], ReplDeclaration ([DType
  (Ident "Vec", [Param (BName (Ident "A"), EUniverse)], EArrow (EIdentifier
  (Ident "Nat"), EUniverse), [ Constr (Ident "nil", EApplication (EApplication
  (EIdentifier (Ident "Vec"), EIdentifier (Ident "A")), EIdentifier (Ident
  "zero"))) ])], SEMISEMI ";;"));
  ("5", Expression (Lambda (Name "x", Lambda (Name "y", Unit))), ReplExpression
  (ELambda ([BName (Ident "x"); BName (Ident "y")], EUnit), SEMISEMI ";;"))
  ])

let test_syntax = "syntax" >::: [test_desugar; test_resugar]
