open Lexing
open List
open OUnit2

open AbsConcrete
open Abstract
open Parser

let test_eq_parser (name, input, expected) =
  name >:: fun _ -> (assert_equal (parse_repl (from_string input)) expected)

let test_parser = "parser" >::: (map test_eq_parser [
  ("t1", "U;;", ReplExpression (EUniverse, SEMISEMI ";;"));
  ("t2", "let x : U = U;;", ReplDeclaration ([DLet (Ident "x", [], EUniverse,
  EUniverse)], SEMISEMI ";;"));
  ("t3", "let f : Nat -> Nat * Bool -> Nat = fun x _ -> succ x;;",
  ReplDeclaration ([DLet (Ident "f", [], EArrow (EIdentifier (Ident "Nat"),
  EArrow (ETimes (EIdentifier (Ident "Nat"), EIdentifier (Ident "Bool")),
  EIdentifier (Ident "Nat"))), ELambda ([BName (Ident "x"); BUnderscore],
  EApplication (EIdentifier (Ident "succ"), EIdentifier (Ident "x"))))],
  SEMISEMI ";;"));
  ("t4", "fun A -> A -> Empty;;", ReplExpression (ELambda ([BName (Ident "A")],
  EArrow (EIdentifier (Ident "A"), EIdentifier (Ident "Empty"))), SEMISEMI
  ";;"));
  ("t5", "function;;", ReplExpression (EFunction [], SEMISEMI ";;"));
  ("t6", "let rec f : Nat = zero and type Nat = zero : Nat | succ : (_:Nat) ->
  Nat;;", ReplDeclaration ([DLetRec (Ident "f", [], EIdentifier (Ident "Nat"),
  EIdentifier (Ident "zero")); DSimpleType (Ident "Nat", [Constr (Ident
  "zero", EIdentifier (Ident "Nat")); Constr (Ident "succ", EPi (BUnderscore,
  EIdentifier (Ident "Nat"), EIdentifier (Ident "Nat")))])], SEMISEMI ";;"));
  ("t7", "let f : U = U in type Empty = in Empty;;", ReplExpression
  (EDeclaration ([DLet (Ident "f", [], EUniverse, EUniverse)], EDeclaration
  ([DSimpleType (Ident "Empty", [])], EIdentifier (Ident "Empty"))), SEMISEMI
  ";;"));
  ("t8", "type Id (A : U) (a : A) : A -> U = | refl : Id A a a;;",
  ReplDeclaration ([DType (Ident "Id", [Param (BName (Ident "A"), EUniverse);
  Param (BName (Ident "a"), EIdentifier (Ident "A"))], EArrow (EIdentifier
  (Ident "A"), EUniverse), [Constr (Ident "refl", EApplication (EApplication
  (EApplication (EIdentifier (Ident "Id"), EIdentifier (Ident "A")), EIdentifier
  (Ident "a")), EIdentifier (Ident "a")))])], SEMISEMI ";;"));
  ("t9", "a (b c) d;;", ReplExpression (EApplication (EApplication (EIdentifier
  (Ident "a"), EApplication (EIdentifier (Ident "b"), EIdentifier (Ident "c"))),
  EIdentifier (Ident "d")), SEMISEMI ";;"));
  ("t10", "(x, y, z).1;;", ReplExpression (EProj1 (EPair (EIdentifier (Ident
  "x"), EPair (EIdentifier (Ident "y"), EIdentifier (Ident "z")))), SEMISEMI
  ";;"));
  ("t9", "let rec f (x : A) (_ : B) : U = fun z -> U;;", ReplDeclaration
  ([DLetRec (Ident "f", [Param (BName (Ident "x"), EIdentifier (Ident "A"));
  Param (BUnderscore, EIdentifier (Ident "B"))], EUniverse, ELambda ([BName
  (Ident "z")], EUniverse))], SEMISEMI ";;"))
  ])

let test_eq_desugar (name, input, expected) =
  name >:: fun _ -> (assert_equal (desugar input) expected)

let test_desugar = "desugar" >::: (map test_eq_desugar [
  ("t1", ReplExpression (EArrow (EIdentifier (Ident "Nat"), EMatch (EIdentifier
  (Ident "x"), [CCase (PPair (PUnderscore, PIdentifier (Ident "y")),
  EUniverse)])), SEMISEMI ";;"), Expression (Pi (Underscore, Identifier "Nat",
  Application (Function [(PatternPair (PatternUnderscore, PatternIdentifier
  "y"), Universe)], Identifier "x"))));
  ("t2", ReplExpression (EDeclaration ([DSimpleType (Ident "Bool", [Constr
  (Ident "false", EIdentifier (Ident "Bool")); Constr (Ident "true", EIdentifier
  (Ident "Bool"))]); DLetRec (Ident "x", [], EUnitType, EUnit) ], EUnit),
  SEMISEMI ";;"), Expression (LocalDeclaration ([Type ("Bool", [], Universe,
  [("false", Identifier "Bool"); ("true", Identifier "Bool")]); LetRec ("x",
  UnitType, Unit) ], Unit)));
  ("t3", ReplExpression (ETimes (EUniverse, EUniverse), SEMISEMI ";;"),
  Expression (Sigma (Underscore, Universe, Universe)));
  ("t4", ReplDeclaration ([DType (Ident "Vec", [Param (BName (Ident "A"),
  EUniverse)], EArrow (EIdentifier (Ident "Nat"), EUniverse), [Constr (Ident
  "nil", EApplication (EApplication (EIdentifier (Ident "Vec"), EIdentifier
  (Ident "A")), EIdentifier (Ident "zero"))) ])], SEMISEMI ";;"), Declaration
  [Type ("Vec", [(Name "A", Universe)], Pi (Underscore, Identifier "Nat",
  Universe), [ ("nil", Application (Application (Identifier "Vec", Identifier
  "A"), Identifier "zero")) ])]);
  ("t5", ReplExpression (ELambda ([BName (Ident "x"); BName (Ident "y")],
  EUnit), SEMISEMI ";;"), Expression (Lambda (Name "x", Lambda (Name "y",
  Unit))));
  ("t6", ReplDeclaration ([DLet (Ident "f", [Param (BName (Ident "x"),
  EUniverse); Param (BName (Ident "y"), EUnitType); Param (BUnderscore,
  EIdentifier (Ident "A"))], EUniverse, EUnitType)], SEMISEMI ";;"), Declaration
  ([Let ("f", Pi (Name "x", Universe, Pi (Name "y", UnitType, Pi (Underscore,
  Identifier "A", Universe))), Lambda (Name "x", Lambda (Name "y", Lambda
  (Underscore, UnitType))))]))
  ])

let test_eq_resugar (name, input, expected) =
  name >:: fun _ -> (assert_equal (resugar input) expected)

let test_resugar = "resugar" >::: (map test_eq_resugar [
  ("t1", Expression (Pi (Underscore, Identifier "Nat", Application (Function
  [(PatternPair (PatternUnderscore, PatternIdentifier "y"), Universe)],
  Identifier "x"))), ReplExpression (EArrow (EIdentifier (Ident "Nat"), EMatch
  (EIdentifier (Ident "x"), [CCase (PPair (PUnderscore, PIdentifier (Ident
  "y")), EUniverse)])), SEMISEMI ";;"));
  ("t2", Expression (LocalDeclaration ([Type ("Bool", [], Universe, [("false",
  Identifier "Bool"); ("true", Identifier "Bool")]); LetRec ("x", UnitType,
  Unit) ], Unit)), ReplExpression (EDeclaration ([DSimpleType (Ident "Bool",
  [Constr (Ident "false", EIdentifier (Ident "Bool")); Constr (Ident "true",
  EIdentifier (Ident "Bool"))]); DLetRec (Ident "x", [], EUnitType, EUnit) ],
  EUnit), SEMISEMI ";;"));
  ("t3", Expression (Sigma (Underscore, Universe, Universe)), ReplExpression
  (ETimes (EUniverse, EUniverse), SEMISEMI ";;"));
  ("t4", Declaration [Type ("Vec", [(Name "A", Universe)], Pi (Underscore,
  Identifier "Nat", Universe), [("nil", Application (Application (Identifier
  "Vec", Identifier "A"), Identifier "zero")) ])], ReplDeclaration ([DType
  (Ident "Vec", [Param (BName (Ident "A"), EUniverse)], EArrow (EIdentifier
  (Ident "Nat"), EUniverse), [Constr (Ident "nil", EApplication (EApplication
  (EIdentifier (Ident "Vec"), EIdentifier (Ident "A")), EIdentifier (Ident
  "zero"))) ])], SEMISEMI ";;"));
  ("t5", Expression (Lambda (Name "x", Lambda (Name "y", Unit))), ReplExpression
  (ELambda ([BName (Ident "x"); BName (Ident "y")], EUnit), SEMISEMI ";;"));
  ("t6", Declaration ([Let ("f", Pi (Underscore, Identifier "A", Pi (Name "x",
  Identifier "B", Pi (Name "y", Identifier "C", Pi (Underscore, Identifier "D",
  UnitType)))), Lambda (Underscore, Lambda (Name "x", Lambda (Name "y", Lambda
  (Name "z", Unit)))))]), ReplDeclaration ([DLet ( Ident "f", [Param
  (BUnderscore, EIdentifier (Ident "A")); Param (BName (Ident "x"), EIdentifier
  (Ident "B")); Param (BName (Ident "y"), EIdentifier (Ident "C"))], EArrow
  (EIdentifier (Ident "D"), EUnitType), ELambda ([BName (Ident "z")], EUnit))],
  SEMISEMI ";;"))
  ])

let test_syntax = "syntax" >::: [test_parser; test_desugar; test_resugar]
