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
  ("t2", "let x : U = U;;", ReplDeclarations (LLDCons ([DLet (Ident "x", [],
  EUniverse, EUniverse)], LLDEmpty), SEMISEMI ";;"));
  ("t3", "let f : Nat -> Nat * Bool -> Nat = fun x _ -> succ x;;",
  ReplDeclarations (LLDCons ([DLet (Ident "f", [], EArrow (EIdentifier (Ident
  "Nat"), EArrow (ETimes (EIdentifier (Ident "Nat"), EIdentifier (Ident
  "Bool")), EIdentifier (Ident "Nat"))), ELambda ([BName (Ident "x");
  BUnderscore], EApplication (EIdentifier (Ident "succ"), EIdentifier (Ident
  "x"))))], LLDEmpty), SEMISEMI ";;"));
  ("t4", "fun A -> A -> Empty;;", ReplExpression (ELambda ([BName (Ident "A")],
  EArrow (EIdentifier (Ident "A"), EIdentifier (Ident "Empty"))), SEMISEMI
  ";;"));
  ("t5", "function;;", ReplExpression (EFunction [], SEMISEMI ";;"));
  ("t6", "let rec f : Nat = zero and type Nat = zero : Nat | succ : (_:Nat) ->
  Nat;;", ReplDeclarations (LLDCons ([DLetRec (Ident "f", [], EIdentifier
  (Ident "Nat"), EIdentifier (Ident "zero")); DSimpleType (Ident "Nat",
  [Constr (Ident "zero", EIdentifier (Ident "Nat")); Constr (Ident "succ", EPi
  (BUnderscore, EIdentifier (Ident "Nat"), EIdentifier (Ident "Nat")))])],
  LLDEmpty), SEMISEMI ";;"));
  ("t7", "let f : U = U in type Empty = in Empty;;", ReplExpression
  (EDeclaration ([DLet (Ident "f", [], EUniverse, EUniverse)], EDeclaration
  ([DSimpleType (Ident "Empty", [])], EIdentifier (Ident "Empty"))), SEMISEMI
  ";;"));
  ("t8", "type Id (A : U) (a : A) : A -> U = | refl : Id A a a;;",
  ReplDeclarations (LLDCons ([DType (Ident "Id", [Param (BName (Ident "A"),
  EUniverse); Param (BName (Ident "a"), EIdentifier (Ident "A"))], EArrow
  (EIdentifier (Ident "A"), EUniverse), [Constr (Ident "refl", EApplication
  (EApplication (EApplication (EIdentifier (Ident "Id"), EIdentifier (Ident
  "A")), EIdentifier (Ident "a")), EIdentifier (Ident "a")))])], LLDEmpty),
  SEMISEMI ";;"));
  ("t9", "a (b c) d;;", ReplExpression (EApplication (EApplication (EIdentifier
  (Ident "a"), EApplication (EIdentifier (Ident "b"), EIdentifier (Ident "c"))),
  EIdentifier (Ident "d")), SEMISEMI ";;"));
  ("t10", "(x, y, z).1;;", ReplExpression (EProj1 (EPair (EIdentifier (Ident
  "x"), EPair (EIdentifier (Ident "y"), EIdentifier (Ident "z")))), SEMISEMI
  ";;"));
  ("t9", "let rec f (x : A) (_ : B) : U = fun z -> U;;", ReplDeclarations
  (LLDCons ([DLetRec (Ident "f", [Param (BName (Ident "x"), EIdentifier (Ident
  "A")); Param (BUnderscore, EIdentifier (Ident "B"))], EUniverse, ELambda
  ([BName (Ident "z")], EUniverse))], LLDEmpty), SEMISEMI ";;"))
  ])

let test_eq_desugar_expression (name, input, expected) =
  name >:: fun _ -> (assert_equal (desugar_expression input) expected)

let test_desugar_expression = "desugar_expression" >::: (
  map test_eq_desugar_expression [
  ("t1", EArrow (EIdentifier (Ident "Nat"), EMatch (EIdentifier (Ident "x"),
  [CCase (PPair (PUnderscore, PIdentifier (Ident "y")), EUniverse)])), Pi
  (Underscore, Identifier "Nat", Application (Function [(PatternPair
  (PatternUnderscore, PatternIdentifier "y"), Universe)], Identifier "x")));
  ("t2", EDeclaration ([DSimpleType (Ident "Bool", [Constr (Ident "false",
  EIdentifier (Ident "Bool")); Constr (Ident "true", EIdentifier (Ident
  "Bool"))]); DLetRec (Ident "x", [], EUnitType, EUnit)], EUnit),
  LocalDeclaration ([Type ("Bool", [], Universe, [("false", Identifier "Bool");
  ("true", Identifier "Bool")]); LetRec ("x", UnitType, Unit) ], Unit));
  ("t3", ETimes (EUniverse, EUniverse), Sigma (Underscore, Universe, Universe));
  ("t4", ELambda ([BName (Ident "x"); BName (Ident "y")], EUnit), Lambda (Name
  "x", Lambda (Name "y", Unit)))
  ])

let test_eq_desugar_declaration (name, input, expected) =
  name >:: fun _ -> (assert_equal (desugar_declaration input) expected)

let test_desugar_declaration = "desugar_declaration" >::: (map
test_eq_desugar_declaration [
  ("t1", DType (Ident "Vec", [Param (BName (Ident "A"), EUniverse)], EArrow
  (EIdentifier (Ident "Nat"), EUniverse), [Constr (Ident "nil", EApplication
  (EApplication (EIdentifier (Ident "Vec"), EIdentifier (Ident "A")),
  EIdentifier (Ident "zero"))) ]), Type ("Vec", [(Name "A", Universe)], Pi
  (Underscore, Identifier "Nat", Universe), [ ("nil", Application (Application
  (Identifier "Vec", Identifier "A"), Identifier "zero")) ]));
  ("t2", DLet (Ident "f", [Param (BName (Ident "x"), EUniverse); Param (BName
  (Ident "y"), EUnitType); Param (BUnderscore, EIdentifier (Ident "A"))],
  EUniverse, EUnitType),Let ("f", Pi (Name "x", Universe, Pi (Name "y",
  UnitType, Pi (Underscore, Identifier "A", Universe))), Lambda (Name "x",
  Lambda (Name "y", Lambda (Underscore, UnitType)))))
  ])

let test_eq_resugar_expression (name, input, expected) =
  name >:: fun _ -> (assert_equal (resugar_expression input) expected)

let test_resugar_expression = "resugar_expression" >::: (
  map test_eq_resugar_expression [
  ("t1", Pi (Underscore, Identifier "Nat", Application (Function [(PatternPair
  (PatternUnderscore, PatternIdentifier "y"), Universe)], Identifier "x")),
  EArrow (EIdentifier (Ident "Nat"), EMatch (EIdentifier (Ident "x"), [CCase
  (PPair (PUnderscore, PIdentifier (Ident "y")), EUniverse)])));
  ("t2", LocalDeclaration ([Type ("Bool", [], Universe, [("false", Identifier
  "Bool"); ("true", Identifier "Bool")]); LetRec ("x", UnitType, Unit) ], Unit),
  EDeclaration ([DSimpleType (Ident "Bool", [Constr (Ident "false", EIdentifier
  (Ident "Bool")); Constr (Ident "true", EIdentifier (Ident "Bool"))]); DLetRec
  (Ident "x", [], EUnitType, EUnit)], EUnit));
  ("t3", Sigma (Underscore, Universe, Universe), ETimes (EUniverse, EUniverse));
  ("t4", Lambda (Name "x", Lambda (Name "y", Unit)), ELambda ([BName (Ident
  "x"); BName (Ident "y")], EUnit))
  ])

let test_eq_resugar_declaration (name, input, expected) =
  name >:: fun _ -> (assert_equal (resugar_declaration input) expected)

let test_resugar_declaration = "resugar_declaration" >::: (
  map test_eq_resugar_declaration [
  ("t1", Type ("Vec", [(Name "A", Universe)], Pi (Underscore, Identifier "Nat",
  Universe), [("nil", Application (Application (Identifier "Vec", Identifier
  "A"), Identifier "zero")) ]), DType (Ident "Vec", [Param (BName (Ident "A"),
  EUniverse)], EArrow (EIdentifier (Ident "Nat"), EUniverse), [Constr (Ident
  "nil", EApplication (EApplication (EIdentifier (Ident "Vec"), EIdentifier
  (Ident "A")), EIdentifier (Ident "zero"))) ]));
  ("t2", Let ("f", Pi (Underscore, Identifier "A", Pi (Name "x", Identifier "B",
  Pi (Name "y", Identifier "C", Pi (Underscore, Identifier "D", UnitType)))),
  Lambda (Underscore, Lambda (Name "x", Lambda (Name "y", Lambda (Name "z",
  Unit))))), DLet ( Ident "f", [Param (BUnderscore, EIdentifier (Ident "A"));
  Param (BName (Ident "x"), EIdentifier (Ident "B")); Param (BName (Ident "y"),
  EIdentifier (Ident "C"))], EArrow (EIdentifier (Ident "D"), EUnitType),
  ELambda ([BName (Ident "z")], EUnit)))
  ])

let test_syntax = "syntax" >::: [test_parser
                               ; test_desugar_expression
                               ; test_desugar_declaration
                               ; test_resugar_expression
                               ; test_resugar_declaration]
