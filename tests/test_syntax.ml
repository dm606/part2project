open Lexing
open List
open OUnit2
open QuickCheck

open AbsConcrete
open Abstract
open LexConcrete
open ParConcrete
open Parser
open PrintConcrete
open Testing

let test_eq_parser_repl (name, input, expected) =
  name >:: fun _ -> (assert_equal (parse_repl (from_string input)) expected)

let test_parser_repl = "parser_repl" >::: (map test_eq_parser_repl [
  ("t1", "U;;", [Exp EUniverse]);
  ("t2", "let x : U = U;;", [Decl [DLet (Ident "x", [], EUniverse,
  EUniverse)]]);
  ("t3", "let f : Nat -> Nat * Bool -> Nat = fun x _ -> succ x;;", [Decl [DLet
  (Ident "f", [], EArrow (EIdentifier (Ident "Nat"), EArrow (ETimes (EIdentifier
  (Ident "Nat"), EIdentifier (Ident "Bool")), EIdentifier (Ident "Nat"))),
  ELambda ([BName (Ident "x"); BUnderscore], EApplication (EIdentifier (Ident
  "succ"), EIdentifier (Ident "x"))))]]);
  ("t4", "fun A -> A -> Empty;;", [Exp (ELambda ([BName (Ident "A")], EArrow
  (EIdentifier (Ident "A"), EIdentifier (Ident "Empty"))))]);
  ("t5", "function;;", [Exp (EFunction [])]);
  ("t6", "let rec f : Nat = zero and type Nat = zero : Nat | succ : (_:Nat) ->
  Nat;;", [Decl ([DLetRec (Ident "f", [], EIdentifier (Ident "Nat"),
  EIdentifier (Ident "zero")); DSimpleType (Ident "Nat", [Constr (Ident
  "zero", EIdentifier (Ident "Nat")); Constr (Ident "succ", EPi (BUnderscore,
  EIdentifier (Ident "Nat"), EIdentifier (Ident "Nat")))])])]);
  ("t7", "let f : U = U in type Empty = in Empty;;", [Exp  (EDeclaration ([DLet
  (Ident "f", [], EUniverse, EUniverse)], EDeclaration ([DSimpleType (Ident
  "Empty", [])], EIdentifier (Ident "Empty"))))]);
  ("t8", "type Id (A : U) (a : A) : A -> U = | refl : Id A a a;;", [Decl ([DType
  (Ident "Id", [Param (BName (Ident "A"), EUniverse); Param (BName (Ident "a"),
  EIdentifier (Ident "A"))], EArrow (EIdentifier (Ident "A"), EUniverse),
  [Constr (Ident "refl", EApplication (EApplication (EApplication (EIdentifier
  (Ident "Id"), EIdentifier (Ident "A")), EIdentifier (Ident "a")), EIdentifier
  (Ident "a")))])])]);
  ("t9", "a (b c) d;;", [Exp (EApplication (EApplication (EIdentifier (Ident
  "a"), EApplication (EIdentifier (Ident "b"), EIdentifier (Ident "c"))),
  EIdentifier (Ident "d")))]);
  ("t10", "(x, y, z).1;;", [Exp (EProj1 (EPair (EIdentifier (Ident "x"), EPair
  (EIdentifier (Ident "y"), EIdentifier (Ident "z")))))]);
  ("t9", "let rec f (x : A) (_ : B) : U = fun z -> U;;", [Decl ([DLetRec (Ident
  "f", [Param (BName (Ident "x"), EIdentifier (Ident "A")); Param (BUnderscore,
  EIdentifier (Ident "B"))], EUniverse, ELambda ([BName (Ident "z")],
  EUniverse))])])
  ])

let test_eq_parser_file (name, input, expected) =
  name >:: fun _ -> (assert_equal (parse_file (from_string input)) expected)

let test_parser_file = "parser_file" >::: (map test_eq_parser_file [
  ("t1", "U", [Exp EUniverse]);
  ("t2", "U;;U", [Exp EUniverse; Exp EUniverse]);
  ("t3", "let x : U = U let y : U = U", [Decl [DLet (Ident "x", [], EUniverse,
  EUniverse)]; Decl [DLet (Ident "y", [], EUniverse, EUniverse)]]);
  ("t4", "let x : U = U;; let y : U = U", [Decl [DLet (Ident "x", [], EUniverse,
  EUniverse)]; Decl [DLet (Ident "y", [], EUniverse, EUniverse)]]);
  ("t5", "#use \"f\" let x : U = U", [Comm (CommandString (Ident "use", "f"));
  Decl [DLet (Ident "x", [], EUniverse, EUniverse)]]) 
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

let test_eq_lexfun_repl (name, input, expected) =
  name >:: fun _ ->
    let t = lexfun_repl token in
    let lexbuf = from_string input in
    assert_bool "Tokens did not match"
      (List.for_all (fun tok -> (t lexbuf) = tok) expected)

let test_lexfun_repl = "lexfun_repl" >::: (map test_eq_lexfun_repl [
  ("t1", ";;", [TOK_SEMISEMI ";;"; TOK_EOF]);
  ("t2", ";;;;", [TOK_SEMISEMI ";;"; TOK_EOF])
])

let test_resugar_desugar =
  quickCheck_test "resugar_desugar"
    (testable_fun arbitrary_expression show_expression testable_bool)
    (fun e -> desugar_expression (resugar_expression e) = e)

let test_print_parse =
  quickCheck_test "print_parse"
    (testable_fun arbitrary_expression show_expression testable_bool)
    (fun e ->
      let s = printTree prtReplStructure
        (ReplExpression (resugar_expression e, SEMISEMI ";;")) in
      match parse_file (from_string s) with
      | [Exp r] -> desugar_expression r = e
      | _ -> false)

let test_syntax = "syntax" >::: [test_parser_repl
                               ; test_parser_file
                               ; test_desugar_expression
                               ; test_desugar_declaration
                               ; test_resugar_expression
                               ; test_resugar_declaration
                               ; test_lexfun_repl
                               ; test_resugar_desugar
                               ; test_print_parse]
