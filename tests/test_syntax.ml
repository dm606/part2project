open Lexing
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

let test_parser_repl = "parser_repl" >::: (List.map test_eq_parser_repl [
  ("t1", "Type;;", [Exp (EUnindexedUniverse)]);
  ("t2", "let x : Type 1 = Type;;", [Decl [DLet (Ident "x", [], EUniverse 1,
  EUnindexedUniverse)]]);
  ("t3", "let f : Nat -> Nat * Bool -> Nat = fun x _ -> succ x;;", [Decl [DLet
  (Ident "f", [], EArrow (EIdentifier (Ident "Nat"), EArrow (ETimes (EIdentifier
  (Ident "Nat"), EIdentifier (Ident "Bool")), EIdentifier (Ident "Nat"))),
  ELambda ([LBinder (BName (Ident "x")); LBinder BUnderscore], EApplication (EIdentifier (Ident
  "succ"), EIdentifier (Ident "x"))))]]);
  ("t4", "fun A -> A -> Empty;;", [Exp (ELambda ([LBinder (BName (Ident
  "A"))], EArrow
  (EIdentifier (Ident "A"), EIdentifier (Ident "Empty"))))]);
  ("t5", "function;;", [Exp (EFunction [])]);
  ("t6", "let rec f : Nat = zero and type Nat = zero : Nat | succ : (_:Nat) ->
  Nat;;", [Decl ([DLetRec (Ident "f", [], EIdentifier (Ident "Nat"),
  EIdentifier (Ident "zero")); DSimpleType (Ident "Nat", [Constr (Ident
  "zero", EIdentifier (Ident "Nat")); Constr (Ident "succ", EPi (BUnderscore,
  EIdentifier (Ident "Nat"), EIdentifier (Ident "Nat")))])])]);
  ("t7", "let f : Type 1 = Type in type Empty = in Empty;;", [Exp  (EDeclaration
  ([DLet (Ident "f", [], EUniverse 1, EUnindexedUniverse)], EDeclaration
  ([DSimpleType (Ident "Empty", [])], EIdentifier (Ident "Empty"))))]);
  ("t8", "type Id (A : Type) (a : A) : A -> Type = | refl : Id A a a;;", [Decl
  ([DType (Ident "Id", [Param (Ident "A", EUnindexedUniverse); Param
  (Ident "a", EIdentifier (Ident "A"))], EArrow (EIdentifier (Ident
  "A"), EUnindexedUniverse), [Constr (Ident "refl", EApplication (EApplication
  (EApplication (EIdentifier (Ident "Id"), EIdentifier (Ident "A")), EIdentifier
  (Ident "a")), EIdentifier (Ident "a")))])])]);
  ("t9", "a (b c) d;;", [Exp (EApplication (EApplication (EIdentifier (Ident
  "a"), EApplication (EIdentifier (Ident "b"), EIdentifier (Ident "c"))),
  EIdentifier (Ident "d")))]);
  ("t10", "(x, y, z).1;;", [Exp (EProj1 (EPair (EIdentifier (Ident "x"), EPair
  (EIdentifier (Ident "y"), EIdentifier (Ident "z")))))]);
  ])

let test_eq_parser_file (name, input, expected) =
  name >:: fun _ -> (assert_equal (parse_file (from_string input)) expected)

let test_parser_file = "parser_file" >::: (List.map test_eq_parser_file [
  ("t1", "Type", [Exp (EUnindexedUniverse)]);
  ("t2", "Type 0;;Type 0", [Exp (EUniverse 0); Exp (EUniverse 0)]);
  ("t3", "let x : Type = Type let y : Type = Type", [Decl [DLet (Ident "x", [],
  EUnindexedUniverse, EUnindexedUniverse)]; Decl [DLet (Ident "y", [],
  EUnindexedUniverse, EUnindexedUniverse)]]);
  ("t4", "let x : Type 0 = Type 0;; let y : Type 0 = Type 0", [Decl [DLet (Ident
  "x", [], EUniverse 0, EUniverse 0)]; Decl [DLet (Ident "y", [], EUniverse 0,
  EUniverse 0)]]);
  ("t5", "#use \"f\" let x : Type 0 = Type 0", [Comm (CommandString (Ident
  "use", "f")); Decl [DLet (Ident "x", [], EUniverse 0, EUniverse 0)]]) 
  ])

let test_eq_desugar_expression (name, env, input, expected) =
  name >:: fun _ -> (assert_equal (desugar_expression env input) expected)

let test_desugar_expression = "desugar_expression" >::: (
  List.map test_eq_desugar_expression [
    ("t1", mk_env (["x"; "Nat"], []), EArrow (EIdentifier (Ident "Nat"), EMatch
    (EIdentifier (Ident "x"), [CCase (PPair (PUnderscore, PIdentifier (Ident
    "y")), EUnindexedUniverse)])), Pi (Underscore, Index 1, Application
    (Function [(PatternPair (PatternUnderscore, PatternBinder "y"), Universe
    0)], Index 0)));
    ("t2", mk_env ([], []), EDeclaration ([DSimpleType (Ident "Bool", [Constr
    (Ident "false", EIdentifier (Ident "Bool")); Constr (Ident "true",
    EIdentifier (Ident "Bool"))]); DLetRec (Ident "x", [], EUnitType, EUnit)],
    EUnit), LocalDeclaration ([Type ("Bool", [], Universe 0, [("false",
    Constructor "Bool"); ("true", Constructor "Bool")]); LetRec ("x", UnitType,
    Unit)], Unit));
    ("t3", mk_env ([], []), ETimes (EUniverse 0, EUniverse 0), Sigma
    (Underscore, Universe 0, Universe 0));
    ("t4", mk_env ([], []), ELambda ([LBinder (BName (Ident "x"));
    LBinder (BName (Ident "y"))],
    EUnit), Lambda (Name "x", Lambda (Name "y", Unit)))
  ])

let test_eq_desugar_declarations (name, env, input, expected) =
  name >:: fun _ -> (assert_equal (desugar_declarations env [input]) [expected])

let test_desugar_declarations = "desugar_declarations" >::: (
  List.map test_eq_desugar_declarations [
    ("t1", mk_env ([], ["Nat", "Type"; "zero", "Nat"]), DType (Ident "Vec",
    [Param (Ident "A", EUnindexedUniverse)], EArrow (EIdentifier (Ident
    "Nat"), EUniverse 0), [Constr (Ident "nil", EApplication (EApplication
    (EIdentifier (Ident "Vec"), EIdentifier (Ident "A")), EIdentifier (Ident
    "zero")))]), Type ("Vec", [Parameter ("A", Universe 0)], Pi (Underscore,
    Constructor "Nat", Universe 0), [("nil", Application (Application
    (Constructor "Vec", Index 0), Constructor "zero"))]));
    ("t2", mk_env (["A"], []), DLet (Ident "f", [Param (Ident "x",
    EUniverse 0); Param (Ident "y", EUnitType); Param (Ident "z",
    EIdentifier (Ident "A"))], EUniverse 0, EUnitType), Let ("f", Pi (Name "x",
    Universe 0, Pi (Name "y", UnitType, Pi (Name "z", Index 2, Universe 0))),
    Lambda (Name "x", Lambda (Name "y", Lambda (Name "z", UnitType)))))
  ])

let test_eq_resugar_expression (name, env, input, expected) =
  name >:: fun _ -> (assert_equal (resugar_expression env input) expected)

let test_resugar_expression = "resugar_expression" >::: (
  List.map test_eq_resugar_expression [
    ("t1", mk_env (["x"; "Nat"], []), Pi (Underscore, Index 1, Application
    (Function [(PatternPair (PatternUnderscore, PatternBinder "y"), Universe
    0)], Index 0)), EArrow (EIdentifier (Ident "Nat"), EMatch (EIdentifier
    (Ident "x"), [CCase (PPair (PUnderscore, PIdentifier (Ident "y")),
    EUnindexedUniverse)])));
    ("t2", mk_env ([], []), LocalDeclaration ([Type ("Bool", [], Universe 0,
    [("false", Constructor "Bool"); ("true", Constructor "Bool")]); LetRec ("x",
    UnitType, Unit) ], Unit), EDeclaration ([DSimpleType (Ident "Bool", [Constr
    (Ident "false", EIdentifier (Ident "Bool")); Constr (Ident "true",
    EIdentifier (Ident "Bool"))]); DLetRec (Ident "x", [], EUnitType, EUnit)],
    EUnit));
    ("t3", mk_env ([], []), Sigma (Underscore, Universe 1, Universe 2), ETimes
    (EUniverse 1, EUniverse 2));
    ("t4", mk_env ([], []), Lambda (Name "x", Lambda (Name "y", Unit)), ELambda
    ([LBinder (BName (Ident "x")); LBinder (BName (Ident "y"))], EUnit))
  ])

let test_eq_resugar_declarations (name, env, input, expected) =
  name >:: fun _ -> (assert_equal (resugar_declarations env [input]) [expected])

let test_resugar_declarations = "resugar_declarations" >::: (
  List.map test_eq_resugar_declarations [
    ("t1", mk_env ([], []), Type ("Vec", [Parameter ("A", Universe 0)], Pi
    (Underscore, Constructor "Nat", Universe 0), [("nil", Application
    (Application (Constructor "Vec", Index 0), Constructor "zero")) ]), DType
    (Ident "Vec", [Param (Ident "A", EUnindexedUniverse)], EArrow
    (EIdentifier (Ident "Nat"), EUnindexedUniverse), [Constr (Ident "nil",
    EApplication (EApplication (EIdentifier (Ident "Vec"), EIdentifier (Ident
    "A")), EIdentifier (Ident "zero")))]))
  ])

let test_eq_lexfun_repl (name, input, expected) =
  name >:: fun _ ->
    let t = lexfun_repl token in
    let lexbuf = from_string input in
    assert_bool "Tokens did not match"
      (List.for_all (fun tok -> (t lexbuf) = tok) expected)

let test_lexfun_repl = "lexfun_repl" >::: (List.map test_eq_lexfun_repl [
  ("t1", ";;", [TOK_SEMISEMI ";;"; TOK_EOF]);
  ("t2", ";;;;", [TOK_SEMISEMI ";;"; TOK_EOF])
])

let test_resugar_desugar =
  quickCheck_test "resugar_desugar"
    (testable_fun arbitrary_expression show_expression testable_bool)
    (fun e -> desugar_expression (mk_env ([], !all_identifiers))
      (resugar_expression (mk_env ([], !all_identifiers)) e) = e)

let test_print_parse =
  quickCheck_test "print_parse"
    (testable_fun arbitrary_expression show_expression testable_bool)
    (fun e ->
      let s = printTree prtReplStructure
        (ReplExpression (resugar_expression (mk_env ([], !all_identifiers)) e
                       , SEMISEMI ";;")) in
      match parse_file (from_string s) with
      | [Exp r] -> desugar_expression (mk_env ([], !all_identifiers)) r = e
      | _ -> false)

let test_syntax = "syntax" >::: [test_parser_repl
                               ; test_parser_file
                               ; test_desugar_expression
                               ; test_desugar_declarations
                               ; test_resugar_expression
                               ; test_resugar_declarations
                               ; test_lexfun_repl
                               ; test_resugar_desugar
                               ; test_print_parse]
