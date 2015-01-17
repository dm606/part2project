open OUnit2

open Abstract
open Eval
open Value

let test_eval (name, env, input, expected) =
  name >:: fun _ -> (assert_equal (eval env input) expected)

let test_tuples = "tuples" >::: (List.map test_eval [
  ("tuple", Environment.empty, Pair (Pair (Universe 0, Unit), Pair (UnitType,
  Universe 0)), VPair (VPair (VUniverse 0, VUnit), VPair (VUnitType, VUniverse
  0)));
  ("proj1", Environment.empty, Proj1 (Pair (Universe 0, Unit)), VUniverse 0);
  ("proj2", Environment.empty, Proj2 (Pair (Universe 0, Unit)), VUnit);
  ("nested", Environment.empty, Proj1 (Proj2 (Pair (Unit, Pair (Proj1 (Pair
  (UnitType, Universe 0)), UnitType)))), VUnitType)
]) @ [
  ("not_a_pair" >:: fun _ -> (
    assert_raises
      (Cannot_evaluate
        "Attempted to project an element out of a value which is not a pair")
      (fun () -> eval Environment.empty (Proj1 (Universe 0)))))
]

let test_lambdas = "lambdas" >::: (List.map test_eval [
  ("simple_lambda", Environment.empty, Lambda (Underscore, Proj1 (Universe 0)),
  VLambda (Underscore, Proj1 (Universe 0), Environment.empty));
  ("simple_application", Environment.empty, Application (Lambda (Name "x", Index
  0), Unit), VUnit);
  ("higher_order1", Environment.empty, Application (Lambda (Underscore, Lambda
  (Name "x", Unit)), Unit), VLambda (Name "x", Unit, Environment.empty));
  ("higher_order2", Environment.empty, Application (Lambda (Name "x", Index 0),
  Lambda (Name "y", Unit)), VLambda (Name "y", Unit, Environment.empty))
])

let test_patterns = "patterns" >::: (List.map test_eval [
  ("catch_all1", Environment.empty, Application (Function [PatternUnderscore,
  Unit], Unit), VUnit);
  ("catch_all2", Environment.empty, Application (Function [PatternBinder "x",
  Index 0], Unit), VUnit);
  ("bool1", Environment.empty, Application (Function [PatternApplication
  ("true", []), Unit; PatternApplication ("false", []), UnitType], Constructor
  "true"), VUnit);
  ("bool2", Environment.empty, Application (Function [PatternApplication
  ("true", []), Unit; PatternApplication ("false", []), UnitType], Constructor
  "false"), VUnitType);
  (* (function a _ (_, b x) y _ -> (x, y)) (a U (U, b ()) Unit U) evaluates to
   * (), Unit *)
  ("binders", Environment.empty, Application (Function [PatternApplication ("a",
  [PatternUnderscore; PatternPair (PatternUnderscore, PatternApplication ("b",
  [PatternBinder "x"])); PatternBinder "y"; PatternUnderscore]), Pair (Index 1,
  Index 0)], Application (Application (Application (Application (Constructor
  "a", Universe 0), Pair (Universe 0, Application (Constructor "b", Unit))),
  UnitType), Universe 0)), VPair (VUnit, VUnitType))
]) @ [
  ("no_match" >:: fun _ -> (
    assert_raises
      Pattern_match
      (fun () -> eval Environment.empty (Application (Function [
          PatternApplication ("a", []), Unit
        ; PatternApplication ("b", []), Unit], Constructor "c")))))]

let test_eval_other = "eval_other" >::: (List.map test_eval [
  ("declaration", Environment.empty, LocalDeclaration ([Let ("x", Universe 0,
  UnitType)], Index 0), VUnitType);
  ("mutual_declarations", Environment.empty, LocalDeclaration ([Let ("x",
  Universe 0, Application (Index 0, Constructor "true")); LetRec ("y", Universe
  0, Function [PatternApplication ("true", []), Application (Index 0,
  Constructor "false"); PatternApplication ("false", []), UnitType])], Index 1),
  VUnitType)
])

let test_eval = "eval" >::: [test_tuples
                           ; test_lambdas
                           ; test_patterns
                           ; test_eval_other]
