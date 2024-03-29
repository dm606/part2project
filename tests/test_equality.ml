open OUnit2
open QuickCheck

open Abstract
open Equality
open Value
open Testing

let test_readback (name, input, expected) =
  name >:: fun _ -> (assert_equal (readback no_constraints 0 input) expected)

let test_lambdas = "lambdas" >::: (List.map test_readback [
  ("lambda", VLambda (Underscore, Universe 0, Environment.empty), NLambda ("_", 0,
  NUniverse 0));
  ("lambda2", VLambda (Underscore, Lambda (Name "x", Index 0),
  Environment.empty), NLambda ("_", 0, NLambda ("x", 1, NNeutral (NVar ("x", 1)))));
  ("lambda3", VLambda (Name "x", Lambda (Underscore, Index 0),
  Environment.empty), NLambda ("x", 0, NLambda ("_", 1, NNeutral (NVar ("x", 0)))));
  ("lambda_app", VLambda (Name "x", Application (Lambda (Name "y", Index 0),
  Index 0), Environment.empty), NLambda ("x", 0, NNeutral (NVar ("x", 0))))
])

let test_functions = "functions" >::: (List.map test_readback [
  ("empty", VFunction ([], Environment.empty), NFunction ([], empty_envt));
  ("appl", VNeutral (VFunctionApplication ([], Environment.empty, (VNeutral
  (VVar ("",0))))),
  NNeutral (NFunctionApplication ([], empty_envt, NNeutral (NVar ("", 0)))))
])

let test_readback_other = "readback_other" >::: (List.map test_readback [
  ("universe", VUniverse 0, NUniverse 0);
  ("unit", VUnit, NUnit);
  ("unit_type", VUnitType, NUnitType);
  ("pair", VPair (VUnit, VUniverse 0), NPair (NUnit, NUniverse 0))
])

let test_let_equality = quickCheck_test "let_equality"
  (testable_fun arbitrary_expression show_expression testable_bool)
  (fun e -> 
    let e2 = LocalDeclaration ([Let ("x", Universe 0, e)], Index 0) in
    try always_satisfied (test_expression_equality Environment.empty e e2)
    with
    | Eval.Cannot_evaluate _ -> true
    | Eval.Pattern_match -> true)

let test_equality = "equality" >::: [test_lambdas
                                   ; test_functions
                                   ; test_readback_other
                                   ; test_let_equality]
