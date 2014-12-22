open OUnit2
open QuickCheck

open Abstract
open Equality
open Value
open Testing

let test_readback (name, input, expected) =
  name >:: fun _ -> (assert_equal (readback 0 input) expected)

let test_lambdas = "lambdas" >::: (List.map test_readback [
  ("lambda", VLambda (Underscore, Universe, Environment.empty), NLambda (0,
  NUniverse));
  ("lambda2", VLambda (Underscore, Lambda (Name "x", Index 0),
  Environment.empty), NLambda (0, NLambda (1, NNeutral (NVar 1))));
  ("lambda3", VLambda (Name "x", Lambda (Underscore, Index 0),
  Environment.empty), NLambda (0, NLambda (1, NNeutral (NVar 0))));
  ("lambda_app", VLambda (Name "x", Application (Lambda (Name "y", Index 0),
  Index 0), Environment.empty), NLambda (0, NNeutral (NVar 0)))
])

let test_functions = "functions" >::: (List.map test_readback [
  ("empty", VFunction ([], Environment.empty), NFunction ([], empty_envt));
  ("appl", VNeutral (VFunctionApplication ([], Environment.empty, VVar 0)),
  NNeutral (NFunctionApplication ([], empty_envt, NVar 0)))
])

let test_readback_other = "readback_other" >::: (List.map test_readback [
  ("universe", VUniverse, NUniverse);
  ("unit", VUnit, NUnit);
  ("unit_type", VUnitType, NUnitType);
  ("pair", VPair (VUnit, VUniverse), NPair (NUnit, NUniverse))
])

let test_let_equality = quickCheck_test "let_equality"
  (testable_fun arbitrary_expression show_expression testable_bool)
  (fun e -> 
    let e2 = LocalDeclaration ([Let ("x", Universe, e)], Index 0) in
    try are_equal Environment.empty e e2
    with
    | Eval.Cannot_evaluate _ -> true
    | Eval.Pattern_match -> true)

let test_equality = "equality" >::: [test_lambdas
                                   ; test_functions
                                   ; test_readback_other
                                   ; test_let_equality]
