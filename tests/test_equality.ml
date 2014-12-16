open OUnit2
open QuickCheck

open Abstract
open Equality
open Value
open Testing

let test_readback (name, input, expected) =
  name >:: fun _ -> (assert_equal (readback 0 input) expected)

let test_lambdas = "lambdas" >::: (List.map test_readback [

        ("lambda", VLambda (Underscore, Universe, Environment.empty), NLambda (0, NUniverse))

])

let test_functions = "functions" >::: (List.map test_readback [

])

let test_readback_other = "readback_other" >::: (List.map test_readback [

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
