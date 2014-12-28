open OUnit2
open QuickCheck

open Abstract
open Checker
open Testing
open Value

let test_infer_type_success (name, env, context, input, expected) =
  name >:: fun _ ->
    let result = infer_type env context input in
    assert_bool "Incorrect result produced by infer_type"
      ((succeeded result) && (expected = get_type result))

let test_infer_type_fail (name, env, context, input) =
  name >:: fun _ ->
    let result = infer_type env context input in
    assert_bool "Expected infer_type to fail" (not (succeeded result))

let test_infer_type = "infer_type" >::: (List.map test_infer_type_success [
  ("universe", Environment.empty, Context.empty, Universe, VUniverse);
  ("unit_type", Environment.empty, Context.empty, UnitType, VUniverse);
  ("unit", Environment.empty, Context.empty, Unit, VUnitType);
  ("pair", Environment.empty, Context.empty, Pair (Unit, UnitType), VSigma
  (Underscore, VUnitType, Universe, Environment.empty));
  ("constructor" , Environment.empty , Context.add_constructor
  (Context.add_constructor Context.empty "Bool" "U" VUniverse) "true" "Bool"
  (VConstruct ("Bool", [])) , Constructor "true", VConstruct ("Bool", []));
  ("declarations", Environment.empty, Context.empty, LocalDeclaration ([Let
  ("x", UnitType, Unit)], Index 0), VUnitType);
  ("mutual_declarations", Environment.empty, Context.empty, LocalDeclaration
  ([Let ("x", UnitType, Index 0); LetRec ("y", UnitType, Unit)], Index 1),
  VUnitType);
  ("application", Environment.add Environment.empty (VLambda (Name "x", Index 0,
  Environment.empty)), Context.add_binder Context.empty "f" (VPi (Underscore,
  VUnitType, UnitType, Environment.empty)), Application (Index 0, Unit),
  VUnitType);
  ("projection", Environment.empty, Context.empty, Proj1 (Pair (Universe,
  Universe)), VUniverse)
]) @ (List.map test_infer_type_fail [
  ("lambda_cannot_infer", Environment.empty, Context.empty, Lambda (Name "x",
  Index 0));
  ("application_cannot_infer", Environment.empty, Context.empty,
  Application (Lambda (Name "x", Unit), Unit));
  ("application_invalid", Environment.add Environment.empty (VLambda (Name "x",
  Index 0, Environment.empty)), Context.add_binder Context.empty "f" (VPi
  (Underscore, VUnitType, UnitType, Environment.empty)), Application (Index 0,
  UnitType));
  ("application_invalid2", Environment.empty, Context.empty, Application (Unit,
  Unit));
  ("projection_invalid", Environment.empty, Context.empty, Proj1 Unit);
  ("pi_invalid", Environment.empty, Context.empty, Pi (Name "A", Universe, Pi
  (Name "a", Index 0, Index 0)))
])

let test_check_success (name, env, context, expression, typ) =
  name >:: fun _ ->
    let result = check_type env context expression typ in
    assert_bool "Type checker failed" (succeeded result)

let test_check_fail (name, env, context, expression, typ) =
  name >:: fun _ -> 
    let result = check_type env context expression typ in
    assert_bool "Type checker expected to fail" (not (succeeded result))

let test_check = "check" >::: (List.map test_check_success [
  ("universe", Environment.empty, Context.empty, Universe, VUniverse);
  ("unit_type", Environment.empty, Context.empty, UnitType, VUniverse);
  ("unit", Environment.empty, Context.empty, Unit, VUnitType);
  ("pair", Environment.empty, Context.empty, Pair (Unit, UnitType), VSigma
  (Underscore, VUnitType, Universe, Environment.empty));
  ("constructor" , Environment.empty , Context.add_constructor
  (Context.add_constructor Context.empty "Bool" "U" VUniverse) "true" "Bool"
  (VConstruct ("Bool", [])) , Constructor "true", VConstruct ("Bool", []));
  ("declarations", Environment.empty, Context.empty, LocalDeclaration ([Let
  ("x", UnitType, Unit)], Index 0), VUnitType);
  ("mutual_declarations", Environment.empty, Context.empty, LocalDeclaration
  ([Let ("x", UnitType, Index 0); LetRec ("y", UnitType, Unit)], Index 1),
  VUnitType);
  ("application", Environment.add Environment.empty (VLambda (Name "x", Index 0,
  Environment.empty)), Context.add_binder Context.empty "f" (VPi (Underscore,
  VUnitType, UnitType, Environment.empty)), Application (Index 0, Unit),
  VUnitType);
  ("projection", Environment.empty, Context.empty, Proj1 (Pair (Universe,
  Universe)), VUniverse);
  ("lambda", Environment.empty, Context.empty, Lambda (Name "x", Index 0), VPi
  (Underscore, VUnitType, UnitType, Environment.empty));
  ("pair2", Environment.empty, Context.empty, Pair (UnitType, Unit), VSigma
  (Name "A", VUniverse, Index 0, Environment.empty))
]) @ (List.map test_check_fail [
  ("application", Environment.add Environment.empty (VLambda (Name "x", Index 0,
  Environment.empty)), Context.add_binder Context.empty "f" (VPi (Underscore,
  VUnitType, UnitType, Environment.empty)), Application (Index 0, UnitType),
  VUnit);
  ("application2", Environment.empty, Context.empty, Application (Unit, Unit),
  VUnit);
  ("projection", Environment.empty, Context.empty, Proj1 (Pair (Universe,
  Universe)), VUnitType);
  ("pi", Environment.empty, Context.empty, Pi (Name "A", Universe, Pi (Name "a",
  Index 0, Index 0)), VUniverse)
])

let test_infer_check =
  quickCheck_test "infer_check"
    (testable_fun arbitrary_expression show_expression testable_bool)
    (fun e ->
      let infer_result = infer_type Environment.empty Context.empty e in
      if succeeded infer_result
      then succeeded (check_type Environment.empty Context.empty e
             (get_type infer_result))
      else true)

let test_checker = "type_checker" >::: [test_infer_type;
                                        test_check;
                                        test_infer_check]
