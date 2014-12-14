open OUnit2

open Abstract
open Eval
open Value

let test_eval (name, env, input, expected) =
  name >:: fun _ -> (assert_equal (eval env input) expected)

let test_tuples = "tuples" >::: (List.map test_eval [
  ("tuple", Environment.empty, Pair (Pair (Universe, Unit), Pair (UnitType,
  Universe)), VPair (VPair (VUniverse, VUnit), VPair (VUnitType, VUniverse)));
  ("proj1", Environment.empty, Proj1 (Pair (Universe, Unit)), VUniverse);
  ("proj2", Environment.empty, Proj2 (Pair (Universe, Unit)), VUnit);
  ("nested", Environment.empty, Proj1 (Proj2 (Pair (Unit, Pair (Proj1 (Pair
  (UnitType, Universe)), UnitType)))), VUnitType)
]) @ [
  ("not_a_pair" >:: fun _ -> (
    assert_raises
      (Cannot_evaluate
        "Attempted to project an element out of a value which is not a pair")
      (fun () -> eval Environment.empty (Proj1 Universe))))
]

let test_lambdas = "lambdas" >::: (List.map test_eval [

])

let test_patterns = "patterns" >::: (List.map test_eval [

])

let test_eval_other = "eval_other" >::: (List.map test_eval [

])

let test_eval = "eval" >::: [test_tuples
                           ; test_lambdas
                           ; test_patterns
                           ; test_eval_other]
