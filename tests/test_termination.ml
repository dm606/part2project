open OUnit2

open Abstract
open Termination

let test_termination (name, env, input, expected) =
  name >:: fun _ ->
    let result = check_termination env input in
    assert_bool "Incorrect result produced by check_termination"
      (result = expected)

let test_termination = "termination" >::: (List.map test_termination [
  ("single_let", Environment.empty, [Let ("x", UnitType, Unit)], None);
  ("simple_recursion_non_terminating", Environment.empty, [LetRec ("x",
  UnitType, Index 0)], Some "x");
  ("simple_recursion_terminating", Environment.empty, [LetRec ("x", UnitType,
  Function [PatternApplication ("zero", []), Unit; PatternApplication ("succ",
  [false, PatternBinder "x"]), Application (Index 1, Index 0)])], None);
  ("cannot_show_termination", Environment.empty, [LetRec ("x", UnitType,
  Function [PatternApplication ("zero", []), Unit; PatternApplication ("succ",
  [false, PatternBinder "x"]), Application (Index 1, Constructor "zero")])],
  Some "x");
  ("mutual_recursion_terminating", Environment.empty, [LetRec ("x", UnitType,
  Function [PatternApplication ("zero", []), Unit; PatternApplication ("succ",
  [false, PatternBinder "x"]), Application (Index 2, Index 0)]); LetRec ("y",
  UnitType, Lambda (Name "x", Application (Index 2, Index 0)))], None);
  ("mutual_recursion_non_terminating", Environment.empty, [LetRec ("x",
  UnitType, Function [PatternApplication ("zero", []), Unit; PatternApplication
  ("succ", [false, PatternBinder "x"]), Application (Index 2, Index 0)]); LetRec
  ("y", UnitType, Lambda (Name "x", Application (Index 2, Application
  (Constructor "succ", Index 0))))], Some "x")
])
