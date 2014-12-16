open OUnit2;;

let all_tests = "all_tests" >::: [Test_syntax.test_syntax
                                ; Test_eval.test_eval
                                ; Test_equality.test_equality]

let _ = run_test_tt_main all_tests
