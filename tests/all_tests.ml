open OUnit2;;

let all_tests = "all_tests" >::: [Test_syntax.test_syntax
                                ; Test_eval.test_eval
                                ; Test_equality.test_equality
                                ; Test_checker.test_checker]

let () = run_test_tt_main all_tests
