open OUnit2
open Printf
open QuickCheck
open QuickCheck_gen
open Bytes

open Abstract

let size_factor = 3

let quickCheck_config = {
  quick with
    maxTest = 130
}

let quickCheck_test name testable test = name >:: fun _ ->
  match check testable quickCheck_config test with
  | Success -> ()
  | Failure i -> assert_failure ("quickcheck test failure " ^ (string_of_int i))
  | Exhausted i ->
      assert_failure ("quicktest test exhausted " ^ (string_of_int i))

let arbitrary_nonempty_list f =
  f >>= (fun a -> (arbitrary_list f) >>= (fun l -> ret_gen (a::l)))

let all_identifiers = ref []

let arbitrary_binder_name =
  let n = ref 0 in
  Gen (fun _ ->
    let name = "b" ^ (string_of_int !n) in
    n := !n + 1; name)

let arbitrary_identifier =
  let n = ref 0 in
  Gen (fun _ ->
    let name = "a" ^ (string_of_int !n) in
    all_identifiers := (name, "") :: !all_identifiers;
    n := !n + 1; name)

let arbitrary_binder =
  oneof [ret_gen Underscore; arbitrary_binder_name
                         >>= (fun s -> ret_gen (Name s))]

let arbitrary_pattern =
  let rec f = function
    | 0 -> 
        oneof [
          ret_gen PatternUnderscore;
          arbitrary_binder_name >>= (fun s -> ret_gen (PatternBinder s))
        ]
    | n -> 
        let g = f (n / size_factor) in
        oneof [
          g >>= (fun p1 -> (g >>= (fun p2 -> ret_gen (PatternPair (p1, p2)))));
          arbitrary_identifier >>= (fun s -> ((arbitrary_nonempty_list g)
            >>= (fun l -> ret_gen (PatternApplication (s, l)))));
          arbitrary_binder_name >>= (fun s -> ret_gen (PatternBinder s));
          ret_gen PatternUnderscore
        ] in
  sized f

(* HACK to avoid let rec restrictions *)
let arb_exp = ref (ret_gen Unit)

let arbitrary_declaration =
  let f n = 
    let exp = resize (n / size_factor) !arb_exp in
    oneof [
      arbitrary_identifier >>= (fun s -> (exp
        >>= (fun e1 -> (exp >>= (fun e2 -> ret_gen (Let (s, e1, e2)))))));
      arbitrary_identifier >>= (fun s -> (exp
        >>= (fun e1 -> (exp >>= (fun e2 -> ret_gen (LetRec (s, e1, e2)))))));
      arbitrary_identifier
        >>= (fun s -> ((arbitrary_list (arbitrary_pair arbitrary_binder exp))
        >>= (fun p -> (exp
        >>= (fun e ->
            ((arbitrary_list (arbitrary_pair arbitrary_identifier exp))
        >>= (fun l -> ret_gen (Type (s, p, e, l)))))))))
    ] in
  sized f

let rec arbitrary_expression =
  let rec f = function
    | 0 -> oneof [
      ret_gen Universe;
      ret_gen UnitType;
      ret_gen Unit;
      arbitrary_identifier >>= (fun s -> ret_gen (Constructor s));
    ]
    | n ->
        let g = f (n / size_factor) in 
        let patt = resize (n / size_factor) arbitrary_pattern in
        let decl = resize n arbitrary_declaration in
        oneof [
          g >>= (fun e1 -> (g >>= (fun e2 -> ret_gen (Pair (e1, e2)))));
          arbitrary_binder
            >>= (fun b -> (g >>= (fun e -> ret_gen (Lambda (b, e)))));
          arbitrary_binder >>= (fun b -> (g
            >>= (fun e1 -> (g >>= (fun e2 -> ret_gen (Pi (b, e1, e2)))))));
          arbitrary_binder >>= (fun b -> (g
            >>= (fun e1 -> (g >>= (fun e2 -> ret_gen (Sigma (b, e1, e2)))))));
          (arbitrary_list (arbitrary_pair patt g))
            >>= (fun l -> ret_gen (Function l));
          (arbitrary_nonempty_list decl) >>= (fun l -> (g
            >>= (fun e -> ret_gen (LocalDeclaration (l, e)))));
          g >>= (fun e1 -> (g >>= (fun e2 -> ret_gen (Application (e1, e2)))));
          ret_gen Universe;
          ret_gen UnitType;
          ret_gen Unit;
          arbitrary_identifier >>= (fun s -> ret_gen (Constructor s));
          g >>= (fun e -> ret_gen (Proj1 e));
          g >>= (fun e -> ret_gen (Proj2 e))
        ] in
  sized f

let () = arb_exp := arbitrary_expression 

let show_binder = function
  | Underscore -> "Underscore"
  | Name n -> sprintf "Name \"%s\"" n

let rec show_pattern = function 
  | PatternPair (p1, p2) ->
      sprintf "PatternPair (%s, %s)" (show_pattern p1) (show_pattern p2)
  | PatternApplication (s, l) ->
      sprintf "PatternApplication (\"%s\", %s)" s (show_list show_pattern l)
  | PatternBinder s -> sprintf "PatternBinder \"%s\"" s
  | PatternUnderscore -> "PatternUnderscore"
  | PatternInaccessible e ->
      sprintf "PatternInaccessible (%s)" (show_expression e)
and show_expression = function
  | Pair (e1, e2) ->
      sprintf "Pair (%s, %s)" (show_expression e1) (show_expression e2)
  | Lambda (b, e) ->
      sprintf "Lambda (%s, %s)" (show_binder b) (show_expression e)
  | Pi (b, e1, e2) -> 
      sprintf "Pi (%s, %s, %s)" (show_binder b) (show_expression e1)
        (show_expression e2)
  | Sigma (b, e1, e2) -> 
      sprintf "Sigma (%s, %s, %s)" (show_binder b) (show_expression e1)
        (show_expression e2)
  | Function l ->
      sprintf "Function %s"
        (show_list (show_pair show_pattern show_expression) l)
  | LocalDeclaration (l, e) ->
      sprintf "LocalDeclaration (%s, %s)" (show_list show_declaration l)
        (show_expression e)
  | Application (e1, e2) ->
      sprintf "Application (%s, %s)" (show_expression e1) (show_expression e2)
  | Universe -> "Universe"
  | UnitType -> "UnitType"
  | Unit -> "Unit"
  | Constructor i -> sprintf "Constructor \"%s\"" i
  | Index i -> sprintf "Index %i" i
  | Proj1 e -> sprintf "Proj1 (%s)" (show_expression e)
  | Proj2 e -> sprintf "Proj2 (%s)" (show_expression e)

and show_declaration = function
  | Let (s, e1, e2) ->
      sprintf "Let (\"%s\", %s, %s)" s (show_expression e1) (show_expression e2)
  | LetRec (s, e1, e2) ->
      sprintf "LetRec (\"%s\", %s, %s)"
        s (show_expression e1) (show_expression e2)
  | Type (s, p, e, l) ->
      sprintf "Type (\"%s\", %s, %s, %s)" 
        s
        (show_list (show_pair show_binder show_expression) p)
        (show_expression e)
        (show_list (show_pair (fun x -> "\"" ^ x ^ "\"") show_expression) l)
