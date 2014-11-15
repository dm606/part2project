open Printf
open OUnit2
open QuickCheck
open QuickCheck_gen

open Abstract

let quickCheck_test name testable test = name >:: fun _ ->
  match verboseCheck testable test with
  | Success -> ()
  | Failure i -> assert_failure ("quickcheck test failure " ^ (string_of_int i))
  | Exhausted i ->
      assert_failure ("quicktest test exhausted " ^ (string_of_int i))

let arbitrary_binder =
  oneof [ret_gen Underscore; arbitrary_string >>= (fun s -> ret_gen (Name s))]

let arbitrary_pattern =
  let rec f = function
    | 0 -> ret_gen PatternUnderscore
    | n -> 
        let g = f (n / 2) in
        oneof [
          g >>= (fun p1 -> (g >>= (fun p2 -> ret_gen (PatternPair (p1, p2)))));
          arbitrary_string >>= (fun s -> ((arbitrary_list g)
            >>= (fun l -> ret_gen (PatternApplication (s, l)))));
          arbitrary_string >>= (fun s -> ret_gen (PatternIdentifier s));
          ret_gen PatternUnderscore
        ] in
  sized f

(* HACK to avoid let rec restrictions *)
let arb_exp = ref (ret_gen Unit)

let arbitrary_declaration =
  let f n = 
    let exp = resize (n / 2) !arb_exp in
    oneof [
      arbitrary_string >>= (fun s -> (exp
        >>= (fun e1 -> (exp >>= (fun e2 -> ret_gen (Let (s, e1, e2)))))));
      arbitrary_string >>= (fun s -> (exp
        >>= (fun e1 -> (exp >>= (fun e2 -> ret_gen (LetRec (s, e1, e2)))))));
      arbitrary_string
        >>= (fun s -> ((arbitrary_list (arbitrary_pair arbitrary_binder exp))
        >>= (fun p -> (exp
        >>= (fun e -> ((arbitrary_list (arbitrary_pair arbitrary_string exp))
        >>= (fun l -> ret_gen (Type (s, p, e, l)))))))))
    ] in
  sized f

let rec arbitrary_expression =
  let rec f = function
    | 0 -> ret_gen Unit
    | n ->
        let g = f (n / 2) in 
        let patt = resize (n / 2) arbitrary_pattern in
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
          (arbitrary_list decl) >>= (fun l -> (g
            >>= (fun e -> ret_gen (LocalDeclaration (l, e)))));
          g >>= (fun e1 -> (g >>= (fun e2 -> ret_gen (Application (e1, e2)))));
          ret_gen Universe;
          ret_gen UnitType;
          ret_gen Unit;
          arbitrary_string >>= (fun s -> ret_gen (Identifier s));
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
  | PatternIdentifier s -> sprintf "PatternIdentifier \"%s\"" s
  | PatternUnderscore -> "PatternUnderscore"

let rec show_expression = function
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
      sprintf "Function %s" (show_list (show_pair show_pattern show_expression) l)
  | LocalDeclaration (l, e) ->
      sprintf "Declaration (%s, %s)" (show_list show_declaration l)
        (show_expression e)
  | Application (e1, e2) ->
      sprintf "Application (%s, %s)" (show_expression e1) (show_expression e2)
  | Universe -> "Universe"
  | UnitType -> "UnitType"
  | Unit -> "Unit"
  | Identifier i -> sprintf "Identifier \"%s\"" i
  | Proj1 e -> sprintf "Proj1 (%s)" (show_expression e)
  | Proj2 e -> sprintf "Proj2 (%s)" (show_expression e)

and show_declaration = function
  | Let (s, e1, e2) ->
      sprintf "Let (\"%s\", %s, %s)" s (show_expression e1) (show_expression e2)
  | LetRec (s, e1, e2) ->
      sprintf "LetRec (\"%s\", %s, %s)" s (show_expression e1) (show_expression e2)
  | Type (s, p, e, l) ->
      sprintf "Type (\"%s\", %s, %s, %s)" 
        s
        (show_list (show_pair show_binder show_expression) p)
        (show_expression e)
        (show_list (show_pair (fun x -> x) show_expression) l)
