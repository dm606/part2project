open Core_bench.Bench.Test

let code = "
type Nat = zero : Nat | succ : Nat -> Nat

let rec double : Nat -> Nat = function
  | zero -> zero
  | succ n -> succ (succ (double n))

let rec pow2 : Nat -> Nat = function
  | zero -> succ zero
  | succ n -> double (pow2 n)

let double_tr : Nat -> Nat =
  let rec aux (acc : Nat) : Nat -> Nat = function
    | zero -> acc
    | succ n -> aux (succ (succ acc)) n in
  aux zero

let pow2_tr : Nat -> Nat =
  let rec aux (acc : Nat) : Nat -> Nat = function
    | zero -> acc
    | succ n -> aux (double_tr acc) n in
  aux (succ zero)

type Bool = false : Bool | true : Bool

type List = nil : List | cons : Nat -> List -> List

let rec lt_nat (m : Nat) (n : Nat) : Bool = match m, n with
  | _, zero -> false
  | zero, succ _ -> true
  | succ x, succ y -> lt_nat x y

let rec insert (a : Nat) : List -> List = function
  | nil -> cons a nil
  | cons b l -> (match lt_nat a b with
      | false -> cons b (insert a l)
      | true -> cons a (cons b l))

let insert_sort : List -> List =
  let rec aux (acc : List) : List -> List = function
    | nil -> acc
    | cons a l -> aux (insert a acc) l in
  aux nil
"

let declared = ref Abstract.empty_env
let env = ref Environment.empty
let context = ref Context.empty
let constraints = ref Equality.no_constraints

let check_declarations context d =
  let result = Checker.check_declarations !constraints !env context d in
  if Checker.succeeded result then result
  else (Checker.print_error stderr result; exit 1)

let add_declarations_to_context context result =
  let context =
    List.fold_right
      (fun (s, v) c -> Context.add_binder c s v)
      (Checker.get_binder_types result) context in
  let constructor_types = Checker.get_constructor_types result in
  constraints := Checker.get_constraints result;
  (* the order of constructors does not matter -- use fold_left for
   * efficiency *)
  List.fold_left
    (fun c (s, type_name, v) -> Context.add_constructor c s type_name v)
    context constructor_types

let desugar = function
  | Parser.Exp e ->
      let exp = Abstract.desugar_expression !declared e in
      let typing_result = Checker.infer_type !constraints !env !context exp in
      if Checker.succeeded typing_result
      then Some (Checker.get_expression typing_result)
      else (Checker.print_error stderr typing_result; exit 1)
  | Parser.Decl d ->
      let new_declared = Abstract.add_all_declaration_binders !declared d in
      let decl = Abstract.desugar_declarations !declared d in
      let result = check_declarations !context decl in
      let decl = Checker.get_declarations result in
      let new_context = add_declarations_to_context !context result in
      let new_env = Environment.add_declarations !env decl in
      declared := new_declared;
      env := new_env;
      context := new_context;
      None
  | _ -> exit 1

let rec map_opt f = function
  | [] -> []
  | hd::tl -> (match f hd with
      | None -> map_opt f tl
      | Some hd -> hd::(map_opt f tl))

let parse_string s =
  Lexing.from_string s
  |> Parser.parse_file
  |> map_opt desugar

let random_list =
  let rec aux n = if n = 0 then [] else (Random.int 10)::(aux (n - 1)) in
  Random.self_init ();
  aux 100000

(*****************************************************************************)
(* ^2                                                                        *)
(*****************************************************************************)
let pow2_exp, pow2_tr_exp, insert_sort_exp =
  match parse_string (code ^ "\n;; pow2;; pow2_tr;; insert_sort") with
  | [x; y; z] -> x, y, z
  | _ -> exit 1

let rec get_nat = function
  | 0 -> Abstract.Constructor "zero"
  | n -> Abstract.Application (Abstract.Constructor "succ", get_nat (n - 1))

let eval_pow2 n =
  let exp = Abstract.Application (pow2_exp, get_nat n) in
  let eval = Eval.eval (Equality.get_metavariable_assignment !constraints) !env in
  Core.Staged.stage (fun () -> ignore (eval exp))

let eval_pow2_tr n =
  let exp = Abstract.Application (pow2_tr_exp, get_nat n) in
  let eval = Eval.eval (Equality.get_metavariable_assignment !constraints) !env in
  Core.Staged.stage (fun () -> ignore (eval exp))

(*****************************************************************************)
(* Insert sort                                                               *)
(*****************************************************************************)

let get_list n =
  let rec aux rem n =
    if n = 0 then Abstract.Constructor "nil"
    else
      Abstract.Application (
        Abstract.Application (Abstract.Constructor "cons", List.hd rem),
        aux (List.tl rem) (n - 1)) in
  aux (List.map get_nat random_list) n

let eval_insert_sort n =
  let exp = Abstract.Application (insert_sort_exp, get_list n) in
  let eval = Eval.eval (Equality.get_metavariable_assignment !constraints) !env in
  Core.Staged.stage (fun () -> ignore (eval exp))

(******************************************************************************)
(* OCaml unary ^2                                                             *)
(******************************************************************************)
type nat = Zero | Succ of nat

let rec double = function
  | Zero -> Zero
  | Succ n -> Succ (Succ (double n))

let rec unary_pow2 = function
  | Zero -> Succ Zero
  | Succ n -> double (unary_pow2 n)

let rec get_nat = function
  | 0 -> Zero
  | n -> Succ (get_nat (n - 1))

let unary_pow2 n =
  let n = get_nat n in
  Core.Staged.stage (fun () -> ignore (unary_pow2 n))

let double_tr =
  let rec aux acc = function
    | Zero -> Zero
    | Succ n -> aux (Succ (Succ acc)) n in
  aux Zero

let unary_pow2_tr =
  let rec aux acc = function
    | Zero -> acc
    | Succ n -> aux (double_tr acc) n in
  aux (Succ Zero)

let unary_pow2_tr n =
  let n = get_nat n in
  Core.Staged.stage (fun () -> ignore (unary_pow2_tr n))

(******************************************************************************)
(* OCaml insert sort                                                          *)
(******************************************************************************)

type bool = False | True

type list  = Nil | Cons of nat * list

let rec lt_nat m n = match m, n with
  | _, Zero -> False
  | Zero, Succ _ -> True
  | Succ x, Succ y -> lt_nat x y

let rec insert a = function
  | Nil -> Cons (a, Nil)
  | Cons (b, l) -> (match lt_nat a b with
      | False -> Cons (b, (insert a l))
      | True -> Cons (a, (Cons (b, l))))

let insert_sort =
  let rec aux acc = function
    | Nil -> acc
    | Cons (a, l) -> aux (insert a acc) l in
  aux Nil

let get_list n =
  let rec aux rem n =
    if n = 0 then Nil
    else Cons (List.hd rem, aux (List.tl rem) (n - 1)) in
  aux (List.map get_nat random_list) n

let unary_insert_sort n =
  let list = get_list n in
  Core.Staged.stage (fun () -> ignore (insert_sort list))

(******************************************************************************)
(* Benchmarks                                                                 *)
(******************************************************************************)

let rec (--) n1 n2 = if n1 > n2 then [] else n1::((n1+1)--n2)

let pow2_indices = 0--14
let insert_sort_indices = List.map (fun n -> n * 10) (0--20)

let bench = [
  create_indexed "pow2" pow2_indices eval_pow2;
  create_indexed "pow2_tr" pow2_indices eval_pow2_tr;
  create_indexed "unary_pow2" pow2_indices unary_pow2;
  create_indexed "unary_pow2_tr" pow2_indices eval_pow2;
  create_indexed "insert_sort" insert_sort_indices eval_insert_sort;
  create_indexed "unary_insert_sort" insert_sort_indices unary_insert_sort]

let () =
  bench
  |> Core_bench.Bench.make_command
  |> Core.Std.Command.run
