open Abstract
open Value

exception Cannot_check_termination of string * string
exception Doesnt_terminate of string

type order = LessThan | LessThanOrEqual | Unknown

type order_matrix = order list list (* list of rows *)

let multiply_order x y = match x, y with
  | LessThan, LessThan -> LessThan
  | LessThan, LessThanOrEqual -> LessThan
  | LessThan, Unknown -> Unknown
  | LessThanOrEqual, LessThan -> LessThan
  | LessThanOrEqual, LessThanOrEqual -> LessThanOrEqual
  | LessThanOrEqual, Unknown -> Unknown
  | Unknown, LessThan -> Unknown
  | Unknown, LessThanOrEqual -> Unknown
  | Unknown, Unknown -> Unknown

let add_order x y = match x, y with
  | LessThan, LessThan -> LessThan
  | LessThan, LessThanOrEqual -> LessThan
  | LessThan, Unknown -> LessThan
  | LessThanOrEqual, LessThan -> LessThan
  | LessThanOrEqual, LessThanOrEqual -> LessThanOrEqual
  | LessThanOrEqual, Unknown -> LessThanOrEqual
  | Unknown, LessThan -> LessThan
  | Unknown, LessThanOrEqual -> LessThanOrEqual
  | Unknown, Unknown -> Unknown

let minimum_order x y = match x, y with
  | LessThan, LessThan -> LessThan
  | LessThan, LessThanOrEqual -> LessThanOrEqual
  | LessThan, Unknown -> Unknown
  | LessThanOrEqual, LessThan -> LessThanOrEqual
  | LessThanOrEqual, LessThanOrEqual -> LessThanOrEqual
  | LessThanOrEqual, Unknown -> Unknown
  | Unknown, LessThan -> Unknown
  | Unknown, LessThanOrEqual -> Unknown
  | Unknown, Unknown -> Unknown

(* transpose_map f [[x11; ...; x1n]; ...; [xm1; ...; xmn]] returns
 * [f [x11; x21; ...; xm1]; ...; f [x1n; ... xmn]].
 *
 * Assumes that the list is not empty, and that all lists are of the same length
 * *)
let rec transpose_map f l = 
  if List.hd l = [] then []
  else (f (List.map List.hd l))::transpose_map f (List.map List.tl l)

let rec map_append f = List.fold_left (fun tl a -> tl @ (f a)) []

(* Multiplication of order matrices. The matrices will be small, so naive
 * multiplication is fine here. This function assumes that the sizes are
 * compatible *)
let rec ( * ) l1 l2 =
  List.map (fun row -> transpose_map (fun column -> 
    List.fold_left add_order Unknown
    (List.map2 multiply_order row column)) l2) l1

(* exists_element p m returns true iff the matrix m contains an element
 * satisfying p *)
let exists_element p = List.exists (fun l -> List.exists p l)

(* reverses the first list, removes all elements which are already in the
 * second list, and then appends *)
let nodup_rev_append l1 l2 =
  List.fold_left
    (fun (tl, p) x -> if List.mem x tl then (tl, p) else (x::tl, true))
    (l2, false)
    l1

let rec take i l = match i, l with
  | 0, _ -> []
  | _, hd::tl -> hd::(take (i - 1) tl)
  | _ -> raise (Failure "take")

(* removes rows and columns from the ends of the matrices to make them able to
 * be multiplied *)
let rec trim m m2 =
  if m = [] then [], []
  else
    let colsm = List.length (List.hd m) in
    let rowsm2 = List.length m2 in
    if colsm = rowsm2 then m, m2
    else if colsm < rowsm2 then m, take colsm m2
    else List.map (take rowsm2) m, m2

(* closes a call graph i.e. for each possible stack of calls from x to y,
 * returns a call graph showing how the arguments of x relate to the arguments
 * of y *)
let close =
  let compose_all (x, y, m) =
    List.fold_left
      (fun tl (x2, y2, m2) -> if y = x2 then
         (* trim to make the dimensions match -- loses information, making the
          * algorithm less likely to report that the declarations terminate *)
         let m, m2 = trim m m2 in
         (x, y2, m * m2)::tl else tl)
      [] in
  let close_step l =
    List.fold_left
      (fun (tl, p) t ->
         match nodup_rev_append (compose_all t l) tl with
         | l, false -> (l, p)
         | l, true -> (l, true))
      (l, false) l in
  let rec aux l = match close_step l with
    | l, true -> aux l
    | l, false -> l in
  aux

(* does_terminate name closed, where closed is a closed call graph, returns
 * true only if the declaration refered to by name is terminating *)
let does_terminate name l =
  (* the important matrices are those from name to name, which are the same if
   * twice as many calls are made *)
  let important_matrices =
    List.filter (fun (a, b, m) ->
      let m, m2 = trim m m in
      a = b && a = name && m * m2 = m) l in 
  (* if all important matrices contain at least one LessThan, then the function
   * must always terminate *)
  List.for_all (fun (a, b, m) -> exists_element (fun x -> x = LessThan) m)
    important_matrices

(* if an environment does not contain a neutral variable, then calls in it
 * cannot refer to one of the declarations being checked, so calls inside it can
 * exception Doesnt_terminate
 * be ignored *)
let rec contains_neutral_variable env =
  let rec value = function
    | VPair (v1, v2) -> value v1 || value v2
    | VLambda (_, _, e) -> contains_neutral_variable e
    | VArrow (v1, v2) -> value v1 || value v2
    | VPi (_, a, _, e) -> value a || contains_neutral_variable e
    | VTimes (v1, v2) -> value v1 || value v2
    | VSigma (_, a, _, e) -> value a || contains_neutral_variable e
    | VFunction (_, e) -> contains_neutral_variable e
    | VUniverse _ | VUnit | VUnitType -> false
    | VConstruct (_, l) -> List.exists value l
    | VNeutral _ -> true in
  List.mem true (Environment.map_to_list (fun v -> value v)
    (fun d -> false) env)

let rec get_rel v1 v2 =
  if v1 = v2 then LessThanOrEqual
  else match v1, v2 with
    | VConstruct (c1, []), VConstruct (c2, []) when c1 = c2 -> LessThanOrEqual
    | VConstruct (c1, tl1) , VConstruct (c2, tl2) when c1 = c2 ->
        List.fold_left2 (fun r v1 v2 -> min r (get_rel v1 v2)) Unknown tl1 tl2
    | VConstruct (c1, _), VConstruct (c2, _) -> Unknown
    | _, VConstruct (c1, tl) ->
        if List.exists (fun v2 -> get_rel v1 v2 <> Unknown) tl then LessThan
        else Unknown
    | VPair (v11, v12), VPair (v21, v22) ->
        min (get_rel v11 v21) (get_rel v12 v22)
    | _, VPair (v21, v22) ->
        if get_rel v1 v21 = LessThan || get_rel v1 v22 = LessThan then LessThan
        else Unknown
    | _ -> Unknown

let get_matrix l1 l2 =
  List.map (fun v2 -> List.map (fun v1 -> get_rel v2 v1) l1) l2

let rec find_non_terminating i graph = function
  | [] -> None
  | (LetRec (x, _, _))::tl ->
      if does_terminate i graph
      then find_non_terminating (i + 1) graph tl else Some x
  | _::tl -> find_non_terminating i graph tl

let rec add_decls i env = function
  | [] -> env
  | x::xs -> add_decls (i + 1) (Environment.add env (VNeutral (VVar i))) xs

let rec eval i env =
  Eval.eval' (fun env l -> match check_termination' i env l with
    | Some x -> raise (Doesnt_terminate x)
    | None -> ()) env

and add_pattern i env = function
  | PatternUnderscore -> (i + 1, env, VNeutral (VVar i))
  | PatternBinder _ ->
      (i + 1, Environment.add env (VNeutral (VVar i)), VNeutral (VVar i))
  | PatternInaccessible e -> (i, env, eval i env e)
  | PatternPair (p1, p2) ->
      let i, env, v1 = add_pattern i env p1 in
      let i, env, v2 = add_pattern i env p2 in
      (i, env, VPair (v1, v2))
  | PatternApplication (c, tl) -> 
      let i, env, values = List.fold_left
        (fun (i, env, tl) p ->
           let i, env, v = add_pattern i env p in
           (i, env, v::tl))
        (i, env, []) tl in
      (i, env, VConstruct (c, values))

(* the declaration must have been added as neutrals to the environment *)
and extract_calls x i env args = function
  | VPair (e1, e2) ->
      extract_calls x i env args e1 @ extract_calls x i env args e2
  | VLambda (Underscore, e, lambda_env) ->
      if contains_neutral_variable lambda_env 
      then extract_calls x i lambda_env args (eval i lambda_env e)
      else []
  | VLambda (Name x, e, lambda_env) ->
      if contains_neutral_variable lambda_env
      then
        let lambda_env' = Environment.add lambda_env (VNeutral (VVar i)) in
        extract_calls x (i + 1) lambda_env' args (eval (i + 1) lambda_env' e)
      else []
  | VArrow (a, b) -> extract_calls x i env args a @ extract_calls x i env args b
  | VPi (x, a, b, pi_env) ->
      if contains_neutral_variable pi_env
      then
        let pi_env' = Environment.add pi_env (VNeutral (VVar i)) in
        extract_calls x i env args a
        @ extract_calls x (i + 1) pi_env' args (eval (i + 1) pi_env' b)
      else extract_calls x i env args a
  | VTimes (a, b) -> extract_calls x i env args a @ extract_calls x i env args b
  | VSigma (x, a, b, sigma_env) ->
      if contains_neutral_variable sigma_env
      then
        let sigma_env' = Environment.add sigma_env (VNeutral (VVar i)) in
        extract_calls x i env args a
        @ extract_calls x (i + 1) sigma_env' args (eval (i + 1) sigma_env' b)
      else extract_calls x i env args a 
  | VFunction (c, fun_env) ->
      if contains_neutral_variable fun_env
      then
        map_append 
          (extract_calls_case x (i + 1) fun_env args (VNeutral (VVar i))) c
      else []
  | VUniverse _ | VUnit | VUnitType -> []
  | VConstruct (_, l) -> map_append (extract_calls x i env args) l
  | VNeutral n -> extract_calls_neutral x i env args n
and extract_calls_neutral x i env args = function
  | VVar i -> [i, []]
(*  | VFunctionApplication (c, fun_env, v) ->
      if contains_neutral_variable fun_env
      then
        extract_calls i env args v
        @ map_append (extract_calls_case i fun_env args v) c
      else extract_calls i env args v*)
  | VFunctionApplication (c, fun_env, v) -> extract_calls x i env args v 
  | VApplication (n, v) ->
      extract_calls x i env args v
      @ extract_calls_application x i env args n [v]
  | VProj1 n -> extract_calls_neutral x i env args n
  | VProj2 n -> extract_calls_neutral x i env args n
and extract_calls_case x i env args v (p, e) =
  let i, env, v2 = add_pattern i env p in
  match Context.mgu Context.subst_empty v v2 with
  | None ->
      raise (Cannot_check_termination (x, 
        "Couldn't unify the value which a function was applied to with one of "
        ^ "the patterns in it's definition. Maybe there is a type error."))
  | Some subst ->
      let env = Context.subst_env subst env in
      let args = List.map (Context.subst_value subst) args in
      extract_calls x i env args (eval (i + 1) env e)
and extract_calls_application x i env args n tl =
  match n with
  | VVar i -> [i, get_matrix args tl]
  | VFunctionApplication (c, fun_env, v) ->
      map_append (fun (_, e) ->
        let fun_env = Environment.add fun_env (VNeutral (VVar i)) in
        extract_calls x (i + 1) fun_env args (eval (i + 1) fun_env e)) c @
        extract_calls x i env args v
  | VApplication (n, v) ->
      extract_calls x i env args v
      @ extract_calls_application x i env args n (v::tl)
  | VProj1 _ | VProj2 _ -> raise (Cannot_check_termination (x, ""))

and get_call_matrices' x i args env decl_var min_var max_var e =
  match eval i env e with
  | VLambda (Underscore, e, lambda_env) ->
      get_call_matrices' x (i + 1) ((VNeutral (VVar i))::args) lambda_env
        decl_var min_var max_var e
  | VLambda (Name _, e, lambda_env) ->
      let v = VNeutral (VVar i) in
      get_call_matrices' x (i + 1) (v::args) (Environment.add lambda_env v)
        decl_var min_var max_var e
  | VFunction (c, fun_env) ->
      map_append (fun (p, e) ->
        let (i, env, v) = add_pattern i env p in
        get_call_matrices' x i (v::args) env decl_var min_var max_var e
      ) c
  | v ->
      let calls = List.filter (fun (j, _) -> j >= min_var && j <= max_var)
        (extract_calls x i env (List.rev args) v) in
      List.map (fun (i, tl) -> (decl_var, i, tl)) calls 

and get_call_matrices x i = get_call_matrices' x i []

and check_termination' i env l =
  let min_var = i in
  let rec get_max_var i = function
    | [] -> i
    | (LetRec _)::tl -> get_max_var (i + 1) tl
    | _::tl -> get_max_var i tl in
  let max_var = get_max_var (i - 1) l in
  let rec get_graph i graph rest = function
    | [] -> graph
    | (LetRec (x, a, b))::xs -> (
        try
          let v = VNeutral (VVar i) in
          let env' = add_decls (i + 1) env xs in
          let env' = add_decls min_var env' (List.rev rest) in
          let env' = Environment.add env' v in
          let rest = v::rest in
          let graph =
            get_call_matrices x (max_var + 1) env' i min_var max_var b
            @ graph in
          get_graph (i + 1) graph rest xs with
        | Eval.Cannot_evaluate _ | Eval.Pattern_match | Eval.Match_neutral ->
            raise
              (Cannot_check_termination (x, "Maybe there is a type error.")))
    | _::tl -> get_graph i graph rest tl in
  let graph = close (get_graph min_var [] [] l) in
  
  find_non_terminating min_var graph l 

let check_termination env l = try check_termination' 0 env l with
  | Doesnt_terminate x -> Some x
