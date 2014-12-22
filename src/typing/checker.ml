open Printf

open Abstract
open Context
open Value

type typing_result =
  | SType of value
  | SDecl of (string * value) list * (string * value) list
  | F of string * string Lazy.t

(* these aren't quite the normal monad operations, but they are close *)
let (>>) r f = match r with
  | F _ -> r
  | r -> f ()

let (>>=) r f = match r with
  | F _ -> r
  | SDecl _ -> assert false
  | SType t -> f t

let succeeded = function
  | SType _ | SDecl _ -> true 
  | F _ -> false

let get_type = function
  | SType t -> t
  | F _ | SDecl _ -> raise (Failure "get_type")

let get_binder_types = function
  | SDecl (l, _) -> l
  | F _ | SType _ -> raise (Failure "get_binder_types")

let get_constructor_types = function
  | SDecl (_, l) -> l
  | F _ | SType _ -> raise (Failure "get_constructor_types")

let print_error outchan = function
  | SType _ | SDecl _ -> raise (Failure "print_error")
  | F (e, _) -> fprintf outchan "%s\n" e

let print_trace outchan = function
  | SType _ | SDecl _ -> raise (Failure "print_trace")
  | F (_, t) -> fprintf outchan "%s\n" (Lazy.force t) 

let get_envt context =
    mk_env (get_binder_names context, get_constructor_names context)

let get_full_type env ps e =
  Eval.eval env (List.fold_right (fun (x, t1) t2 -> Pi (x, t1, t2)) ps e)

let filter = List.filter (function
    | LetRec (_, _, _) -> true
    | _ -> false)

let get_env env rest_ds xs =
    Environment.add_declarations env (xs @ (List.rev (filter rest_ds)))

(* adds declarations to the given context; lets are added iff the argument
 * lets is true *)
let add_to_context lets env context =
  let rec add context rest_ds = function
    | [] -> context
    | (Let (x, e1, e2))::xs ->
        if lets
        then add (Context.add_lazy_binder context x
          (lazy (Eval.eval (get_env env rest_ds xs) e1))) rest_ds xs
        else add context rest_ds xs
    | (LetRec (x, e1, e2) as d)::xs ->
        add (Context.add_lazy_binder context x
          (lazy (Eval.eval (get_env env rest_ds xs) e1))) (d::rest_ds) xs
    | (Type (x, ps, e, cs))::xs ->
        let context =
          Context.add_lazy_constructor context x
            (lazy (get_full_type (get_env env rest_ds xs) ps e)) in
        let context =
          List.fold_left (fun context (x, e) -> Context.add_lazy_constructor
            context x (lazy (get_full_type (get_env env rest_ds xs) ps e)))
            context cs in
        add context rest_ds xs in
    add context []

let add_all_to_context = add_to_context true
let add_to_context = add_to_context false

let rec infer_type i env context exp =
  let print () e = 
    try print_expression (get_envt context) e with _ -> "???" in

  let tr = function
    | SType _ as r -> r
    | SDecl _ -> assert false
    | F (e, t) ->
        F (e, lazy (sprintf "%s\nInferring a type for %a."
            (Lazy.force t) print exp)) in

  let failure s = F (s, lazy "") in

  match exp with
  | Pi (Underscore, e1, e2) -> tr (
      check_type i env context e1 VUniverse
      >>= fun _ -> 
      check_type (i + 1) env context e2 VUniverse
      >>= fun _ ->
      SType VUniverse)
  | Pi (Name x, e1, e2) -> tr (
      check_type i env context e1 VUniverse
      >>= fun _ ->
      let env' = Environment.add env (VNeutral (VVar i)) in
      let context' = Context.add_binder context x (Eval.eval env e1) in
      check_type (i + 1) env' context' e2 VUniverse
      >>= fun _ ->
      SType VUniverse)
  | Sigma (Underscore, e1, e2) -> tr (
      check_type i env context e1 VUniverse
      >>= fun _ -> 
      check_type (i + 1) env context e2 VUniverse
      >>= fun _ ->
      SType VUniverse)
  | Sigma (Name x, e1, e2) -> tr (
      check_type i env context e1 VUniverse
      >>= fun _ ->
      let env' = Environment.add env (VNeutral (VVar i)) in
      let context' = Context.add_binder context x (Eval.eval env e1) in
      check_type (i + 1) env' context' e2 VUniverse
      >>= fun _ -> 
      SType VUniverse)
  | Application (e1, e2) -> tr (
      infer_type i env context e1
      >>= function
        | VPi (Underscore, a, b, pi_env) ->
            check_type i env context e2 a
            >>= fun _ ->
            SType (Eval.eval pi_env b)
        | VPi (Name x, a, b, pi_env) -> 
            check_type i env context e2 a
            >>= fun _ ->
            let pi_env' = Environment.add pi_env (Eval.eval env e2) in
            SType (Eval.eval pi_env' b)
        | v ->
            failure (
              sprintf "%a is not a function; it cannot be applied." print e1))
  | Universe -> SType VUniverse
  | Unit -> SType VUnitType
  | UnitType -> SType VUniverse
  | Index j -> (match get_binder_type context j with
      | None ->
          tr (failure (sprintf "The type of index %i is not in the context." j))
      | Some v -> SType v)

  (* normally a type checking rule -- included for declarations given as part of
   * expressions in the REPL *)
  | LocalDeclaration (d, e) -> tr (
      check_declarations i env context d
      >> fun _ ->
      let env' = Environment.add_declarations env d in
      let context' = add_all_to_context env context d in
      tr (infer_type i env' context' e))

  (* not needed in type system -- included for constructors given as part of
   * expressions in the REPL *)
  | Constructor c -> (match get_unique_constructor_type context c with
      | None ->
          failure
            (sprintf "The constructor \"%s\" does not have a unique type." c)
      | Some t -> SType t)

  (* not needed in the type system -- included for pairs given as part of
   * expressions in the REPL *)
  | Pair (e1, e2) -> tr (
      infer_type i env context e1
      >>= fun t1 ->
      infer_type i env context e2
      >>= fun t2 ->
      (* env should not be needed in the next line -- a reified value should not
       * have free variables *)
      SType (VSigma (Underscore, t1, reify t2, env)))

  | _ -> failure (sprintf "Cannot infer a type for %a." print exp)

and check_type i env context exp typ =
  let print_exp () e =
    try print_expression (get_envt context) e with _ -> "???" in
  let print_val () v = 
    try Print_value.string_of_value v with _ -> "???" in

  let tr = function
    | SType _ as r -> r
    | SDecl _ -> assert false
    | F (e, t) ->
        F (e, lazy (sprintf "%s\nChecking that %a has type %a."
            (Lazy.force t) print_exp exp print_val typ)) in

  let failure s = F (s, lazy "") in

  match exp, typ with
  | Pair (e1, e2), VSigma (Underscore, a, b, sigma_env) -> tr (
      check_type i env context e1 a
      >>= fun _ ->
      check_type i env context e2 (Eval.eval sigma_env b))
  | Pair (e1, e2), VSigma (Name x, a, b, sigma_env) -> tr (
      check_type i env context e1 a
      >>= fun _ ->
      let sigma_env' = Environment.add env (Eval.eval sigma_env e1) in
      let context' = Context.add_binder context x a in
      check_type i env context' e2 (Eval.eval sigma_env' b))
  | Lambda (Underscore, e1), VPi (Underscore, a, b, pi_env) -> tr (
      check_type i env context e1 (Eval.eval pi_env b))
  | Lambda (Underscore, e1), VPi (Name x, a, b, pi_env) -> tr (
      let pi_env' = Environment.add pi_env (VNeutral (VVar i)) in
      check_type (i + 1) env context e1 (Eval.eval pi_env' b))
  | Lambda (Name x, e1), VPi (Underscore, a, b, pi_env) -> tr (
      let env' = Environment.add env (VNeutral (VVar i)) in
      let context' = Context.add_binder context x a in
      check_type (i + 1) env' context' e1 (Eval.eval pi_env b))
  | Lambda (Name x, e1), VPi (Name y, a, b, pi_env) -> tr (
      let env' = Environment.add env (VNeutral (VVar i)) in
      let context' = Context.add_binder context x a in
      let pi_env' = Environment.add pi_env (VNeutral (VVar i)) in
      check_type (i + 1) env' context' e1 (Eval.eval pi_env' b))
  | Constructor c, _ -> 
      if check_constructor_type context c typ
      then SType typ
      else
        tr (failure (sprintf "The type of \"%s\" is not %a." c print_val typ))
  | LocalDeclaration (d, e), _ -> tr (
      check_declarations i env context d
      >> fun _ ->
      let env' = Environment.add_declarations env d in
      let context' = add_all_to_context env context d in
      tr (check_type i env' context' e typ))
  | _ -> tr (
      infer_type i env context exp
      >>= fun inferred_type ->
      if (Equality.readback i inferred_type) = (Equality.readback i typ)
      then SType typ
      else failure (sprintf "%a is not equal to %a." print_val inferred_type
             print_val typ))

and check_declarations i env context =
  let tr x = function
    | SType _ as r -> r
    | SDecl _ -> assert false
    | F (e, t) ->
        F (e, lazy (sprintf "%s\nChecking the declaration of \"%s\"."
            (Lazy.force t) x)) in
  
  let get_new_context rest_bs rest_cs xs =
    let context =
       List.fold_left (fun c (s, v) -> Context.add_constructor c s v)
         context rest_cs in
    (* assume that everything in xs has the correct type, without actually
     * checking them *)
    let context = add_to_context env context xs in
    List.fold_right (fun (s, v) c -> Context.add_binder c s v)
      rest_bs context in

  let rec check_decls result_bs result_cs rest_ds rest_bs = function
    | [] -> SDecl (result_bs, result_cs)
    | (Let (x, e1, e2))::xs ->
        (* FIXME: Should check that e1 is a type first *)
        let decl_env = get_env env rest_ds xs in
        let t = Eval.eval decl_env e1 in
        let decl_context = get_new_context rest_bs result_cs xs in
        tr x (check_type i decl_env decl_context e2 t)
        >>= fun _ -> 
        check_decls ((x, t)::result_bs) result_cs rest_ds rest_bs xs
    | (LetRec (x, e1, e2) as d)::xs ->
        (* FIXME: Should check that e1 is a type first *)
        let decl_env = get_env env rest_ds xs in
        let decl_env2 = 
          Environment.add_declarations env
            (xs @ (List.rev (d::(filter rest_ds)))) in
        let t = Eval.eval decl_env e1 in
        let decl_context = get_new_context ((x, t)::rest_bs) result_cs xs in
        tr x (check_type i decl_env2 decl_context e2 t)
        >>= fun _ -> 
        check_decls ((x, t)::result_bs) result_cs (d::rest_ds) rest_bs xs
    | (Type (x, ps, e, cs))::xs ->
        (* FIXME: Should check that the types are actually types *)
        let decl_env = env in
        let result_cs = (x, (get_full_type decl_env ps e)) :: result_cs in
        let result_cs = List.fold_left
          (fun l (x, e) -> (x, (get_full_type decl_env ps e))::l)
          result_cs cs in
        check_decls result_bs result_cs rest_ds rest_bs xs in
  check_decls [] [] [] []

let infer_type = infer_type 0
let check_type = check_type 0
let check_declarations = check_declarations 0
