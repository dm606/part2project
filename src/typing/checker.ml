open Printf

open Abstract
open Context
open Value

exception Unsolved_implicit_metavariable

type typing_result =
  | SType of expression * value * Equality.constraints
  | SDecl of declaration list * declaration list * (string * value) list * (string * string * value) list
             * Equality.constraints
  | F of string * string Lazy.t

(* these aren't quite the normal monad operations, but they are close *)
let (>>) r f = match r with
  | F _ -> r
  | SDecl (_, _, _, _, constraints) -> f constraints
  | SType (_, _, constraints) -> f constraints

let (>>=) r f = match r with
  | F _ -> r
  | SDecl _ -> assert false
  | SType (e, t, constraints) -> f (e, t, constraints)

let succeeded = function
  | SType _ | SDecl _ -> true 
  | F _ -> false

let get_type = function
  | SType (_, t, _) -> t
  | F _ | SDecl _ -> raise (Failure "get_type")

let get_expression = function
  | SType (e, _, _) -> e
  | F _ | SDecl _ -> raise (Failure "get_expression")

let get_binder_types = function
  | SDecl (_, _, l, _, _) -> l
  | F _ | SType _ -> raise (Failure "get_binder_types")

let get_constructor_types = function
  | SDecl (_, _, _, l, _) -> l
  | F _ | SType _ -> raise (Failure "get_constructor_types")

let get_declarations = function
  | SDecl (_, d, _, _, _) -> d
  | F _ | SType _ -> raise (Failure "get_declarations")

let get_constraints = function
  | SType (_, _, c) -> c
  | SDecl (_, _, _, _, c) -> c
  | F _ -> raise (Failure "get_constraints")

let print_error outchan = function
  | SType _ | SDecl _ -> raise (Failure "print_error")
  | F (e, _) -> fprintf outchan "%s\n" e

let print_trace outchan = function
  | SType _ | SDecl _ -> raise (Failure "print_trace")
  | F (_, t) -> fprintf outchan "%s\n" (Lazy.force t) 

let get_envt context =
    mk_env (get_binder_names context, get_constructor_names context)

let get_full_type implicit_params ps e =
  let add p t2 = match p with
    | Parameter (x, t1) -> if implicit_params then PiImplicit (x, t1, t2) else Pi (Name x, t1, t2)
    | ParameterImplicit (x, t1) -> PiImplicit (x, t1, t2) in
  List.fold_right add ps e

let filter = List.filter (function
    | LetRec (_, _, _) -> true
    | _ -> false)

let get_env env rest_ds xs =
    Environment.add_declarations env (xs @ (List.rev (filter rest_ds)))

(*let rec add_applications constraints ((_, _, env) as c) exp rest target t = match rest, target, t with
  | ApplicationImplicit (e1, e2), target, VPiImplicit (y, a2, b2, env2) ->
      let v2 = Eval.eval (Equality.get_metavariable_assignment constraints) env e2 in
      let b2 = Eval.eval (Equality.get_metavariable_assignment constraints)
        (Environment.add env2 v2) b2 in
      add_applications constraints c exp e1 target b2
  | rest, VPiImplicit (x, a1, b1, env1), VPiImplicit (y, a2, b2, env2) ->
      let id = create_implicit_metavariable () in
      let constraints = Equality.add_metavariable constraints c id a1 in
      let b1 = Eval.eval (Equality.get_metavariable_assignment constraints)
      (Environment.add env1 (VNeutral (VMeta id))) b1 in
      let b2 = Eval.eval (Equality.get_metavariable_assignment constraints)
      (Environment.add env1 (VNeutral (VMeta id))) b2 in
      add_applications constraints c rest (ApplicationImplicit (exp, Meta id)) b1 b2
  | rest, target, VPiImplicit (y, a2, b2, env2) ->
      let id = create_implicit_metavariable () in
      let b2 = Eval.eval (Equality.get_metavariable_assignment constraints)
      (Environment.add env2 (VNeutral (VMeta id))) b2 in
      add_applications constraints c rest (ApplicationImplicit (exp, Meta id)) target b2
  | _, _, _ -> (exp, target, t, constraints)
*)

let rec add_applications constraints ((_, _, env) as c) exp target t = match target, t with
  | VPiImplicit (x, a1, b1, env1), VPiImplicit (y, a2, b2, env2) ->
      let id = create_implicit_metavariable () in
      let constraints = Equality.add_metavariable constraints c id a1 in
      let b1 = Eval.eval (Equality.get_metavariable_assignment constraints)
      (Environment.add env1 (VNeutral (VMeta id))) b1 in
      let b2 = Eval.eval (Equality.get_metavariable_assignment constraints)
      (Environment.add env1 (VNeutral (VMeta id))) b2 in
      add_applications constraints c (ApplicationImplicit (exp, Meta id)) b1 b2
  | target, VPiImplicit (y, a2, b2, env2) ->
      let id = create_implicit_metavariable () in
      let b2 = Eval.eval (Equality.get_metavariable_assignment constraints)
      (Environment.add env2 (VNeutral (VMeta id))) b2 in
      add_applications constraints c (ApplicationImplicit (exp, Meta id)) target b2
  | _, _ -> (exp, target, t, constraints)

let rec strip_implicit_applications constraints env apps t = match apps, t with
  | e2::tl, VPiImplicit (x, a, b, pi_env) ->
      let v2 = Eval.eval (Equality.get_metavariable_assignment constraints) env
      e2 in
      let b = Eval.eval (Equality.get_metavariable_assignment constraints)
      (Environment.add pi_env v2) b in
      strip_implicit_applications constraints env tl b
  | _, _ -> t

(* adds declarations to the given context; lets are added iff the argument
 * lets is true *)
let add_to_context lets metavars env context =
  let rec add context rest_ds = function
    | [] -> context
    | (Let (x, e1, e2))::xs ->
        if lets
        then add (Context.add_lazy_binder context x
          (lazy (Eval.eval metavars (get_env env rest_ds xs) e1))) rest_ds xs
        else add context rest_ds xs
    | (LetRec (x, e1, e2) as d)::xs ->
        add (Context.add_lazy_binder context x
          (lazy (Eval.eval metavars (get_env env rest_ds xs) e1))) (d::rest_ds) xs
    | (Type (x, ps, e, cs))::xs ->
        let context = Context.remove_constructors_of_type context x in
        let context =
          Context.add_lazy_constructor context x "Type"
            (lazy (Eval.eval metavars (get_env env rest_ds xs) (get_full_type false ps e))) in
        let context =
          List.fold_left (fun context (c, e) -> Context.add_lazy_constructor
              context c x
              (lazy (Eval.eval metavars (get_env env rest_ds xs) (get_full_type true ps e))))
            context cs in
        add context rest_ds xs in
    add context []

let rec is_implicit_constructor_application = function
  | Constructor _ -> true
  | ApplicationImplicit (e1, _) -> is_implicit_constructor_application e1
  | _ -> false

let rec get_constructor_from_implicit_application = function
  | Constructor c -> c
  | ApplicationImplicit (e1, _) -> get_constructor_from_implicit_application e1
  | _ -> assert false

let rec is_implicit_index_application = function
  | Index _ -> true
  | ApplicationImplicit (e1, _) -> is_implicit_index_application e1
  | _ -> false

let rec get_index_from_implicit_application = function
  | Index c -> c
  | ApplicationImplicit (e1, _) -> get_index_from_implicit_application e1
  | _ -> assert false

let get_list_implicit_applications = 
  let rec aux acc = function
    | ApplicationImplicit (e1, e2) -> aux (e2::acc) e1
    | _ -> acc in
  aux []

let form_implicit_application c =
  let rec aux acc = function
    | [] -> acc
    | e::tl -> aux (ApplicationImplicit (acc, e)) tl in
  aux c


let add_all_to_context = add_to_context true
let add_to_context = add_to_context false

let rec infer_type i constraints env context exp =
  let print () e = 
    try print_expression (get_envt context) e with _ -> "???" in
  let print_in context e =
    try print_expression (get_envt context) e with _ -> "???" in

  let tr = function
    | SType _ as r -> r
    | SDecl _ -> assert false
    | F (e, t) ->
        F (e, lazy (sprintf "%s\nInferring a type for %a."
            (Lazy.force t) print exp)) in

  let failure s = F (s, lazy "") in

  match exp with
  (* pi types *)
  | Pi (Underscore, e1, e2) -> tr (
      infer_type i constraints env context e1
      >>= (function
      | e1, VUniverse j, constraints ->
          infer_type (i + 1) constraints env context e2
          >>= (function
          | e2, VUniverse k, constraints -> SType (Pi (Underscore, e1, e2), VUniverse (max j k), constraints)
          | _ -> failure (sprintf "%a is not a type" print e2))
      | _ -> failure (sprintf "%a is not a type." print e1))
      )
  | Pi (Name x, e1, e2) -> tr (
      infer_type i constraints env context e1
      >>= (function
      | e1, VUniverse j, constraints ->
          let env' = Environment.add env (VNeutral (VVar (x, i))) in
          let context' = Context.add_binder context x (Eval.eval (Equality.get_metavariable_assignment constraints) env e1) in
          infer_type (i + 1) constraints env' context' e2
          >>= (function
          | e2, VUniverse k, constraints -> SType (Pi (Name x, e1, e2), VUniverse (max j k), constraints)
          | _ -> failure (sprintf "%s is not a type." (print_in context' e2)))
      | _ -> failure (sprintf "%a is not a type." print e1)))

  (* implicit pi types *)
  | PiImplicit (x, e1, e2) -> tr (
      infer_type i constraints env context e1
      >>= (function
      | e1, VUniverse j, constraints ->
          let env' = Environment.add env (VNeutral (VVar (x, i))) in
          let context' = Context.add_binder context x (Eval.eval (Equality.get_metavariable_assignment constraints) env e1) in
          infer_type (i + 1) constraints env' context' e2
          >>= (function
          | e2, VUniverse k, constraints -> SType (PiImplicit (x, e1, e2), VUniverse (max j k), constraints)
          | _ -> failure (sprintf "%s is not a type." (print_in context' e2)))
      | _ -> failure (sprintf "%a is not a type." print e1)))

  (* sigma types *)
  | Sigma (Underscore, e1, e2) -> tr (
      infer_type i constraints env context e1
      >>= (function
      | e1, VUniverse j, constraints ->
          infer_type (i + 1) constraints env context e2
          >>= (function
          | e2, VUniverse k, constraints -> SType (Sigma (Underscore, e1, e2), VUniverse (max j k), constraints)
          | _ -> failure (sprintf "%a is not a type" print e2))
      | _ -> failure (sprintf "%a is not a type." print e1)))
  | Sigma (Name x, e1, e2) -> tr (
      infer_type i constraints env context e1
      >>= (function
      | e1, VUniverse j, constraints ->
          let env' = Environment.add env (VNeutral (VVar (x, i))) in
          let context' = Context.add_binder context x (Eval.eval (Equality.get_metavariable_assignment constraints) env e1) in
          infer_type (i + 1) constraints env' context' e2
          >>= (function
          | e2, VUniverse k, constraints -> SType (Sigma (Name x, e1, e2), VUniverse (max j k), constraints)
          | _ -> failure (sprintf "%s is not a type." (print_in context' e2)))
      | _ -> failure (sprintf "%a is not a type." print e1)))

  (* application *)
  | Application (e1, e2) -> tr (
      infer_type i constraints env context e1
      >>= function
        | e1, VArrow (a, b), constraints ->
            check_type i constraints env context e2 a
            >>= fun (e2, _, constraints) ->
            SType (Application (e1, e2), b, constraints)
        | e1, VPi (x, a, b, pi_env), constraints -> 
            check_type i constraints env context e2 a
            >>= fun (e2, _, constraints) ->
            let pi_env' = Environment.add pi_env (Eval.eval (Equality.get_metavariable_assignment constraints) env e2) in
            SType (Application (e1, e2), Eval.eval (Equality.get_metavariable_assignment constraints) pi_env' b, constraints)
        | e1, (VPiImplicit (x, a, b, pi_env)), constraints -> 
            let meta = Abstract.create_implicit_metavariable () in
            let constraints = Equality.add_metavariable constraints (i, context, env) meta a in
            infer_type i constraints env context (Application (ApplicationImplicit (e1, Meta meta), e2))
        | _ ->
            failure (
              sprintf "%a is not a function; it cannot be applied." print e1))

  (* implicit application *)
  | ApplicationImplicit (Constructor c, e2) -> tr (
      match get_unique_constructor_type context c with
      | None ->
          failure
            (sprintf "The constructor \"%s\" does not have a unique type." c)
      | Some (VPiImplicit (x, a, b, pi_env)) ->
            check_type i constraints env context e2 a
            >>= fun (e2, _, constraints) ->
            let pi_env' = Environment.add pi_env (Eval.eval (Equality.get_metavariable_assignment constraints) env e2) in
            SType (ApplicationImplicit (Constructor c, e2), Eval.eval (Equality.get_metavariable_assignment constraints) pi_env' b, constraints)
      | _ -> 
          failure (
              sprintf "%a is not a function with an implicit argument; it cannot be applied implicitly." print (Constructor c)))
  | ApplicationImplicit (e1, e2) -> tr (
      infer_type i constraints env context e1
      >>= function
        | e1, VPiImplicit (x, a, b, pi_env), constraints -> 
            check_type i constraints env context e2 a
            >>= fun (e2, _, constraints) ->
            let pi_env' = Environment.add pi_env (Eval.eval (Equality.get_metavariable_assignment constraints) env e2) in
            SType (ApplicationImplicit (e1, e2), Eval.eval (Equality.get_metavariable_assignment constraints) pi_env' b, constraints)
        | _ ->
            failure (
              sprintf "%a is not a function with an implicit argument; it cannot be applied implicitly." print e1))

  (* universes *)
  | Universe i -> SType (Universe i, VUniverse (i + 1), constraints)

  (* unit *)
  | Unit -> SType (Unit, VUnitType, constraints)
  | UnitType -> SType (UnitType, VUniverse 0, constraints)

  (* de Bruijn indices *)
  | Index j -> (match get_binder_type context j with
      | None ->
          tr (failure (sprintf "The type of index %i is not in the context." j))
      | Some v -> SType (Index j, v, constraints))

  (* projections *)
  | Proj1 e -> tr (
      infer_type i constraints env context e
      >>= function
        | e, VTimes (a, _), constraints -> SType (Proj1 e, a, constraints)
        | e, VSigma (_, a, _, _), constraints -> SType (Proj1 e, a, constraints)
        | _ -> failure (sprintf "%a is not a pair" print e))
  | Proj2 e -> tr (
      infer_type i constraints env context e
      >>= function
        | e, VTimes (_, b), constraints ->
            SType (Proj2 e, b, constraints)
        | e, VSigma (x, a, b, sigma_env), constraints ->
            let sigma_env' =
              Environment.add sigma_env (Eval.eval (Equality.get_metavariable_assignment constraints) env (Proj1 e)) in
            SType (Proj2 e, Eval.eval (Equality.get_metavariable_assignment constraints) sigma_env' b, constraints)
        | _ -> failure (sprintf "%a is not a pair" print e))

  (* metavariables *)
  | Meta id ->
      if Equality.has_metavariable constraints id
      then
        (* TODO: Should the metavariable be replaced if it has been assigned? *)
        SType (Meta id, Equality.get_metavariable constraints id, constraints)
      else failure (sprintf "Cannot infer a type for %a." print exp)

  (* normally a type checking rule -- included for declarations given as part of
   * expressions in the REPL *)
  | LocalDeclaration (d, e) -> tr (
      match check_declarations i constraints env context d with
      | F _ as f -> f
      | SDecl (_, d, _, _, constraints) ->
          let env' = Environment.add_declarations env d in
          let context' = add_all_to_context (Equality.get_metavariable_assignment constraints) env context d in
          infer_type i constraints env' context' e
          >>= fun (e, typ, constraints) ->
          SType (LocalDeclaration (d, e), typ, constraints)
      | SType _ -> assert false)

  (* not needed in type system -- included for constructors given as part of
   * expressions in the REPL *)
  | Constructor c -> (match get_unique_constructor_type context c with
      | None ->
          failure
            (sprintf "The constructor \"%s\" does not have a unique type." c)
      | Some t ->
          SType (Constructor c, t, constraints))

  (* not needed in the type system -- included for pairs given as part of
   * expressions in the REPL *)
  | Pair (e1, e2) -> tr ( 
      infer_type i constraints env context e1
      >>= fun (e1, t1, constraints) ->
      infer_type i constraints env context e2
      >>= fun (e2, t2, constraints) ->
      (* env should not be needed in the next line -- a reified value should not
       * have free variables *)
      try SType (Pair (e1, e2), VTimes (t1, t2), constraints)
      with Cannot_reify _ ->
        failure (sprintf "Cannot convert the type of %a to an expression"
          print e2))

  | _ -> failure (sprintf "Cannot infer a type for %a." print exp)

and check_subtype i constraints a b =
  let check_equal a b constraints = 
    let constraints = Equality.test_equality i constraints a b in
    if Equality.never_satisfied constraints then None else Some constraints in

  let (>>=) c f = match c with
    | Some c -> f c
    | None -> None in
  let check i a b constraints = check_subtype i constraints a b in

  match a, b with
  | VUniverse j, VUniverse k -> if j <= k then Some constraints else None
  | VArrow (a1, b1), VArrow (a2, b2) ->
      Some constraints >>= check_equal a1 a2 >>= check i b1 b2
  | VPi (x1, a1, b1, pi_env1), VPi (x2, a2, b2, pi_env2) ->
      let b1 =
        Eval.eval (Equality.get_metavariable_assignment constraints) (Environment.add pi_env1 (VNeutral (VVar (x1, i)))) b1 in
      let b2 =
        Eval.eval (Equality.get_metavariable_assignment constraints) (Environment.add pi_env2 (VNeutral (VVar (x2, i)))) b2 in
      Some constraints >>= check_equal a1 a2 >>= check (i + 1) b1 b2
  | VPiImplicit (x1, a1, b1, pi_env1), VPiImplicit (x2, a2, b2, pi_env2) ->
      let b1 =
        Eval.eval (Equality.get_metavariable_assignment constraints) (Environment.add pi_env1 (VNeutral (VVar (x1, i)))) b1 in
      let b2 =
        Eval.eval (Equality.get_metavariable_assignment constraints) (Environment.add pi_env2 (VNeutral (VVar (x2, i)))) b2 in
      Some constraints >>= check_equal a1 a2 >>= check (i + 1) b1 b2 
  | VTimes (a1, b1), VTimes (a2, b2) ->
      Some constraints >>= check_equal a1 a2 >>= check i b1 b2
  | VSigma (x1, a1, b1, pi_env1), VSigma (x2, a2, b2, pi_env2) ->
      let b1 =
        Eval.eval (Equality.get_metavariable_assignment constraints) (Environment.add pi_env1 (VNeutral (VVar (x1, i)))) b1 in
      let b2 =
        Eval.eval (Equality.get_metavariable_assignment constraints) (Environment.add pi_env2 (VNeutral (VVar (x2, i)))) b2 in
      Some constraints >>= check_equal a1 a2 >>= check (i + 1) b1 b2
  | _ -> check_equal a b constraints

and check_type i constraints env context exp typ =
  let print_exp () e =
    try print_expression (get_envt context) e with _ -> "???" in
  let print_val () v = 
    try Print_value.string_of_value v with _ -> "???" in
  let print_pattern () p = 
    try print_pattern (get_envt context) p with _ -> "???" in

  let tr = function
    | SType _ as r -> r
    | SDecl _ -> assert false
    | F (e, t) ->
        F (e, lazy (sprintf "%s\nChecking that %a has type %a."
            (Lazy.force t) print_exp exp print_val typ)) in

  let failure s = F (s, lazy "") in

  let try_subtype () = tr (
      infer_type i constraints env context exp
      >>= fun (exp, inferred_type, constraints) ->
      match check_subtype i constraints inferred_type typ with
      | Some constraints -> SType (exp, typ, constraints)
      | None -> failure (sprintf "%a is not a subtype of %a." print_val inferred_type
             print_val typ)) in

  match exp, typ with
  | e, typ when is_implicit_constructor_application e -> (
      let c = get_constructor_from_implicit_application e in
      match get_unique_constructor_type context c with
      | None ->
          failure
            (sprintf "The constructor \"%s\" does not have a unique type." c)
      | Some t ->
          let rec check_implicit_applications constraints env context = function
            | VPiImplicit (x, a, b, pi_env), e::tl -> (
                match check_type i constraints env context e a with
                | SType (e, _, constraints) -> (
                    let pi_env = Environment.add pi_env (Eval.eval (Equality.get_metavariable_assignment constraints) env e) in
                    let b = Eval.eval (Equality.get_metavariable_assignment constraints) pi_env b in
                    match check_implicit_applications constraints env context (b, tl) with
                    | None -> None
                    | Some (l, constraints) -> Some (e::l, constraints))
                | _ -> None)
            | _, _::_ -> None
            | _, tl -> Some (tl, constraints) in
          let apps = get_list_implicit_applications exp in
          let e, target, rest_t, constraints = add_applications constraints (i, context, env) exp typ 
            (strip_implicit_applications constraints env apps t) in
          let l = get_list_implicit_applications e in
          match check_implicit_applications constraints env context (t, l) with
          | None -> failure (sprintf "%a does not have type %a" print_exp exp print_val typ)
          | Some (l, constraints) ->
              match check_subtype i constraints target rest_t with
              | Some constraints -> SType (form_implicit_application (Constructor c) l, typ, constraints)
              | None -> failure (sprintf "%a does not have type %a" print_exp exp print_val typ))

(*
  | Constructor c, typ -> (
      match get_unique_constructor_type context c with
      | None -> 
          failure
            (sprintf "The constructor \"%s\" does not have a unique type." c)
      | Some inferred_type ->
          check_type i constraints env context exp typ)
*)

  (* pairs *)
  | Pair (e1, e2), VTimes (a, b) -> tr (
      check_type i constraints env context e1 a
      >>= fun (e1, _, constraints) ->
      check_type i constraints env context e2 b
      >>= fun (e2, _, constraints) ->
      SType (Pair (e1, e2), typ, constraints))
  | Pair (e1, e2), VSigma (x, a, b, sigma_env) -> tr (
      check_type i constraints env context e1 a
      >>= fun (e1, _, constraints) ->
      let sigma_env' = Environment.add sigma_env (Eval.eval (Equality.get_metavariable_assignment constraints) env e1) in
      check_type i constraints env context e2 (Eval.eval (Equality.get_metavariable_assignment constraints) sigma_env' b)
      >>= fun (e2, _, constraints) ->
      SType (Pair (e1, e2), typ, constraints))

  (* lambda abstractions *)
  | Lambda (Underscore, e1), VArrow (a, b) -> tr (
      check_type i constraints env context e1 b
      >>= fun (e1, _, constraints) ->
      SType (Lambda (Underscore, e1), typ, constraints))
  | Lambda (Underscore, e1), VPi (x, a, b, pi_env) -> tr (
      let pi_env' = Environment.add pi_env (VNeutral (VVar (x, i))) in
      check_type (i + 1) constraints env context e1 (Eval.eval (Equality.get_metavariable_assignment constraints) pi_env' b)
      >>= fun (e1, _, constraints) ->
      SType (Lambda (Underscore, e1), typ, constraints))
  | Lambda (Name x, e1), VArrow (a, b) -> tr (
      let env' = Environment.add env (VNeutral (VVar (x, i))) in
      let context' = Context.add_binder context x a in
      check_type (i + 1) constraints env' context' e1 b
      >>= fun (e1, _, constraints) ->
      SType (Lambda (Name x, e1), typ, constraints))
  | Lambda (Name x, e1), VPi (y, a, b, pi_env) -> tr (
      let env' = Environment.add env (VNeutral (VVar (x, i))) in
      let context' = Context.add_binder context x a in
      let pi_env' = Environment.add pi_env (VNeutral (VVar (y, i))) in
      check_type (i + 1) constraints env' context' e1 (Eval.eval (Equality.get_metavariable_assignment constraints) pi_env' b)
      >>= fun (e1, _, constraints) ->
      SType (Lambda (Name x, e1), typ, constraints))

  (* implicit lambda abstractions *)
  | LambdaImplicit (Underscore, e1), VPiImplicit (x, a, b, pi_env) -> tr (
      let pi_env' = Environment.add pi_env (VNeutral (VVar (x, i))) in
      check_type (i + 1) constraints env context e1 (Eval.eval (Equality.get_metavariable_assignment constraints) pi_env' b)
      >>= fun (e1, _, constraints) ->
      SType (LambdaImplicit (Underscore, e1), typ, constraints))
  | LambdaImplicit (Name x, e1), VPiImplicit (y, a, b, pi_env) -> tr (
      let env' = Environment.add env (VNeutral (VVar (x, i))) in
      let context' = Context.add_binder context x a in
      let pi_env' = Environment.add pi_env (VNeutral (VVar (y, i))) in
      check_type (i + 1) constraints env' context' e1 (Eval.eval (Equality.get_metavariable_assignment constraints) pi_env' b)
      >>= fun (e1, _, constraints) ->
      SType (LambdaImplicit (Name x, e1), typ, constraints))

  (* if the type is an implicit pi type and the expression is not an implicit
   * lambda abstraction, then an implicit lambda abstraction is inserted into
   * the expression *)
  | e, VPiImplicit (x, a, b, pi_env) ->
      tr (check_type i constraints env context (LambdaImplicit (Underscore, e)) typ)

  (* declarations *)
  | LocalDeclaration (d, e), _ -> tr (
      match check_declarations i constraints env context d with
      | SDecl (_, d, _, _, constraints) ->
          let env' = Environment.add_declarations env d in
          let context' = add_all_to_context (Equality.get_metavariable_assignment constraints) env context d in
          check_type i constraints env' context' e typ
          >>= fun (e, typ, constraints) ->
          SType (LocalDeclaration (d, e), typ, constraints)
      | F _ as f -> f
      | SType _ -> assert false)

  (* pattern matching *)
  | Function cases, VArrow (a, b) -> tr (
      let check_case constraints patt exp =
        match Patterns.add_binders
          (fun i constraints context env e v -> 
            match check_type i constraints env context e v with
            | SType (e, _, constraints) -> Some (e, constraints)
            | _ -> None)
          i constraints context env a patt with
        | None -> failure (sprintf
            "The type of the values matched by the pattern %a is not %a."
            print_pattern patt print_val a)
        | Some (_, new_i, constraints, new_context, new_env, subst) ->
            let typ = Context.subst_value subst b in
            check_type new_i constraints new_env new_context exp typ in
      List.fold_left (fun r (p, e) -> r
          >>= fun (func, _, constraints) ->
          match func with
          | Function cases -> 
              check_case constraints p e
              >>= fun (e, a, constraints) ->
              (* the append is inefficient, but the list of cases should be
               * small and I don't want to complicate this bit any more *)
              SType (Function (cases @ [p, e]), a, constraints)
          | _ -> assert false)
        (SType (Function [], a, constraints)) cases
      >>= fun (e, _, constraints) ->
      match Patterns.cover i constraints context (List.map (fun (p, _) -> p) cases) a with
      | None -> SType (e, typ, constraints) (* the patterns cover all cases *)
      | Some v ->
          (* there is no pattern which matches v *)
          failure ("The patterns do not cover all cases.\n"
            ^ (sprintf "Here is an example of a value which is not matched: %a"
            print_val v))
      | exception Patterns.Cannot_pattern_match ->
          failure (sprintf "Cannot pattern match on values of type %a."
            print_val a))
  | Function cases, VPi (x, a, b, pi_env) -> tr (
      let check_case constraints patt exp =
        match Patterns.add_binders
          (fun i constraints context env e v ->
            match check_type i constraints env context e v with
            | SType (e, _, constraints) -> Some (e, constraints)
            | _ -> None)
          i constraints context env a patt with
        | None -> failure (sprintf
            "The type of the values matched by the pattern %a is not %a."
            print_pattern patt print_val a)
        | Some (matched_value, new_i, constraints, new_context, new_env, subst) ->
            let pi_env' =
              Environment.add pi_env matched_value in
            let typ = Context.subst_value subst (Eval.eval (Equality.get_metavariable_assignment constraints) pi_env' b) in
            check_type new_i constraints new_env new_context exp typ in
      List.fold_left (fun r (p, e) -> r
          >>= fun (func, _, constraints) ->
          match func with
          | Function cases -> 
              check_case constraints p e
              >>= fun (e, a, constraints) ->
              (* the append is inefficient, but the list of cases should be
               * small and I don't want to complicate this bit any more *)
              SType (Function (cases @ [p, e]), a, constraints)
          | _ -> assert false)
        (SType (Function [], a, constraints)) cases
      >>= fun (e, _, constraints) ->
      match Patterns.cover i constraints context (List.map (fun (p, _) -> p) cases) a with
      | None -> SType (e, typ, constraints) (* the patterns cover all cases *)
      | Some v ->
          (* there is no pattern which matches v *)
          failure ("The patterns do not cover all cases.\n"
            ^ (sprintf "Here is an example of a value which is not matched: %a"
            print_val v)))

  (* metavariables *)
  | Meta id, typ -> 
      if Equality.has_metavariable constraints id 
      then
        let inferred_type = Equality.get_metavariable constraints id in
        match check_subtype i constraints inferred_type typ with
        | Some constraints ->
            (* TODO: Should the metavariable be replaced if it has been
             * assigned? *)
            SType (Meta id, typ, constraints)
        | None -> tr (failure (sprintf "%a is not a subtype of %a." print_val
            inferred_type print_val typ))
      else 
        let constraints = Equality.add_metavariable constraints (i, context, env) id typ in
        if Equality.never_satisfied constraints
        then tr (failure (sprintf "%a does not have type %a." print_exp (Meta id) print_val typ))
        else SType (Meta id, typ, Equality.add_metavariable constraints (i, context, env) id typ)

  (* application *)
  | Application (e1, e2), t2 -> (match (
        infer_type i constraints env context e2
        >>= fun (e2, t1, constraints) -> (
        try
          check_type i constraints env context e1
            (VArrow (t1, t2))
        with Cannot_reify _ -> failure "")
        >>= fun (e1, _, constraints) ->
        SType (Application (e1, e2), t2, constraints)) with
    | SType _ as r -> r
    | SDecl _ -> assert false 
    | F _ as f -> match try_subtype () with F _ -> f | x -> x)

  (* if all else fails, infer a type for the expression and check if it is a
   * subtype of the type given *)
  | _ -> try_subtype ()
and check_declarations i constraints env context l =
  (* checks that a Π type ends with Type i for some i, and returns i
   * checks for syntactic equality; does not use readback *) 
  let rec get_universe = function
    | Universe i -> Some i
    | Pi (_, _, b) -> get_universe b
    | PiImplicit (_, _, b) -> get_universe b
    | _ -> None in

  let tr x = function
    | SType _ as r -> r
    | SDecl _ -> assert false
    | F (e, t) ->
        F (e, lazy (sprintf "%s\nChecking the declaration of \"%s\"."
            (Lazy.force t) x)) in

  let check_type_family_type constraints env context x typ =
    infer_type i constraints env context typ 
    >>= (function
    | typ, VUniverse j, constraints -> (match get_universe typ with
        | Some k -> SType (typ, VUniverse k, constraints)
        | None ->
            tr x (F (sprintf "\"%s\" is not a family of types." x, lazy "")))
    | _ -> tr x (F (sprintf "\"%s\" is not a family of types." x, lazy ""))) in

  let constructs type_name type_type t =
    let rec flatten acc = function
      | Constructor v -> if v = type_name then Some acc else None
      | Application (e1, e2) -> flatten ((false, e2)::acc) e1
      | ApplicationImplicit (e1, e2) -> flatten ((true, e2)::acc) e1
      | e -> None in
    let rec check acc = function
      | Universe _, [] -> Some acc
      | Pi (_, _, b), (false, e1)::tl -> 
          check (Application (acc, e1)) (b, tl)
      | PiImplicit (_, _, b), (true, e1)::tl -> 
          check (ApplicationImplicit (acc, e1)) (b, tl)
      | PiImplicit (_, _, b), hd::tl -> 
          check (ApplicationImplicit (acc, Meta (create_implicit_metavariable ()))) (b, hd::tl)
      | _ -> None in
    match flatten [] t with
    | None -> None
    | Some l -> check (Constructor type_name) (type_type, l) in

  (* checks that constructor is strictly positive (Dyjber, 2000, section 1) and
   * constructs the type with the given name *)
  let rec strictly_positive type_name type_type = function
    | Constructor t when t = type_name -> Some (Constructor t) 
    | Application _ as typ -> constructs type_name type_type typ
    | Pi (x, a, b) -> (
        match strictly_positive type_name type_type a, strictly_positive type_name type_type b with
        | Some a, Some b -> Some (Pi (x, a, b))
        | None, Some b when does_not_mention type_name a -> Some (Pi (x, a, b))
        | _ -> None)
    | PiImplicit (x, a, b) -> (
        match strictly_positive type_name type_type a, strictly_positive type_name type_type b with
        | Some a, Some b -> Some (PiImplicit (x, a, b))
        | None, Some b when does_not_mention type_name a -> Some (PiImplicit (x, a, b))
        | _ -> None)
    | _ -> None in

  let check_ctor_type i constraints env context type_name type_type type_universe
        constructor_name typ =
    match strictly_positive type_name type_type typ with
    | Some typ ->
      tr type_name (check_type i constraints env context typ type_universe)
      >>= fun (typ, _, constraints) ->
      SType (typ, type_universe, constraints)
    | None ->
      tr type_name
        (F (sprintf "\"%s\" is not a strictly positive constructor of %s"
          constructor_name type_name, lazy "")) in

  let add_parameters i constraints env context =
    List.fold_left
      (fun (i, constraints, env, context) -> function
       | Parameter (x, e) | ParameterImplicit (x, e) -> 
           (i + 1, constraints, Environment.add env (VNeutral (VVar (x, i)))
          , Context.add_binder context x (Eval.eval (Equality.get_metavariable_assignment constraints) env e)))
      (i, constraints, env, context) in
  
  let get_new_context rest_bs rest_cs xs =
    let context =
       List.fold_left (fun c (s, type_name, v)
         -> Context.add_constructor c s type_name v)
         context rest_cs in
    (* assume that everything in xs has the correct type, without actually
     * checking them *)
    let context = add_to_context (Equality.get_metavariable_assignment constraints) env context xs in
    List.fold_right (fun (s, v) c -> Context.add_binder c s v)
      rest_bs context in

  let rec check_decls constraints complete result_ds result_bs result_cs rest_ds rest_bs = function
    | [] -> SDecl (List.rev complete, List.rev result_ds, result_bs, result_cs, constraints)
    | (Let (x, e1, e2))::xs ->
        let decl_env = get_env env rest_ds xs in
        let decl_context = get_new_context rest_bs result_cs xs in
        tr x (infer_type i constraints decl_env decl_context e1)
        >>= (function 
        | e1, VUniverse j, constraints -> 
            let t = Eval.eval (Equality.get_metavariable_assignment constraints) decl_env e1 in
            tr x (check_type i constraints decl_env decl_context e2 t)
            >>= fun (e2, _, constraints) -> 
            check_decls constraints (Let (x, e1, e2)::complete) (Let (x, e1, e2)::result_ds) ((x, t)::result_bs) result_cs rest_ds rest_bs xs
        | _ ->
            tr x (F (sprintf
                "The expression given as the type of \"%s\" is not a type" x
              , lazy "")))
    | (LetRec (x, e1, e2) as d)::xs ->
        let decl_env = get_env env rest_ds xs in
        let decl_env2 = 
          Environment.add_declarations env
            (xs @ (List.rev (d::(filter rest_ds)))) in
        let decl_context = get_new_context rest_bs result_cs xs in
        tr x (infer_type i constraints decl_env decl_context e1)
        >>= (function
        | e1, VUniverse j, constraints ->
            let t = Eval.eval (Equality.get_metavariable_assignment constraints) decl_env e1 in
            let decl_context2 =
              get_new_context ((x, t)::rest_bs) result_cs xs in
            tr x (check_type i constraints decl_env2 decl_context2 e2 t)
            >>= fun (e2, _, constraints) -> 
            check_decls constraints (LetRec (x, e1, e2)::complete) (LetRec (x, e1, e2)::result_ds) ((x, t)::result_bs) result_cs (d::rest_ds)
              ((x, t)::rest_bs) xs
        | _ ->
            tr x (F (sprintf
                "The expression given as the type of \"%s\" is not a type" x
              , lazy "")))
    | (Type (x, ps, e, constructor_types) as type_decl)::xs ->
        let decl_env = get_env env rest_ds xs in
        let decl_context = get_new_context rest_bs result_cs xs in
        let typefam_type = get_full_type false ps e in
        tr x (check_type_family_type constraints decl_env decl_context x typefam_type) 
        >>= (function
        | typefam_type, (VUniverse j as type_universe), constraints ->
            let eval_typefam_type = Eval.eval (Equality.get_metavariable_assignment constraints) decl_env typefam_type in
            let universe_name = "Type " ^ (string_of_int j) in
            let (constructor_i, constraints, constructor_env, constructor_context) =
              add_parameters i constraints decl_env (Context.add_constructor
                decl_context x universe_name eval_typefam_type) ps in
            let check_ctor_type constraints (c, e) =
              check_ctor_type constructor_i constraints constructor_env constructor_context
                x typefam_type type_universe c e in
            let failure = ref (F ("", lazy "")) in (
            match List.fold_left (fun r (c, t) -> match r with
              | None -> None
              | Some (tl, constraints) -> (
                  match check_ctor_type constraints (c, t) with
                  | SType (t, _, constraints) ->
                      Some ((c, t)::tl, constraints)
                  | F _ as f -> failure := f; None
                  | _ -> assert false))
              (Some ([], constraints)) constructor_types with
            | None -> !failure 
            | Some (constructor_types, constraints) ->
              let result_cs =
                (x, universe_name, eval_typefam_type) :: result_cs in
              let result_cs =
                List.fold_left (fun l (c, e) ->
                    (c, x, Eval.eval (Equality.get_metavariable_assignment constraints) decl_env (get_full_type true ps e))::l)
                  result_cs constructor_types in
              check_decls constraints (type_decl::complete) result_ds result_bs result_cs rest_ds rest_bs xs)
        | _ -> assert false) in

  match Termination.check_termination env l with
  | Some x ->
      tr x (F (sprintf "The declaration of %s might not terminate." x, lazy ""))
  | None -> check_decls constraints [] [] [] [] [] [] l
  | exception (Termination.Cannot_check_termination (x, y)) -> 
      tr x (F (sprintf "Cannot check if the declaration of %s terminates. %s"
        x y, lazy ""))

let () = Equality.checker := fun (i, context, env) constraints exp typ -> 
  let result = check_type i constraints env context exp typ in
  if succeeded result then Some (get_constraints result) else None

let keep_constraints = ref false

let rec subst_implicit_metas c = function
  | Pair (e1, e2) ->
      Pair (subst_implicit_metas c e1, subst_implicit_metas c e2)
  | Lambda (b, e) ->
      Lambda (b, subst_implicit_metas c e)
  | LambdaImplicit (b, e) ->
      LambdaImplicit (b, subst_implicit_metas c e)
  | Pi (b, e1, e2) ->
      Pi (b, subst_implicit_metas c e1, subst_implicit_metas c e2)
  | PiImplicit (b, e1, e2) ->
      PiImplicit (b, subst_implicit_metas c e1, subst_implicit_metas c e2)
  | Sigma (b, e1, e2) ->
      Sigma (b, subst_implicit_metas c e1, subst_implicit_metas c e2)
  | Function l -> Function (List.map (fun (p, e) -> (p, subst_implicit_metas c e)) l)
  | LocalDeclaration (d, e) -> LocalDeclaration (List.map (subst_implicit_metas_decl c) d, subst_implicit_metas c e)
  | Application (e1, e2) -> Application (subst_implicit_metas c e1, subst_implicit_metas c e2)
  | ApplicationImplicit (e1, e2) -> ApplicationImplicit (subst_implicit_metas c e1, subst_implicit_metas c e2)
  | Universe i -> Universe i
  | UnitType -> UnitType
  | Unit -> Unit
  | Index i -> Index i
  | Constructor c -> Constructor c
  | Proj1 e -> Proj1 (subst_implicit_metas c e)
  | Proj2 e -> Proj2 (subst_implicit_metas c e)
  | Meta id ->
      if is_implicit id then
        match Equality.get_metavariable_assignment c id with
        | Some v -> (
            try reify (Eval.eval (Equality.get_metavariable_assignment c)) v
            with Cannot_reify _ -> keep_constraints := true; Meta id)
        | None -> raise Unsolved_implicit_metavariable
      else Meta id
and subst_implicit_metas_decl c = function
  | Let (x, e1, e2) -> Let (x, subst_implicit_metas c e1, subst_implicit_metas c e2)
  | LetRec (x, e1, e2) -> LetRec (x, subst_implicit_metas c e1, subst_implicit_metas c e2)
  | Type (x, ps, e, cs) -> Type (x, List.map (subst_implicit_metas_param c) ps, subst_implicit_metas c e, List.map (fun (x, e) -> (x, subst_implicit_metas c e)) cs)
and subst_implicit_metas_param c = function
  | Parameter (b, e) -> Parameter (b, subst_implicit_metas c e)
  | ParameterImplicit (b, e) -> ParameterImplicit (b, subst_implicit_metas c e)

let rec subst_implicit_metas_value c = function
  | VPair (v1, v2) -> VPair (subst_implicit_metas_value c v1, subst_implicit_metas_value c v2)
  | VLambda (b, e, env) -> VLambda (b, subst_implicit_metas c e, subst_implicit_metas_env c env)
  | VLambdaImplicit (b, e, env) -> VLambdaImplicit (b, subst_implicit_metas c e, subst_implicit_metas_env c env)
  | VPi (s, v, e, env) -> VPi (s, subst_implicit_metas_value c v, subst_implicit_metas c e, subst_implicit_metas_env c env)
  | VPiImplicit (s, v, e, env) -> VPiImplicit (s, subst_implicit_metas_value c v, subst_implicit_metas c e, subst_implicit_metas_env c env)
  | VArrow (v1, v2) -> VArrow (subst_implicit_metas_value c v1, subst_implicit_metas_value c v2)
  | VSigma (s, v, e, env) -> VSigma (s, subst_implicit_metas_value c v, subst_implicit_metas c e, subst_implicit_metas_env c env)
  | VTimes (v1, v2) -> VTimes (subst_implicit_metas_value c v1, subst_implicit_metas_value c v2)
  | VFunction (l, env) -> VFunction (List.map (fun (p, e) -> (p, subst_implicit_metas c e)) l, subst_implicit_metas_env c env)
  | VUniverse i -> VUniverse i
  | VUnit -> VUnit 
  | VUnitType -> VUnitType
  | VConstruct (x, l) -> VConstruct (x, List.map (fun (b, v) -> (b, subst_implicit_metas_value c v)) l) 
  | VNeutral n -> subst_implicit_metas_neutral c n
and subst_implicit_metas_neutral c = function
  | VVar (x, i) -> VNeutral (VVar (x, i))
  | VFunctionApplication (l, env, v) ->
      VNeutral (VFunctionApplication (List.map (fun (p, e) -> (p, subst_implicit_metas c e)) l, subst_implicit_metas_env c env, subst_implicit_metas_value c v))
  | VFunctionApplicationImplicit (l, env, v) ->
      VNeutral (VFunctionApplicationImplicit (List.map (fun (p, e) -> (p, subst_implicit_metas c e)) l, subst_implicit_metas_env c env, subst_implicit_metas_value c v))
  | VApplication (x, y) -> (
      let x = subst_implicit_metas_neutral c x in
      let y = subst_implicit_metas_value c y in
      match x with
      | VConstruct (c, l) -> VConstruct (c, (false, y)::l)
      | VLambda (Underscore, e, env) ->
          Eval.eval (Equality.get_metavariable_assignment c) env e
      | VLambda (Name x, e, env) ->
          let env' = Environment.add env y in
          Eval.eval (Equality.get_metavariable_assignment c) env' e
      | VNeutral x -> VNeutral (VApplication (x, y))
      | _ -> assert false)
  | VApplicationImplicit (x, y) -> (
      let x = subst_implicit_metas_neutral c x in
      let y = subst_implicit_metas_value c y in
      match x with
      | VConstruct (c, l) -> VConstruct (c, (true, y)::l)
      | VLambdaImplicit (Underscore, e, env) ->
          Eval.eval (Equality.get_metavariable_assignment c) env e
      | VLambdaImplicit (Name x, e, env) ->
          let env' = Environment.add env y in
          Eval.eval (Equality.get_metavariable_assignment c) env' e
      | VNeutral x -> VNeutral (VApplication (x, y))
      | _ -> assert false) 
   | VProj1 n -> (
      match subst_implicit_metas_neutral c n with
      | VPair (x, _) -> x
      | VNeutral n -> VNeutral (VProj1 n)
      | _ -> assert false)
   | VProj2 n -> (
      match subst_implicit_metas_neutral c n with
      | VPair (_, y) -> y
      | VNeutral n -> VNeutral (VProj2 n)
      | _ -> assert false)
   | VMeta id ->
      if is_implicit id then
        match Equality.get_metavariable_assignment c id with
        | Some v -> v 
        | None -> raise Unsolved_implicit_metavariable
      else VNeutral (VMeta id)
and subst_implicit_metas_env c env = Environment.map (subst_implicit_metas_value c) (List.map (subst_implicit_metas_decl c)) env

let get_unsolved_metavariables_message constraints =
  sprintf "Some metavariables for implicit arguments were unsolved.\n%s"
    (Equality.string_of_constraints constraints)

let infer_type constraints env context exp =
  infer_type 0 constraints env context exp
  >>= fun (exp, typ, constraints) ->
  try
    let exp = subst_implicit_metas constraints exp in 
    let typ = subst_implicit_metas_value constraints typ in
    SType (exp, typ, if !keep_constraints then constraints else Equality.remove_implicit_metavariables constraints)
  with Unsolved_implicit_metavariable ->
    F (get_unsolved_metavariables_message constraints, lazy "") 
let check_type constraints env context exp typ =
  check_type 0 constraints env context exp typ
  >>= fun (exp, typ, constraints) ->
  try
    let exp = subst_implicit_metas constraints exp in 
    let typ = subst_implicit_metas_value constraints typ in
    SType (exp, typ, if !keep_constraints then constraints else Equality.remove_implicit_metavariables constraints)
  with Unsolved_implicit_metavariable ->
    F (get_unsolved_metavariables_message constraints, lazy "") 
let check_declarations constraints env context decls =
  match check_declarations 0 constraints env context decls with
  | SType _ -> assert false
  | SDecl (d, decls, types, constructors, constraints) -> (
      try
        let decls = List.map (subst_implicit_metas_decl constraints) decls in
        let types = List.map (fun (x, v) -> (x, subst_implicit_metas_value constraints v)) types in
        let constructors = List.map (fun (x, y, v) -> (x, y, subst_implicit_metas_value constraints v)) constructors in
        SDecl (d, decls, types, constructors, if !keep_constraints then constraints else Equality.remove_implicit_metavariables constraints)
      with Unsolved_implicit_metavariable ->
        F (get_unsolved_metavariables_message constraints, lazy ""))
  | F _ as f -> f


