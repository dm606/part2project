open Printf

open Abstract
open Context
open Value

type typing_result =
  | SType of value * Equality.constraints
  | SDecl of (string * value) list * (string * string * value) list
             * Equality.constraints
  | F of string * string Lazy.t

(* these aren't quite the normal monad operations, but they are close *)
let (>>) r f = match r with
  | F _ -> r
  | SDecl (_, _, constraints) -> f constraints
  | SType (_, constraints) -> f constraints

let (>>=) r f = match r with
  | F _ -> r
  | SDecl _ -> assert false
  | SType (t, constraints) -> f (t, constraints)

let succeeded = function
  | SType _ | SDecl _ -> true 
  | F _ -> false

let get_type = function
  | SType (t, _) -> t
  | F _ | SDecl _ -> raise (Failure "get_type")

let get_binder_types = function
  | SDecl (l, _, _) -> l
  | F _ | SType _ -> raise (Failure "get_binder_types")

let get_constructor_types = function
  | SDecl (_, l, _) -> l
  | F _ | SType _ -> raise (Failure "get_constructor_types")

let get_constraints = function
  | SType (_, c) -> c
  | SDecl (_, _, c) -> c
  | F _ -> raise (Failure "get_constraints")

let print_error outchan = function
  | SType _ | SDecl _ -> raise (Failure "print_error")
  | F (e, _) -> fprintf outchan "%s\n" e

let print_trace outchan = function
  | SType _ | SDecl _ -> raise (Failure "print_trace")
  | F (_, t) -> fprintf outchan "%s\n" (Lazy.force t) 

let get_envt context =
    mk_env (get_binder_names context, get_constructor_names context)

let get_full_type ps e =
  List.fold_right (fun (x, t1) t2 -> Pi (x, t1, t2)) ps e

let filter = List.filter (function
    | LetRec (_, _, _) -> true
    | _ -> false)

let get_env env rest_ds xs =
    Environment.add_declarations env (xs @ (List.rev (filter rest_ds)))

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
            (lazy (Eval.eval metavars (get_env env rest_ds xs) (get_full_type ps e))) in
        let context =
          List.fold_left (fun context (c, e) -> Context.add_lazy_constructor
              context c x
              (lazy (Eval.eval metavars (get_env env rest_ds xs) (get_full_type ps e))))
            context cs in
        add context rest_ds xs in
    add context []

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
  | Pi (Underscore, e1, e2) -> tr (
      infer_type i constraints env context e1
      >>= (function
      | VUniverse j, constraints ->
          infer_type (i + 1) constraints env context e2
          >>= (function
          | VUniverse k, constraints -> SType (VUniverse (max j k), constraints)
          | _ -> failure (sprintf "%a is not a type" print e2))
      | _ -> failure (sprintf "%a is not a type." print e1)))
  | Pi (Name x, e1, e2) -> tr (
      infer_type i constraints env context e1
      >>= (function
      | VUniverse j, constraints ->
          let env' = Environment.add env (VNeutral (VVar (x, i))) in
          let context' = Context.add_binder context x (Eval.eval (Equality.get_metavariable_assignment constraints) env e1) in
          infer_type (i + 1) constraints env' context' e2
          >>= (function
          | VUniverse k, constraints -> SType (VUniverse (max j k), constraints)
          | _ -> failure (sprintf "%s is not a type." (print_in context' e2)))
      | _ -> failure (sprintf "%a is not a type." print e1)))
  | Sigma (Underscore, e1, e2) -> tr (
      infer_type i constraints env context e1
      >>= (function
      | VUniverse j, constraints ->
          infer_type (i + 1) constraints env context e2
          >>= (function
          | VUniverse k, constraints -> SType (VUniverse (max j k), constraints)
          | _ -> failure (sprintf "%a is not a type" print e2))
      | _ -> failure (sprintf "%a is not a type." print e1)))
  | Sigma (Name x, e1, e2) -> tr (
      infer_type i constraints env context e1
      >>= (function
      | VUniverse j, constraints ->
          let env' = Environment.add env (VNeutral (VVar (x, i))) in
          let context' = Context.add_binder context x (Eval.eval (Equality.get_metavariable_assignment constraints) env e1) in
          infer_type (i + 1) constraints env' context' e2
          >>= (function
          | VUniverse k, constraints -> SType (VUniverse (max j k), constraints)
          | _ -> failure (sprintf "%s is not a type." (print_in context' e2)))
      | _ -> failure (sprintf "%a is not a type." print e1)))
  | Application (e1, e2) -> tr (
      infer_type i constraints env context e1
      >>= function
        | VArrow (a, b), constraints ->
            check_type i constraints env context e2 a
            >>= fun (_, constraints) ->
            SType (b, constraints)
        | VPi (x, a, b, pi_env), constraints -> 
            check_type i constraints env context e2 a
            >>= fun (_, constraints) ->
            let pi_env' = Environment.add pi_env (Eval.eval (Equality.get_metavariable_assignment constraints) env e2) in
            SType (Eval.eval (Equality.get_metavariable_assignment constraints) pi_env' b, constraints)
        | _ ->
            failure (
              sprintf "%a is not a function; it cannot be applied." print e1))
  | Universe i -> SType (VUniverse (i + 1), constraints)
  | Unit -> SType (VUnitType, constraints)
  | UnitType -> SType (VUniverse 0, constraints)
  | Index j -> (match get_binder_type context j with
      | None ->
          tr (failure (sprintf "The type of index %i is not in the context." j))
      | Some v -> SType (v, constraints))
  | Proj1 e -> tr (
      infer_type i constraints env context e
      >>= function
        | VTimes (a, _), constraints -> SType (a, constraints)
        | VSigma (_, a, _, _), constraints -> SType (a, constraints)
        | _ -> failure (sprintf "%a is not a pair" print e))
  | Proj2 e -> tr (
      infer_type i constraints env context e
      >>= function
        | VTimes (_, b), constraints ->
            SType (b, constraints)
        | VSigma (x, a, b, sigma_env), constraints ->
            let sigma_env' =
              Environment.add sigma_env (Eval.eval (Equality.get_metavariable_assignment constraints) env (Proj1 e)) in
            SType (Eval.eval (Equality.get_metavariable_assignment constraints) sigma_env' b, constraints)
        | _ -> failure (sprintf "%a is not a pair" print e))
  | Meta id -> 
      if Equality.has_metavariable constraints id
      then SType (Equality.get_metavariable constraints id, constraints)
      else failure (sprintf "Cannot infer a type for %a." print exp)

  (* normally a type checking rule -- included for declarations given as part of
   * expressions in the REPL *)
  | LocalDeclaration (d, e) -> tr (
      check_declarations i constraints env context d
      >> fun constraints ->
      let env' = Environment.add_declarations env d in
      let context' = add_all_to_context (Equality.get_metavariable_assignment constraints) env context d in
      tr (infer_type i constraints env' context' e))

  (* not needed in type system -- included for constructors given as part of
   * expressions in the REPL *)
  | Constructor c -> (match get_unique_constructor_type context c with
      | None ->
          failure
            (sprintf "The constructor \"%s\" does not have a unique type." c)
      | Some t -> SType (t, constraints))

  (* not needed in the type system -- included for pairs given as part of
   * expressions in the REPL *)
  | Pair (e1, e2) -> tr ( 
      infer_type i constraints env context e1
      >>= fun (t1, constraints) ->
      infer_type i constraints env context e2
      >>= fun (t2, constraints) ->
      (* env should not be needed in the next line -- a reified value should not
       * have free variables *)
      try SType (VTimes (t1, t2), constraints)
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
      >>= fun (inferred_type, constraints) ->
      match check_subtype i constraints inferred_type typ with
      | Some constraints -> SType (typ, constraints)
      | None -> failure (sprintf "%a is not a subtype of %a." print_val inferred_type
             print_val typ)) in

  match exp, typ with
  | Pair (e1, e2), VTimes (a, b) -> tr (
      check_type i constraints env context e1 a
      >>= fun (_, constraints) ->
      check_type i constraints env context e2 b
      >>= fun (_, constraints) ->
      SType (typ, constraints))
  | Pair (e1, e2), VSigma (x, a, b, sigma_env) -> tr (
      check_type i constraints env context e1 a
      >>= fun (_, constraints) ->
      let sigma_env' = Environment.add sigma_env (Eval.eval (Equality.get_metavariable_assignment constraints) env e1) in
      check_type i constraints env context e2 (Eval.eval (Equality.get_metavariable_assignment constraints) sigma_env' b)
      >>= fun (_, constraints) ->
      SType (typ, constraints))
  | Lambda (Underscore, e1), VArrow (a, b) -> tr (
      check_type i constraints env context e1 b
      >>= fun (_, constraints) ->
      SType (typ, constraints))
  | Lambda (Underscore, e1), VPi (x, a, b, pi_env) -> tr (
      let pi_env' = Environment.add pi_env (VNeutral (VVar (x, i))) in
      check_type (i + 1) constraints env context e1 (Eval.eval (Equality.get_metavariable_assignment constraints) pi_env' b)
      >>= fun (_, constraints) ->
      SType (typ, constraints))
  | Lambda (Name x, e1), VArrow (a, b) -> tr (
      let env' = Environment.add env (VNeutral (VVar (x, i))) in
      let context' = Context.add_binder context x a in
      check_type (i + 1) constraints env' context' e1 b
      >>= fun (_, constraints) ->
      SType (typ, constraints))
  | Lambda (Name x, e1), VPi (y, a, b, pi_env) -> tr (
      let env' = Environment.add env (VNeutral (VVar (x, i))) in
      let context' = Context.add_binder context x a in
      let pi_env' = Environment.add pi_env (VNeutral (VVar (y, i))) in
      check_type (i + 1) constraints env' context' e1 (Eval.eval (Equality.get_metavariable_assignment constraints) pi_env' b)
      >>= fun (_, constraints) ->
      SType (typ, constraints))
  | Constructor c, _ -> ( 
      match check_constructor_type context constraints c typ with
      | Some constraints when not (Equality.never_satisfied constraints) ->
          SType (typ, constraints)
      | _ ->
          tr (failure (sprintf "\"%s\" does not have type %a."
            c print_val typ)))
  | LocalDeclaration (d, e), _ -> tr (
      check_declarations i constraints env context d
      >> fun constraints ->
      let env' = Environment.add_declarations env d in
      let context' = add_all_to_context (Equality.get_metavariable_assignment constraints) env context d in
      check_type i constraints env' context' e typ)
  | Function cases, VArrow (a, b) -> tr (
      let check_case constraints patt exp =
        match Patterns.add_binders
          (fun i constraints context env e v -> 
            match check_type i constraints env context e v with
            | SType (_, constraints) -> Some constraints
            | _ -> None)
          i constraints context env a patt with
        | None -> failure (sprintf
            "The type of the values matched by the pattern %a is not %a."
            print_pattern patt print_val a)
        | Some (_, new_i, constraints, new_context, new_env, subst) ->
            let typ = Context.subst_value subst b in
            check_type new_i constraints new_env new_context exp typ in
      List.fold_left (fun r (p, e) -> r
          >>= fun (_, constraints) ->
          check_case constraints p e)
        (SType (a, constraints)) cases
      >>= fun (_, constraints) ->
      match Patterns.cover i constraints context (List.map (fun (p, _) -> p) cases) a with
      | None -> SType (typ, constraints) (* the patterns cover all cases *)
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
            | SType (_, constraints) -> Some constraints
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
          >>= fun (_, constraints) ->
          check_case constraints p e)
        (SType (a, constraints)) cases
      >>= fun (_, constraints) ->
      match Patterns.cover i constraints context (List.map (fun (p, _) -> p) cases) a with
      | None -> SType (typ, constraints) (* the patterns cover all cases *)
      | Some v ->
          (* there is no pattern which matches v *)
          failure ("The patterns do not cover all cases.\n"
            ^ (sprintf "Here is an example of a value which is not matched: %a"
            print_val v)))
  | Meta id, typ -> 
      if Equality.has_metavariable constraints id 
      then
        let inferred_type = Equality.get_metavariable constraints id in
        match check_subtype i constraints inferred_type typ with
        | Some constraints -> SType (typ, constraints)
        | None -> tr (failure (sprintf "%a is not a subtype of %a." print_val
            inferred_type print_val typ))
      else 
        SType (typ, Equality.add_metavariable constraints id typ)


  (* not normally a type checking rule -- included because we cannot infer types
   * for lamdba abstractions or pattern-matching functions, but type inference
   * for application requires inference of the function being applied *)
  | Application (e1, e2), t2 -> (match (
        infer_type i constraints env context e2
        >>= fun (t1, constraints) -> (
        try
          check_type i constraints env context e1
            (VArrow (t1, t2))
        with Cannot_reify _ -> failure "")
        >> fun constraints ->
        SType (t2, constraints)) with
    | SType _ as r -> r
    | SDecl _ -> assert false 
    | F _ -> try_subtype ())

  | _ -> try_subtype ()
and check_declarations i constraints env context l =
  (* checks that a Π type ends with Type i for some i, and returns i
   * checks for syntactic equality; does not use readback *) 
  let rec get_universe = function
    | Universe i -> Some i
    | Pi (_, _, b) -> get_universe b
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
    | VUniverse j, constraints -> (match get_universe typ with
        | Some k -> SType (VUniverse k, constraints)
        | None ->
            tr x (F (sprintf "\"%s\" is not a family of types." x, lazy "")))
    | _ -> tr x (F (sprintf "\"%s\" is not a family of types." x, lazy ""))) in

  let rec constructs type_name type_type t = match type_type, t with
    | Universe _, Constructor n when n = type_name -> true
    | Pi (_, _, b), Application (e1, _) -> constructs type_name b e1
    | _ -> false in

  (* checks that constructor is strictly positive (Dyjber, 2000, section 1) and
   * constructs the type with the given name *)
  let rec strictly_positive type_name type_type = function
    | Constructor t when t = type_name -> true
    | Application _ as typ -> constructs type_name type_type typ
    | Pi (_, a, b) ->
        (strictly_positive type_name type_type a
         || does_not_mention type_name a)
        && strictly_positive type_name type_type b
    | _ -> false in

  let check_ctor_type i constraints env context type_name type_type type_universe
        constructor_name typ =
    if strictly_positive type_name type_type typ then
      tr type_name (check_type i constraints env context typ type_universe)
      >>= fun (_, constraints) ->
      SType (type_universe, constraints)
    else
      tr type_name
        (F (sprintf "\"%s\" is not a strictly positive constructor of %s"
          constructor_name type_name, lazy "")) in

  let add_parameters i constraints env context =
    List.fold_left
      (fun (i, constraints, env, context) -> function
       | Underscore, _ -> (i, constraints, env, context)
       | Name x, e -> 
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

  let rec check_decls constraints result_bs result_cs rest_ds rest_bs = function
    | [] -> SDecl (result_bs, result_cs, constraints)
    | (Let (x, e1, e2))::xs ->
        let decl_env = get_env env rest_ds xs in
        let decl_context = get_new_context rest_bs result_cs xs in
        tr x (infer_type i constraints decl_env decl_context e1)
        >>= (function 
        | VUniverse j, constraints -> 
            let t = Eval.eval (Equality.get_metavariable_assignment constraints) decl_env e1 in
            tr x (check_type i constraints decl_env decl_context e2 t)
            >>= fun (_, constraints) -> 
            check_decls constraints ((x, t)::result_bs) result_cs rest_ds rest_bs xs
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
        | VUniverse j, constraints ->
            let t = Eval.eval (Equality.get_metavariable_assignment constraints) decl_env e1 in
            let decl_context2 =
              get_new_context ((x, t)::rest_bs) result_cs xs in
            tr x (check_type i constraints decl_env2 decl_context2 e2 t)
            >>= fun (_, constraints) -> 
            check_decls constraints ((x, t)::result_bs) result_cs (d::rest_ds)
              ((x, t)::rest_bs) xs
        | _ ->
            tr x (F (sprintf
                "The expression given as the type of \"%s\" is not a type" x
              , lazy "")))
    | (Type (x, ps, e, constructor_types))::xs ->
        let decl_env = get_env env rest_ds xs in
        let decl_context = get_new_context rest_bs result_cs xs in
        let typefam_type = get_full_type ps e in
        tr x (check_type_family_type constraints decl_env decl_context x typefam_type) 
        >>= (function
        | (VUniverse j as type_universe), constraints ->
            let eval_typefam_type = Eval.eval (Equality.get_metavariable_assignment constraints) decl_env typefam_type in
            let universe_name = "Type " ^ (string_of_int j) in
            let (constructor_i, constraints, constructor_env, constructor_context) =
              add_parameters i constraints decl_env (Context.add_constructor
                decl_context x universe_name eval_typefam_type) ps in
            let check_ctor_type (c, e) =
              check_ctor_type constructor_i constraints constructor_env constructor_context
                x typefam_type type_universe c e in
            List.fold_left
              (fun result p -> result >>= fun (_, constraints) -> check_ctor_type p)
              (SType (type_universe, constraints)) constructor_types 
            >>= fun (_, constraints) ->
            let result_cs =
              (x, universe_name, eval_typefam_type) :: result_cs in
            let result_cs =
              List.fold_left (fun l (c, e) ->
                  (c, x, Eval.eval (Equality.get_metavariable_assignment constraints) decl_env (get_full_type ps e))::l)
                result_cs constructor_types in
            check_decls constraints result_bs result_cs rest_ds rest_bs xs
        | _ -> assert false) in

  match Termination.check_termination env l with
  | Some x ->
      tr x (F (sprintf "The declaration of %s might not terminate." x, lazy ""))
  | None -> check_decls constraints [] [] [] [] l
  | exception (Termination.Cannot_check_termination (x, y)) -> 
      tr x (F (sprintf "Cannot check if the declaration of %s terminates. %s"
        x y, lazy ""))


let infer_type = infer_type 0
let check_type = check_type 0
let check_declarations = check_declarations 0
