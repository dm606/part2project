open Printf

open Abstract
open Context
open Value

type typing_result =
  | SType of value
  | SDecl of (string * value) list * (string * string * value) list
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

let get_full_type ps e =
  List.fold_right (fun (x, t1) t2 -> Pi (x, t1, t2)) ps e

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
        let context = Context.remove_constructors_of_type context x in
        let context =
          Context.add_lazy_constructor context x "U"
            (lazy (Eval.eval (get_env env rest_ds xs) (get_full_type ps e))) in
        let context =
          List.fold_left (fun context (c, e) -> Context.add_lazy_constructor
              context c x
              (lazy (Eval.eval (get_env env rest_ds xs) (get_full_type ps e))))
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
        | VArrow (a, b) ->
            check_type i env context e2 a
            >>= fun _ ->
            SType b 
        | VPi (x, a, b, pi_env) -> 
            check_type i env context e2 a
            >>= fun _ ->
            let pi_env' = Environment.add pi_env (Eval.eval env e2) in
            SType (Eval.eval pi_env' b)
        | _ ->
            failure (
              sprintf "%a is not a function; it cannot be applied." print e1))
  | Universe -> SType VUniverse
  | Unit -> SType VUnitType
  | UnitType -> SType VUniverse
  | Index j -> (match get_binder_type context j with
      | None ->
          tr (failure (sprintf "The type of index %i is not in the context." j))
      | Some v -> SType v)
  | Proj1 e -> tr (
      infer_type i env context e
      >>= function
        | VTimes (a, _) -> SType a
        | VSigma (_, a, _, _) -> SType a
        | _ -> failure (sprintf "%a is not a pair" print e))
  | Proj2 e -> tr (
      infer_type i env context e
      >>= function
        | VTimes (_, b) ->
            SType b
        | VSigma (x, a, b, sigma_env) ->
            let sigma_env' =
              Environment.add sigma_env (Eval.eval env (Proj1 e)) in
            SType (Eval.eval sigma_env' b)
        | _ -> failure (sprintf "%a is not a pair" print e))
  
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
      try SType (VTimes (t1, t2))
      with Cannot_reify _ ->
        failure (sprintf "Cannot convert the type of %a to an expression"
          print e2))

  | _ -> failure (sprintf "Cannot infer a type for %a." print exp)

and check_type i env context exp typ =
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

  let try_eq () = tr (
      infer_type i env context exp
      >>= fun inferred_type ->
      if (Equality.readback i inferred_type) = (Equality.readback i typ)
      then SType typ
      else failure (sprintf "%a is not equal to %a." print_val inferred_type
             print_val typ)) in

  match exp, typ with
  | Pair (e1, e2), VTimes (a, b) -> tr (
      check_type i env context e1 a
      >>= fun _ ->
      check_type i env context e2 b
      >>= fun _ ->
      SType typ)
  | Pair (e1, e2), VSigma (x, a, b, sigma_env) -> tr (
      check_type i env context e1 a
      >>= fun _ ->
      let sigma_env' = Environment.add sigma_env (Eval.eval env e1) in
      check_type i env context e2 (Eval.eval sigma_env' b)
      >>= fun _ ->
      SType typ)
  | Lambda (Underscore, e1), VArrow (a, b) -> tr (
      check_type i env context e1 b
      >>= fun _ ->
      SType typ)
  | Lambda (Underscore, e1), VPi (x, a, b, pi_env) -> tr (
      let pi_env' = Environment.add pi_env (VNeutral (VVar i)) in
      check_type (i + 1) env context e1 (Eval.eval pi_env' b)
      >>= fun _ ->
      SType typ)
  | Lambda (Name x, e1), VArrow (a, b) -> tr (
      let env' = Environment.add env (VNeutral (VVar i)) in
      let context' = Context.add_binder context x a in
      check_type (i + 1) env' context' e1 b
      >>= fun _ ->
      SType typ)
  | Lambda (Name x, e1), VPi (y, a, b, pi_env) -> tr (
      let env' = Environment.add env (VNeutral (VVar i)) in
      let context' = Context.add_binder context x a in
      let pi_env' = Environment.add pi_env (VNeutral (VVar i)) in
      check_type (i + 1) env' context' e1 (Eval.eval pi_env' b)
      >>= fun _ ->
      SType typ)
  | Constructor c, _ -> 
      if check_constructor_type context c typ
      then SType typ
      else
        tr (failure (sprintf "\"%s\" does not have type %a." c print_val typ))
  | LocalDeclaration (d, e), _ -> tr (
      check_declarations i env context d
      >> fun _ ->
      let env' = Environment.add_declarations env d in
      let context' = add_all_to_context env context d in
      check_type i env' context' e typ)
  | Function cases, VArrow (a, b) -> tr (
      let check_case patt exp =
        match Patterns.add_binders
          (fun i context env e v -> succeeded (check_type i env context e v))
          i context env a patt with
        | None -> failure (sprintf
            "The type of the values matched by the pattern %a is not %a."
            print_pattern patt print_val a)
        | Some (_, new_i, new_context, new_env, subst) ->
            let typ = Context.subst_value subst b in
            check_type new_i new_env new_context exp typ in
      List.fold_left (fun r (p, e) -> r >>= fun _ -> check_case p e)
        (SType a) cases
      >>= fun _ ->
      if Patterns.cover i context (List.map (fun (p, _) -> p) cases) a
      then SType typ
      else failure (sprintf "The patterns do not cover all cases"))
  | Function cases, VPi (x, a, b, pi_env) -> tr (
      let check_case patt exp =
        match Patterns.add_binders
          (fun i context env e v -> succeeded (check_type i env context e v))
          i context env a patt with
        | None -> failure (sprintf
            "The type of the values matched by the pattern %a is not %a."
            print_pattern patt print_val a)
        | Some (matched_value, new_i, new_context, new_env, subst) ->
            let pi_env' =
              Environment.add pi_env matched_value in
            let typ = Context.subst_value subst (Eval.eval pi_env' b) in
            check_type new_i new_env new_context exp typ in
      List.fold_left (fun r (p, e) -> r >>= fun _ -> check_case p e)
        (SType a) cases
      >>= fun _ ->
      if Patterns.cover i context (List.map (fun (p, _) -> p) cases) a
      then SType typ
      else failure (sprintf "The patterns do not cover all cases"))
  
  (* not normally a type checking rule -- included because we cannot infer types
   * for lamdba abstractions or pattern-matching functions, but type inference
   * for application requires inference of the function being applied *)
  | Application (e1, e2), t2 -> (match (
        infer_type i env context e2
        >>= fun t1 -> (
        try
          check_type i env context e1
            (VArrow (t1, t2))
        with Cannot_reify _ -> failure "")
        >> fun _ ->
        SType t2) with
    | SType t as r -> r
    | SDecl _ -> assert false 
    | F _ as f -> match try_eq () with F _ -> f | x -> x)

  | _ -> try_eq ()
and check_declarations i env context =
  (* checks that a Π type ends with U
   * checks for syntactic equality; does not use readback *) 
  let rec does_pi_end_with_U = function
    | Universe -> true
    | Pi (_, _, b) -> does_pi_end_with_U b
    | _ -> false in

  let tr x = function
    | SType _ as r -> r
    | SDecl _ -> assert false
    | F (e, t) ->
        F (e, lazy (sprintf "%s\nChecking the declaration of \"%s\"."
            (Lazy.force t) x)) in

  let check_type_family_type x typ =
    check_type i env context typ VUniverse
    >>= fun _ ->
    if does_pi_end_with_U typ then SType VUniverse
    else tr x (F (sprintf "\"%s\" is not a family of types." x, lazy "")) in

  let rec constructs type_name type_type t = match type_type, t with
    | Universe, Constructor n when n = type_name -> true
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

  let check_ctor_type type_name type_type constructor_name typ =
    if strictly_positive type_name type_type typ then SType VUniverse
    else
      tr type_name
        (F (sprintf "\"%s\" is not a strictly positive constructor of %s"
          constructor_name type_name, lazy "")) in
  
  let get_new_context rest_bs rest_cs xs =
    let context =
       List.fold_left (fun c (s, type_name, v)
         -> Context.add_constructor c s type_name v)
         context rest_cs in
    (* assume that everything in xs has the correct type, without actually
     * checking them *)
    let context = add_to_context env context xs in
    List.fold_right (fun (s, v) c -> Context.add_binder c s v)
      rest_bs context in

  let rec check_decls result_bs result_cs rest_ds rest_bs = function
    | [] -> SDecl (result_bs, result_cs)
    | (Let (x, e1, e2))::xs ->
        let decl_env = get_env env rest_ds xs in
        let decl_context = get_new_context rest_bs result_cs xs in
        tr x (check_type i decl_env decl_context e1 VUniverse)
        >>= fun _ -> 
        let t = Eval.eval decl_env e1 in
        tr x (check_type i decl_env decl_context e2 t)
        >>= fun _ -> 
        check_decls ((x, t)::result_bs) result_cs rest_ds rest_bs xs
    | (LetRec (x, e1, e2) as d)::xs ->
        let decl_env = get_env env rest_ds xs in
        let decl_env2 = 
          Environment.add_declarations env
            (xs @ (List.rev (d::(filter rest_ds)))) in
        let decl_context = get_new_context rest_bs result_cs xs in
        tr x (check_type i decl_env decl_context e1 VUniverse)
        >>= fun _ -> 
        let t = Eval.eval decl_env e1 in
        let decl_context2 = get_new_context ((x, t)::rest_bs) result_cs xs in
        tr x (check_type i decl_env2 decl_context2 e2 t)
        >>= fun _ -> 
        check_decls ((x, t)::result_bs) result_cs (d::rest_ds) rest_bs xs
    | (Type (x, ps, e, cs))::xs ->
        let decl_env = get_env env rest_ds xs in
        let typefam_type = get_full_type ps e in
        tr x (check_type_family_type x typefam_type) 
        >>= fun _ ->
        let constructor_types =
          List.map (fun (x, e) -> (x, get_full_type ps e)) cs in
        let check_ctor_type (c, e) = check_ctor_type x typefam_type c e in
        List.fold_left (fun result p -> result >>= fun _ -> check_ctor_type p)
          (SType VUniverse) constructor_types 
        >>= fun _ ->
        let result_cs =
          (x, "U", Eval.eval decl_env typefam_type) :: result_cs in
        let result_cs =
          List.fold_left (fun l (c, e) -> (c, x, Eval.eval decl_env e)::l)
          result_cs constructor_types in
        check_decls result_bs result_cs rest_ds rest_bs xs in
  check_decls [] [] [] []

let infer_type = infer_type 0
let check_type = check_type 0
let check_declarations = check_declarations 0
