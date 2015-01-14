open Abstract
open Value

exception Cannot_pattern_match

let concat_map f =
  let rec aux acc = function
    | [] -> acc
    | x::tl -> aux (f x @ acc) tl in
  aux []

let (>>=) m f = match m with
  | None -> None
  | Some a -> f a

let rec occurs v i = match v with
  | VPair (v1, v2) -> occurs v1 i || occurs v2 i
  | VLambda _ -> false
  | VArrow (a, b) -> occurs a i || occurs b i
  | VPi (_, v, _, _) -> occurs v i
  | VTimes (a, b) -> occurs a i || occurs b i
  | VSigma (_, v, _, _) -> occurs v i
  | VFunction _ -> false
  | VUniverse -> false
  | VUnitType -> false
  | VUnit -> false
  | VConstruct (_, l) -> List.exists (fun v -> occurs v i) l
  | VNeutral n -> neutral_occurs n i
and neutral_occurs n i = match n with
  | VVar j when i = j -> true
  | VVar j -> false
  | VFunctionApplication (_, _, n) -> occurs n i
  | VApplication (n, v) -> neutral_occurs n i || occurs v i
  | VProj1 n -> neutral_occurs n i
  | VProj2 n -> neutral_occurs n i

(* unification *)
let mgu =
  let rec mgu subst v1 v2 = match v1, v2 with
    | VNeutral (VVar i), VNeutral (VVar j) when i = j ->
        Some subst
    (* variables unify than anything, unless they are already in the
     * substitution *)
    | VNeutral (VVar i), v ->
        if occurs v i then None (* occurs check *)
        else
          if Context.subst_mem i subst
          then mgu subst (Context.subst_find i subst) v
          else Some (Context.subst_add i v subst)
    | v, VNeutral (VVar i) ->
        if occurs v i then None (* occurs check *)
        else
          if Context.subst_mem i subst
          then mgu subst v (Context.subst_find i subst) 
          else Some (Context.subst_add i v subst)
    (* atoms unify than themselves *)
    | VUniverse, VUniverse -> Some subst
    | VUnitType, VUnitType -> Some subst
    | VUnit, VUnit -> Some subst
    (* terms unify if they have the same structure and all subterms
     * are unify *)
    | VLambda (Underscore, e, env), VLambda (Underscore, e', env') ->
        if e = e' && env = env' then Some subst else None
    | VLambda (Name _, e, env), VLambda (Name _, e', env') ->
        if e = e' && env = env' then Some subst else None
    | VArrow (a, b), VArrow (a', b') ->
        mgu subst a a' >>= fun subst ->
        mgu subst b b'
    | VPi (_, v, e, env), VPi (_, v', e', env') ->
        mgu subst v v' >>= fun u ->
        if e = e' && env = env' then Some u else None
    | VTimes (a, b), VTimes (a', b') ->
        mgu subst a a' >>= fun subst ->
        mgu subst b b'
    | VSigma (_, v, e, env), VSigma (_, v', e', env') ->
        mgu subst v v' >>= fun u ->
        if e = e' && env = env' then Some u else None
    | VFunction _, VFunction _ -> if v1 = v2 then Some subst else None
    | VConstruct (c,  l), VConstruct (c', l') ->
        if c = c'
        then List.fold_left2
          (fun r v v2 -> r >>= fun u -> mgu u v v2) (Some subst) l l'
        else None
    | VNeutral (VFunctionApplication (l, env, n))
    , VNeutral (VFunctionApplication (l', env', n')) ->
        if l = l' && env = env'
        then mgu subst n n'
        else None
    | VNeutral (VApplication (n, v)), VNeutral (VApplication (n', v')) ->
        mgu subst (VNeutral n) (VNeutral n')
        >>= fun u ->
        mgu u v v'
    | VNeutral (VProj1 n), VNeutral (VProj1 n') ->
        mgu subst (VNeutral n) (VNeutral n')
    | VNeutral (VProj2 n), VNeutral (VProj2 n') ->
        mgu subst (VNeutral n) (VNeutral n')
    (* if none of the above cases match, v1 is not unify than v2 *)
    | _ -> None in
  mgu Context.subst_empty

let unify v1 v2 = match mgu v1 v2 with
  | None -> false
  | Some _ -> true

let rec add_binders checker i context env typ patt = match patt, typ with
  | PatternUnderscore, _ ->
      Some (VNeutral (VVar i)
          , i + 1
          , context
          , env
          , Context.subst_empty)
  | PatternBinder x, _ ->
      Some (VNeutral (VVar i)
          , i + 1
          , Context.add_binder context x typ
          , Environment.add env (VNeutral (VVar i))
          , Context.subst_empty)
  | PatternPair (p1, p2), VTimes (a, b) ->
      add_binders checker i context env a p1
      >>= fun (v1, i, context, env, subst) ->
      add_binders checker i context env b p2
      >>= fun (v2, i, context, env, subst) ->
      Some (VPair (v1, v2), i, context, env, subst)
  | PatternPair (p1, p2), VSigma (x, a, b, sigma_env) ->
      add_binders checker i context env a p1
      >>= fun (v1, i, context, env, subst) ->
      let sigma_env' = Environment.add sigma_env v1 in
      add_binders checker (i + 1) context env (Eval.eval sigma_env' b) p2 
      >>= fun (v2, i, context, env, subst) ->
      Some (VPair (v1, v2), i, context, env, subst)
  | PatternPair _, _ -> None
  | PatternApplication (c, l), _ ->
      let aux result p = result
        >>= fun (tl, i, context, env, t, subst) -> 
        match t with
        | VArrow (a, b) ->
            add_binders checker i context env a p
            >>= fun (v, i, context, env, subst) ->
            Some (v::tl, i, context, env, b, subst)
        | VPi (x, a, b, pi_env) ->
            add_binders checker i context env a p
            >>= fun (v, i, context, env, subst) ->
            let pi_env' = Environment.add pi_env v in
            Some (v::tl, i + 1, context, env, Eval.eval pi_env' b, subst)
        | _ -> None in
      let add constructor_type =
        List.fold_left aux
          (Some ([], i, context, env, constructor_type, Context.subst_empty)) l
        >>= fun (tl, i, context, env, remaining, subst) ->
        match mgu typ remaining with
        | Some subst ->
            let value_matched = VConstruct (c, tl) in
            Some (value_matched, i
                , Context.subst_apply context subst
                , Context.subst_env subst env, subst)
        | None -> None in
      let possible_types = Context.get_constructor_types context c in
      List.fold_left (fun r t -> match r with
        | Some _ -> r
        | None -> add t) None possible_types
  | PatternInaccessible e, _ -> 
      if checker i context env e typ
      then
        let evaluated = Eval.eval env e in
        Some (evaluated, i + 1, context, env, Context.subst_empty)
      else None

 let add_binders checker i context env typ patt =
   add_binders checker i context env typ patt
   >>= fun (v, i, context, env, subst) ->
   Some (v, i, context, env, subst)

type match_result = Match | Unknown of int | NoMatch

let (&) m1 = function
  | Match -> m1
  | Unknown i -> (match m1 with Match -> Unknown i | _ -> m1)
  | NoMatch -> NoMatch

let rec check_match pattern value = match pattern, value with
  | PatternUnderscore, _ -> Match
  | PatternBinder _, _ -> Match
  (* assume that inaccessible patterns have already been checked *)
  | PatternInaccessible _, _ -> Match
  | PatternPair (p1, p2), VPair (v1, v2) ->
      check_match p1 v1 & check_match p2 v2
  | PatternPair _, VConstruct _ -> NoMatch
  | PatternPair _, VNeutral (VVar i) -> Unknown i
  | PatternApplication (pc, pl), VConstruct (vc, vl) when pc = vc ->
      List.fold_left2 (fun m p v -> m & check_match p v) Match pl vl
  | PatternApplication _, VConstruct _ ->
      NoMatch (* constructor names do not match *)
  | PatternApplication _, VPair _ -> NoMatch
  | PatternApplication _, VNeutral (VVar i) -> Unknown i
  | _ -> assert false (* value can't have been created by a split *)

(* split along blocker *)
let rec split i context typ value blocker =
  let rec get_constructed_type i = function
    | VArrow (a, b) -> get_constructed_type i b
    | VPi (_, _, b, env) ->
        get_constructed_type (i + 1)
          (Eval.eval (Environment.add env (VNeutral (VVar i))) b)
    | VConstruct _ as t -> t
    | _ -> assert false in

  let rec construct i = function
    | VArrow (a, b) ->
        let (i, l) = construct (i + 1) b in
        (i, (VNeutral (VVar i))::l)
    | VPi (_, _, b, env) ->
        let (i, l) = construct (i + 1)
          (Eval.eval (Environment.add env (VNeutral (VVar i))) b) in
        (i, (VNeutral (VVar i))::l)
    | VConstruct _ -> (i, [])
    | _ -> assert false in

  match value with 
  | VNeutral (VVar j) when j = blocker -> (match typ with
      | VConstruct (type_name, _) ->
          (* return all valid constructors of type_name *)
          let ctors =
            Context.get_constructors_of_type context type_name in
          (* the constructors which could possibly be used to create a value of
           * type typ *)
          let valid_ctors =
            List.filter (fun (c, v) -> unify (get_constructed_type i v) typ)
              ctors in
          List.map (fun (c, v) ->
            let (i, l) = construct i v in
            (i, VConstruct (c, l))) valid_ctors
      | VSigma _ | VTimes _ ->
          (* return a pair of variables *)
          [i + 2, VPair (VNeutral (VVar i), VNeutral (VVar (i + 1)))]
      | _ -> raise Cannot_pattern_match)
  | VNeutral (VVar j) -> [i, value]
  | VPair (v1, v2) -> (match typ with
      | VTimes (a, b) ->
          let l = split i context a v1 blocker in
          concat_map (fun (i, v1) -> 
            let l2 = split i context b v2 blocker in
            List.map (fun (i, v2) -> i, VPair (v1, v2)) l2) l
      | VSigma (_, a, b, env) ->
          let l = split i context a v1 blocker in
          concat_map (fun (i, v1) -> 
            let env' = Environment.add env v1 in
            let l2 = split i context (Eval.eval env' b) v2 blocker in
            List.map (fun (i, v2) -> i, VPair (v1, v2)) l2) l
      | _ ->
          (* value could only have been produced by a split; a split will only
           * produce a pair if typ is of the form VSigma _ or VTimes _ *)
          assert false)
  | VConstruct (c, l) -> (match typ with
      | VConstruct (type_name, _) ->
          let _, ctor_type =
            List.find (fun (d, _) -> d = c)
              (Context.get_constructors_of_type context type_name) in
          let aux i v typ = match typ with
            | VArrow (a, b) ->
                let l = split i context a v blocker in
                List.map (fun (i, v) -> (i, v, b)) l
            | VPi (_, a, b, env) ->
                let l = split i context a v blocker in
                List.map (fun (i, v) ->
                  let env' = Environment.add env v in
                  (i, v, Eval.eval env' b)) l
            | _ -> assert false in
          let aux2 v (i, l, typ) =
            let split_results = aux i v typ in
            List.map (fun (i, v, typ) -> (i, v::l, typ)) split_results in
          List.map (fun (i, l, _) -> (i, VConstruct (c, l)))
            (List.fold_right (fun v l -> concat_map (aux2 v) l) 
              l [i, [], ctor_type])
      | _ -> assert false)
  | _ -> assert false

(* typ is caseless if spliting [i]:typ along i produces no values *)
let caseless i context typ =
  split (i + 1) context typ (VNeutral (VVar i)) i = []

(* checks that patterns covers all values of the form value (patterns must not
 * be []) *)
let rec cover_rec i context patterns typ value =
  let result = ref None in
  let blocker = ref 0 in
  let rec find_matches = function
    | [] -> []
    | p::tl -> (
        match check_match p value with
        | Match -> result := Some true; []
        | Unknown b ->
            result := Some false; blocker := b; p::(find_matches tl)
        | NoMatch -> find_matches tl) in
  let unknowns = find_matches patterns in

  match !result with
  (* there is no pattern which may match *)
  | None -> false
  | Some true -> true (* there is a match for all values of the form value *)
  | Some false -> (
      (* there may or may not be a match -- split *)
      match unknowns with
      | p::tl ->
          let split_result = split i context typ value !blocker in
          List.for_all (fun (i, v) -> cover_rec i context unknowns typ v)
            split_result
      (* find_matches must return a list containing at least one element *)
      | _ -> assert false)

let cover i context patterns typ =
  (* if the type has no valid constructors, then no patterns are need to form a
   * covering *)
  if patterns = [] then caseless i context typ 
  else cover_rec (i + 1) context patterns typ (VNeutral (VVar i))
