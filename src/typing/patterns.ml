open Abstract
open Value


let (>>=) m f = match m with
  | None -> None
  | Some a -> f a

(* unification
 * there is no occurs check, so this will not return if passed something of the
 * form _ i c (..., i, ...) *)
let mgu =
  let rec mgu subst v1 v2 = match v1, v2 with
    (* variables unify than anything, unless they are already in the
     * substitution *)
    | VNeutral (VVar i), v ->
        if Context.subst_mem i subst then mgu subst (Context.subst_find i subst) v
        else Some (Context.subst_add i v subst)
    | v, VNeutral (VVar i) ->
        if Context.subst_mem i subst then mgu subst v (Context.subst_find i subst) 
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
    | VPi (Underscore, v, e, env), VPi (Underscore, v', e', env') ->
        mgu subst v v' >>= fun u ->
        if e = e' && env = env' then Some u else None
    | VPi (Name _, v, e, env), VPi (Name _, v', e', env') ->
        mgu subst v v' >>= fun u ->
        if e = e' && env = env' then Some u else None
    | VSigma (Underscore, v, e, env), VSigma (Underscore, v', e', env') ->
        mgu subst v v' >>= fun u ->
        if e = e' && env = env' then Some u else None
    | VSigma (Name _, v, e, env), VSigma (Name _, v', e', env') ->
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
        then mgu subst (VNeutral n) (VNeutral n')
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

(* processes a single pattern
 * add_binders i context env typ patt returns None, if the pattern does not
 * match typ, or Some (i', context', env', subst), where
 *   * i' is the level to be used in checking the mody of the clause
 *   * context' is the context with all of the binders in the pattern added
 *   * env' is the environment with all of the binders in the pattern bound to
 *     fresh neutral variables 
 *   * subst is a substitution which maps neutral variables to a more specific
 *     type *)
let rec add_binders i context env typ patt = match patt, typ with
  | PatternUnderscore, _ -> Some (i, context, env, Context.subst_empty)
  | PatternBinder x, _ ->
      Some (i + 1
          , Context.add_binder context x typ
          , Environment.add env (VNeutral (VVar i))
          , Context.subst_empty)
  | PatternPair (p1, p2), VSigma (Underscore, a, b, sigma_env) ->
      add_binders i context env a p1
      >>= fun (i, context, env, subst) ->
      add_binders i context env (Eval.eval sigma_env b) p2
  | PatternPair (p1, p2), VSigma (Name x, a, b, sigma_env) ->
      add_binders i context env a p1
      >>= fun (i, context, env, subst) ->
      (* TODO: is this correct?? *)
      let sigma_env' = Environment.add sigma_env (VNeutral (VVar i)) in
      add_binders (i + 1) context env (Eval.eval sigma_env' b) p2 
  | PatternPair _, _ -> None
  | PatternApplication (c, l), _ ->
      let aux result p = result
        >>= fun (i, context, env, t, subst) -> 
        match t with
        | VPi (Underscore, a, b, pi_env) ->
            add_binders i context env a p
            >>= fun (i, context, env, subst) ->
            Some (i, context, env, Eval.eval pi_env b, subst)
        | VPi (Name x, a, b, pi_env) ->
            add_binders i context env a p
            >>= fun (i, context, env, subst) ->
            let pi_env' = Environment.add pi_env (VNeutral (VVar i)) in
            Some (i + 1, context, env, Eval.eval pi_env' b, subst)
        | _ -> None in
      let add constructor_type =
        List.fold_left aux (Some (i, context, env, constructor_type, Context.subst_empty)) l
        >>= fun (i, context, env, remaining, subst) ->
        match mgu typ remaining with
        | Some subst -> Some (i, Context.subst_apply context subst, Context.subst_env subst env, subst)
        | None -> None in
      let possible_types = Context.get_constructor_types context c in
      List.fold_left (fun r t -> match r with
        | Some _ -> r
        | None -> add t) None possible_types
