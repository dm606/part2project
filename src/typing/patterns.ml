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

let rec add_unify subst x i = function
  | VNeutral (VVar (x1, j)) when j > i ->
      add_unify subst x1 j (VNeutral (VVar (x, i)))
  | VNeutral (VVar (_, j)) when i = j -> Some subst
  | v ->
    if Context.subst_mem i subst
    then Context.mgu subst (Context.subst_find i subst) v
    else Some (Context.subst_add i v subst)

let rec pi_to_list constraints i =
  function
  | VArrow (a, b) ->
      let (i, l, v) = pi_to_list constraints i b in
      (i, ("", -1, a)::l, v)
  | VPi (x, a, b, env) ->
      let j, env = i, Environment.add env (VNeutral (VVar (x, i))) in
      let (i, l, v) = pi_to_list constraints (i + 1)
        (Eval.eval (Equality.get_metavariable_assignment constraints) env b) in
      (i, (x, j, a)::l, v)
  | VPiImplicit (x, a, b, env) ->
      let j, env = i, Environment.add env (VNeutral (VVar (x, i))) in
      pi_to_list constraints (i + 1)
        (Eval.eval (Equality.get_metavariable_assignment constraints) env b) 
  | v -> (i, [], v)

let rec add_binders checker i constraints context env subst typ patt =
  match patt, typ with
  | PatternUnderscore, _ ->
      Some (VNeutral (VVar ("", i))
          , i + 1
          , constraints
          , context
          , env
          , subst)
  | PatternBinder x, _ ->
      Some (VNeutral (VVar (x, i))
          , i + 1
          , constraints
          , Context.add_binder context x typ
          , Environment.add env (VNeutral (VVar (x, i)))
          , subst)
  | PatternPair (p1, p2), VTimes (a, b) ->
      add_binders checker i constraints context env subst a p1
      >>= fun (v1, i, constraints, context, env, subst) ->
      add_binders checker i constraints context env subst b p2
      >>= fun (v2, i, constraints, context, env, subst) ->
      Some (VPair (v1, v2), i, constraints, context, env, subst)
  | PatternPair (p1, p2), VSigma (x, a, b, sigma_env) ->
      add_binders checker i constraints context env subst a p1
      >>= fun (v1, i, constraints, context, env, subst) ->
      let sigma_env' = Environment.add sigma_env v1 in
      add_binders checker (i + 1) constraints context env subst
        (Eval.eval (Equality.get_metavariable_assignment constraints) sigma_env' b) p2 
      >>= fun (v2, i, constraints, context, env, subst) ->
      Some (VPair (v1, v2), i, constraints, context, env, subst)
  | PatternPair _, _ -> None
  | PatternApplication (c, l), _ ->
      let rec add i constraints context env subst values_matched = function
        | [], [] ->
            Some (values_matched, i, constraints, context, env, subst)
        | p::ps, (x, j, t)::ts ->
            let t = Context.subst_value subst t in
            (match p with 
             | PatternInaccessible e -> (
                 match checker i constraints context env e t with
                 | Some (e, constraints) ->
                     let evaluated =
                       Context.subst_value subst (Eval.eval (Equality.get_metavariable_assignment constraints) env e) in
                     (* all values which are checked against the inaccessible
                      * pattern will have the form matched *)
                     let matched =
                       Context.subst_value subst (VNeutral (VVar (x, j))) in
                     (* check that the inaccessible pattern matches in all cases,
                      * i.e. the for of value to be matched is equal to the
                      * expression in the pattern *)
                     let constraints = Equality.test_equality i constraints evaluated matched in
                     (* TODO: the constraints might never be satisfied due to
                      * previous constraints *)
                     if j <> -1 && not (Equality.never_satisfied constraints)
                     then Some (evaluated, i, constraints, context, env, subst)
                     else None
                 | None -> None)
              | _ -> add_binders checker i constraints context env subst t p)
            >>= fun (v, i, constraints, context, env, subst) ->
            if j <> -1 then
              match add_unify subst x j v with
              | Some subst ->
                  add i constraints context env subst (v::values_matched) (ps, ts)
              | None -> None
            else add i constraints context env subst (v::values_matched) (ps, ts)
        | _ -> None in

      let rec try_constructor_type constructor_type =
        let (i, ts, constructed) = pi_to_list constraints i constructor_type in
        match Context.mgu subst typ constructed with
        | None -> None
        | Some subst -> (
            match add i constraints context env subst [] (l, ts) with
            | None -> None
            | Some (tl, i, constraints, context, env, subst) -> 
                let value_matched = VConstruct (c, List.map (fun v -> (false, v)) tl) in
                Some (value_matched, i, constraints, context, env, subst)) in

      let possible_types = Context.get_constructor_types context c in
      List.fold_left (fun r t -> match r with
        | Some _ -> r
        | None -> try_constructor_type t) None possible_types
  | PatternInaccessible _, _ -> 
      (* this function will only accept a pattern if all inaccessible patterns
       * are guaranteed to match. Inaccessible patterns can only be guaranteed
       * to match if they are in a PatternApplication (except in degenerate
       * cases where inaccessible patterns are useless. Hence this case always
       * returns None. Inaccessible patterns inside PatternApplications are
       * handed in the PatternApplication case.  *)
      None

let add_binders checker i constraints context env typ patt =
  add_binders checker i constraints context env Context.subst_empty typ patt
  >>= fun (v, i, constraints, context, env, subst) ->
  Some (v, i, constraints, Context.subst_apply context subst
      , Context.subst_env subst env, subst)

type match_result = Match | Unknown of int | NoMatch

let (&) m1 = function
  | Match -> m1
  | Unknown i -> (match m1 with Match -> Unknown i | _ -> m1)
  | NoMatch -> NoMatch

let rec check_match pattern value =
  let rec check_match_application (pl : pattern list) vl = match pl, vl with
    | [], [] -> Match 
    | pl, (true, v)::vl -> check_match_application pl vl
    | p::pl, (false, v)::vl -> (check_match p v) & (check_match_application pl vl)
    | _ -> NoMatch in

  match pattern, value with
  | PatternUnderscore, _ -> Match
  | PatternBinder _, _ -> Match
  (* assume that inaccessible patterns have already been checked *)
  | PatternInaccessible _, _ -> Match
  | PatternPair (p1, p2), VPair (v1, v2) ->
      check_match p1 v1 & check_match p2 v2
  | PatternPair _, VConstruct _ -> NoMatch
  | PatternPair _, VNeutral (VVar (_, i)) -> Unknown i
  | PatternApplication (pc, pl), VConstruct (vc, vl) when pc = vc ->
      check_match_application pl vl
  | PatternApplication _, VConstruct _ ->
      NoMatch (* constructor names do not match *)
  | PatternApplication _, VPair _ -> NoMatch
  | PatternApplication _, VNeutral (VVar (_, i)) -> Unknown i
  | _ -> assert false (* value can't have been created by a split *)

(* split along blocker *)
let rec split i constraints context subst typ value blocker =
  let rec get_constructed_type i = function
    | VArrow (a, b) -> get_constructed_type i b
    | VPi (x, _, b, env) ->
        get_constructed_type (i + 1)
          (Eval.eval (Equality.get_metavariable_assignment constraints) (Environment.add env (VNeutral (VVar (x, i)))) b)
    | VPiImplicit (x, _, b, env) ->
        get_constructed_type (i + 1)
          (Eval.eval (Equality.get_metavariable_assignment constraints) (Environment.add env (VNeutral (VVar (x, i)))) b)
    | VConstruct _ as t -> t
    | _ -> assert false in

  let rec construct i = function
    | VArrow (a, b) ->
        let (i, l) = construct (i + 1) b in
        (i, (false, VNeutral (VVar ("", i)))::l)
    | VPi (x, _, b, env) ->
        let (i, l) = construct (i + 1)
          (Eval.eval (Equality.get_metavariable_assignment constraints) (Environment.add env (VNeutral (VVar (x, i)))) b) in
        (i, (false, VNeutral (VVar (x, i)))::l)
    | VPiImplicit (x, _, b, env) ->
        let (i, l) = construct (i + 1)
          (Eval.eval (Equality.get_metavariable_assignment constraints) (Environment.add env (VNeutral (VVar (x, i)))) b) in
        (i, l)
    | VConstruct _ -> (i, [])
    | _ -> assert false in

  match value with 
  | VNeutral (VVar (x, j)) when j = blocker -> (match typ with
      | VConstruct (type_name, _) ->
          (* return all valid constructors of type_name *)
          let ctors = List.map
            (fun (c, v) ->
              (c, v, Context.mgu subst (get_constructed_type i v) typ))
            (Context.get_constructors_of_type context type_name) in
          (* the constructors which could possibly be used to create a value of
           * type typ *)
          let valid_ctors =
            List.filter (fun (c, v, subst) -> subst <> None) ctors in
          List.map (fun (c, v, subst) ->
            match subst with
            | None -> assert false (* should have been removed by filter *)
            | Some subst ->
               let (i, l) = construct i v in
               (i, VConstruct (c, l), subst)) valid_ctors
      | VSigma _ | VTimes _ ->
          (* return a pair of variables *)
          [i + 2, VPair (VNeutral (VVar ("", i)), VNeutral (VVar ("", i + 1)))
           , subst]
      | _ -> raise Cannot_pattern_match)
  | VNeutral (VVar (x, j)) -> [i, value, subst]
  | VPair (v1, v2) -> (match typ with
      | VTimes (a, b) ->
          let l = split i constraints context subst a v1 blocker in
          concat_map (fun (i, v1, subst) -> 
            let l2 = split i constraints context subst b v2 blocker in
            List.map (fun (i, v2, subst) -> i, VPair (v1, v2), subst) l2) l
      | VSigma (_, a, b, env) ->
          let l = split i constraints context subst a v1 blocker in
          concat_map (fun (i, v1, subst) -> 
            let env' = Environment.add env v1 in
            let l2 = split i constraints context subst (Eval.eval (Equality.get_metavariable_assignment constraints) env' b) v2 blocker in
            List.map (fun (i, v2, subst) -> i, VPair (v1, v2), subst) l2) l
      | _ ->
          (* value could only have been produced by a split; a split will only
           * produce a pair if typ is of the form VSigma _ or VTimes _ *)
          assert false)
  | VConstruct (c, l) -> (match typ with
      | VConstruct (type_name, _) ->
          let _, ctor_type =
            List.find (fun (d, _) -> d = c)
              (Context.get_constructors_of_type context type_name) in
          let aux i subst v typ = match typ with
            | VArrow (a, b) ->
                let l = split i constraints context subst a v blocker in
                List.map (fun (i, v, subst) -> (i, v, b, subst)) l
            | VPi (_, a, b, env) ->
                let l = split i constraints context subst a v blocker in
                List.map (fun (i, v, subst) ->
                  let env' = Environment.add env v in
                  (i, v, Eval.eval (Equality.get_metavariable_assignment constraints) env' b, subst)) l
            | VPiImplicit (_, a, b, env) ->
                let l = split i constraints context subst a v blocker in
                List.map (fun (i, v, subst) ->
                  let env' = Environment.add env v in
                  (i, v, Eval.eval (Equality.get_metavariable_assignment constraints) env' b, subst)) l
            | _ -> assert false in
          let aux2 (b, v) (i, l, typ, subst) =
            let split_results = aux i subst v typ in
            List.map (fun (i, v, typ, subst) -> (i, (b, v)::l, typ, subst)) split_results in
          List.map (fun (i, l, _, subst) -> (i, VConstruct (c, l), subst))
            (List.fold_right (fun v l -> concat_map (aux2 v) l) 
              l [i, [], ctor_type, subst])
      | _ -> assert false)
  | _ -> assert false

let split i constraints context typ value blocker =
  List.map (fun (i, v, subst) -> (i, v, Context.subst_value subst typ))
    (split i constraints context Context.subst_empty typ value blocker)

let () = Equality.split := split

(* typ is caseless if spliting [i]:typ along i produces no values *)
let caseless i constraints context typ =
  match split (i + 1) constraints context typ (VNeutral (VVar ("", i))) i with
  | [] -> None (* typ is caseless *)
  | (_, v, _)::_ -> Some v

(* checks that patterns covers all values of the form value (patterns must not
 * be []) *)
let rec cover_rec i constraints context patterns typ value =
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
  | None -> Some value 
  | Some true -> None (* there is a match for all values of the form value *)
  | Some false -> (
      (* there may or may not be a match -- split *)
      match unknowns with
      | p::tl ->
          let split_result = split i constraints context typ value !blocker in
          List.fold_left
            (fun r (i, v, typ) -> match r with
               | None -> cover_rec i constraints context unknowns typ v
               | Some v -> r)
            None
            split_result
      (* find_matches must return a list containing at least one element *)
      | _ -> assert false)

let cover i constraints context patterns typ =
  (* if the type has no valid constructors, then no patterns are need to form a
   * covering *)
  if patterns = [] then caseless i constraints context typ 
  else cover_rec (i + 1) constraints context patterns typ (VNeutral (VVar ("", i)))
