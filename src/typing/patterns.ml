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

let rec add_unify subst i = function
  | VNeutral (VVar j) when j > i ->
      add_unify subst j (VNeutral (VVar i))
  | VNeutral (VVar j) when i = j -> Some subst
  | v ->
    if Context.subst_mem i subst
    then Context.mgu subst (Context.subst_find i subst) v
    else Some (Context.subst_add i v subst)

let rec pi_to_list i =
  function
  | VArrow (a, b) ->
      let (i, l, v) = pi_to_list i b in
      (i, (-1, a)::l, v)
  | VPi (_, a, b, env) ->
      let j, env = i, Environment.add env (VNeutral (VVar i)) in
      let (i, l, v) = pi_to_list (i + 1) (Eval.eval env b) in
      (i, (j, a)::l, v)
  | v -> (i, [], v)

let rec add_binders checker i context env subst typ patt = match patt, typ with
  | PatternUnderscore, _ ->
      Some (VNeutral (VVar i)
          , i + 1
          , context
          , env
          , subst)
  | PatternBinder x, _ ->
      Some (VNeutral (VVar i)
          , i + 1
          , Context.add_binder context x typ
          , Environment.add env (VNeutral (VVar i))
          , subst)
  | PatternPair (p1, p2), VTimes (a, b) ->
      add_binders checker i context env subst a p1
      >>= fun (v1, i, context, env, subst) ->
      add_binders checker i context env subst b p2
      >>= fun (v2, i, context, env, subst) ->
      Some (VPair (v1, v2), i, context, env, subst)
  | PatternPair (p1, p2), VSigma (x, a, b, sigma_env) ->
      add_binders checker i context env subst a p1
      >>= fun (v1, i, context, env, subst) ->
      let sigma_env' = Environment.add sigma_env v1 in
      add_binders checker (i + 1) context env subst (Eval.eval sigma_env' b) p2 
      >>= fun (v2, i, context, env, subst) ->
      Some (VPair (v1, v2), i, context, env, subst)
  | PatternPair _, _ -> None
  | PatternApplication (c, l), _ ->
      let rec add i context env subst values_matched = function
        | [], [] ->
            Some (values_matched, i, context, env, subst)
        | p::ps, (j, t)::ts ->
            let t = Context.subst_value subst t in
            (match p with 
             | PatternInaccessible e ->
                 if checker i context env e t
                 then
                   let evaluated = (Eval.eval env e) in
                   (* all values which are checked against the inaccessible
                    * pattern will have the form matched *)
                   let matched =
                     Context.subst_value subst (VNeutral (VVar j)) in
                   (* check that the inaccessible pattern matches in all cases,
                    * i.e. the for of value to be matched is equal to the
                    * expression in the pattern *)
                   let correct =
                     j <> -1
                     && Equality.are_values_equal evaluated matched in
                   if correct then Some (evaluated, i, context, env, subst)
                   else None
                 else None
              | _ -> add_binders checker i context env subst t p)
            >>= fun (v, i, context, env, subst) ->
            if j <> -1 then
              match add_unify subst j v with
              | Some subst ->
                  add i context env subst (v::values_matched) (ps, ts)
              | None -> None
            else add i context env subst (v::values_matched) (ps, ts)
        | _ -> raise Cannot_pattern_match in

      let rec try_constructor_type constructor_type =
        let (i, ts, constructed) = pi_to_list i constructor_type in
        match Context.mgu subst typ constructed with
        | None -> None
        | Some subst -> (
            match add i context env subst [] (l, ts) with
            | None -> None
            | Some (tl, i, context, env, subst) -> 
                let value_matched = VConstruct (c, tl) in
                Some (value_matched, i
                    , context
                    , env, subst)) in

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

let add_binders checker i context env typ patt =
  add_binders checker i context env Context.subst_empty typ patt
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
            List.filter (fun (c, v) -> Context.unify (get_constructed_type i v) typ)
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
  match split (i + 1) context typ (VNeutral (VVar i)) i with
  | [] -> None (* typ is caseless *)
  | (_, v)::_ -> Some v

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
  | None -> Some value 
  | Some true -> None (* there is a match for all values of the form value *)
  | Some false -> (
      (* there may or may not be a match -- split *)
      match unknowns with
      | p::tl ->
          let split_result = split i context typ value !blocker in
          List.fold_left
            (fun r (i, v) -> match r with
               | None -> cover_rec i context unknowns typ v
               | Some v -> r)
            None
            split_result
      (* find_matches must return a list containing at least one element *)
      | _ -> assert false)

let cover i context patterns typ =
  (* if the type has no valid constructors, then no patterns are need to form a
   * covering *)
  if patterns = [] then caseless i context typ 
  else cover_rec (i + 1) context patterns typ (VNeutral (VVar i))
