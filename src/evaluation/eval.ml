open Abstract
open Environment
open Value

exception Cannot_evaluate of string
exception Pattern_match
exception Match_neutral

(* attempts to match the given pattern with the given value, and returns the
 * modifications resulting from the binders in the pattern if successful *)
let rec try_match env pattern value = match pattern, value with
  | PatternPair (p1, p2), VPair (v1, v2) ->
      let (m, new_env) = try_match env p1 v1 in
      if m then try_match new_env p2 v2 else (false, empty)
  | PatternPair _, VNeutral _ -> raise Match_neutral
  | PatternApplication (s, ps), VConstruct (c, vs) when c = s ->
      try_match_all env ps (List.rev vs)
  | PatternApplication _, VNeutral _ -> raise Match_neutral
  | PatternBinder x, v -> (true, add env v)
  | PatternUnderscore, _ -> (true, env)
  (* inaccessible patterns are guaranteed to match by the type checker *)
  | PatternInaccessible _, _ -> (true, env)
  | _ -> (false, empty)
(* attempts to match all of the patterns against their corresponding value *)
and try_match_all env patterns values = match patterns, values with
  | [], [] -> (true, env)
  | p::ps, (false, v)::vs ->
      let (m, new_env) = try_match env p v in
      if m then try_match_all new_env ps vs else (false, empty)
  | patterns, (true, v)::vs -> try_match_all env patterns vs
  | _ -> (false, empty)

(* matches the value against the pattern in each of the cases, returning the
 * expression associated with the first match and the environment with the extra
 * bindings associated with the match *)
let rec pattern_match env cases value = match cases with
  | [] -> raise Pattern_match
  | (p, e)::cs ->
      let (m, new_env) = try_match env p value in
      if m then (new_env, e) else pattern_match env cs value

(* evaluates an expression to a value *)
let rec eval' metavars f env = 
  let apply b e fun_env v = match b with
  | Underscore -> eval' metavars f fun_env e
  | Name _ -> eval' metavars f (add fun_env v) e in

  let apply_function cases fun_env v =
    try 
      let (new_env, e) = pattern_match fun_env cases v in
      eval' metavars f new_env e with
    | Match_neutral -> VNeutral (VFunctionApplication (cases, fun_env, v)) in

  function
  | Pair (e1, e2) -> VPair (eval' metavars f env e1, eval' metavars f env e2)
  | Lambda (b, e) -> VLambda (b, e, env)
  | LambdaImplicit (b, e) -> VLambdaImplicit (b, e, env)
  | Pi (Underscore, e1, e2) -> VArrow (eval' metavars f env e1, eval' metavars f env e2)
  | Pi (Name b, e1, e2) -> VPi (b, eval' metavars f env e1, e2, env)
  | PiImplicit (x, e1, e2) -> VPiImplicit (x, eval' metavars f env e1, e2, env)
  | Sigma (Underscore, e1, e2) ->
      VTimes (eval' metavars f env e1, eval' metavars f env e2)
  | Sigma (Name b, e1, e2) -> VSigma (b, eval' metavars f env e1, e2, env)
  | Function l -> VFunction (l, env)
  | LocalDeclaration (l, e) -> f env l; eval' metavars f (add_declarations env l) e
  (* it is assumed that the type checker has inserted metavariables in the
   * correct places for implicit argument *)
  | Application (e1, e2) ->
      if e1 = e2 then raise (Cannot_evaluate "self-application") else
      let v1 = eval' metavars f env e1 in
      let v2 = eval' metavars f env e2 in
      if v1 = v2 then raise (Cannot_evaluate "self-application") else
      (match v1 with
       | VConstruct (c, l) -> VConstruct (c, (false, v2)::l)
       | VLambda (b, e, fun_env) -> apply b e fun_env v2
       | VLambdaImplicit (b, e, fun_env) ->
           let fun_env = Environment.add fun_env (VNeutral (VMeta ((Abstract.create_implicit_metavariable ())))) in
           eval' metavars f fun_env (Application (e, e2))
       | VFunction (l, fun_env) -> apply_function l fun_env v2
       | VNeutral v -> VNeutral (VApplication (v, v2))
       | _ -> raise (Cannot_evaluate
                "Attempted to apply a value which is not a function"))
  | ApplicationImplicit (e1, e2) ->
      if e1 = e2 then raise (Cannot_evaluate "self-application") else
      let v1 = eval' metavars f env e1 in
      let v2 = eval' metavars f env e2 in
      if v1 = v2 then raise (Cannot_evaluate "self-application") else
      (match v1 with
       | VConstruct (c, l) -> VConstruct (c, (true, v2)::l)
       | VLambda (b, e, fun_env) -> apply b e fun_env v2
       | VLambdaImplicit (b, e, fun_env) -> apply b e fun_env v2
       | VFunction (l, fun_env) -> apply_function l fun_env v2
       | VNeutral v -> VNeutral (VApplicationImplicit (v, v2))
       | _ -> raise (Cannot_evaluate
                "Attempted to apply a value which is not a function"))
  | Universe i -> VUniverse i
  | UnitType -> VUnitType
  | Unit -> VUnit
  | Index i -> 
      (try get env (eval' metavars f) i with
       | Invalid_argument _ ->
           raise (Cannot_evaluate "Attempted to use a negative de Bruijn index")
       | Failure _ ->
           raise (Cannot_evaluate
                    "Attempted to use a de Bruijn index which was too large"))
  | Constructor c -> VConstruct (c, [])
  | Proj1 e -> (
      match eval' metavars f env e with
      | VPair (v1, v2) -> v1
      | VNeutral v -> VNeutral (VProj1 v)
      | _ ->
        raise (Cannot_evaluate
          "Attempted to project an element out of a value which is not a pair"))
  | Proj2 e -> (
      match eval' metavars f env e with
      | VPair (v1, v2) -> v2
      | VNeutral v -> VNeutral (VProj2 v)
      | _ ->
        raise (Cannot_evaluate
          "Attempted to project an element out of a value which is not a pair"))
  | Meta i -> (
      match metavars i with
      | None -> VNeutral (VMeta i)
      | Some v -> v)

let eval metavars = eval' metavars (fun _ _ -> ())
