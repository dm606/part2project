open List

open Abstract
open Value

exception Cannot_evaluate of string
exception Pattern_match

(* attempts to match the given pattern with the given value, and returns the
 * modifications resulting from the binders in the pattern if successful *)
let rec try_match env pattern value = match pattern, value with
  | (PatternPair (p1, p2)), (VPair (v1, v2)) ->
      let (m, new_env) = try_match env p1 v1 in
      if m then try_match new_env p2 v2 else (false, [])
  | (PatternApplication (s, ps)), (VConstruct (c, vs)) when c = s ->
      try_match_all env ps (rev vs)
  | (PatternBinder x), v -> (true, (EnvValue v)::env)
  | (PatternUnderscore), _ -> (true, env)
  | _ -> (false, [])
(* attempts to match all of the patterns against their corresponding value *)
and try_match_all env patterns values = match patterns, values with
  | [], [] -> (true, env)
  | p::ps, v::vs ->
      let (m, new_env) = try_match env p v in
      if m then try_match_all new_env ps vs else (false, [])
  | _ -> (false, [])

(* matches the value against the pattern in each of the cases, returning the
 * expression associated with the first match and the environment with the extra
 * bindings associated with the match *)
let rec pattern_match env cases value = match cases with
  | [] -> raise Pattern_match
  | (p, e)::cs ->
      let (m, new_env) = try_match env p value in
      if m then (new_env, e) else pattern_match env cs value

let rec add_declarations env =
  let rec add_decls rest = function
    | [] -> rest @ env
    | (Let (_, _, e))::xs ->
        add_decls (EnvThunk (lazy (eval (add_decls rest xs) e))::rest) xs
    | (LetRec (_, _, e))::xs as l ->
        add_decls (EnvThunk (lazy (eval (add_decls rest l) e))::rest) xs 
    | _::xs -> add_decls rest xs in
  add_decls []
(* evaluates an expression to a value *)
and eval env = 
  let apply b e fun_env v = match b with
  | Underscore -> eval fun_env e
  | Name _ -> eval ((EnvValue v)::fun_env) e in

  let apply_function cases fun_env v =
    let (new_env, e) = pattern_match fun_env cases v in
    eval new_env e in

  let eval_proj proj e =
    match eval env e with
    | VPair (v1, v2) -> proj (v1, v2)
    | _ ->
      raise (Cannot_evaluate
        "Attempted to project an element out of a value which is not a pair") in

  function
  | Pair (e1, e2) -> VPair (eval env e1, eval env e2)
  | Lambda (b, e) -> VLambda (b, e, env)
  | Pi (b, e1, e2) -> VPi (b, eval env e1, e2, env)
  | Sigma (b, e1, e2) -> VSigma (b, eval env e1, e2, env)
  | Function l -> VFunction (l, env)
  | LocalDeclaration (l, e) -> eval (add_declarations env l) e
  | Application (e1, e2) ->
      let v2 = eval env e2 in
      (match eval env e1 with
       | VConstruct (c, l) -> VConstruct (c, v2::l)
       | VLambda (b, e, fun_env) -> apply b e fun_env v2
       | VFunction (l, fun_env) -> apply_function l fun_env v2
       | _ -> raise (Cannot_evaluate
                "Attempted to apply a value which is not a function"))
  | Universe -> VUniverse
  | UnitType -> VUnitType
  | Unit -> VUnit
  | Index i -> 
      (match nth env i with
       | EnvValue v -> v
       | EnvThunk t -> Lazy.force t
       | exception Invalid_argument _ ->
           raise (Cannot_evaluate "Attempted to use a negative de Bruijn index")
       | exception Failure _ ->
           raise (Cannot_evaluate
                    "Attempted to use a de Bruijn index which was too large"))
  | Constructor c -> VConstruct (c, [])
  | Proj1 e -> eval_proj (fun (v1, _) -> v1) e
  | Proj2 e -> eval_proj (fun (_, v2) -> v2) e

