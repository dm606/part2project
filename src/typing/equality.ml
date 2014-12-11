open Abstract
open Eval
open Value

type normal =
  | NPair of normal * normal
  | NLambda of int option * normal
  | NPi of int option * normal * normal
  | NSigma of int option * normal * normal
  | NFunction of (normal_pattern * normal) list
  | NUniverse
  | NUnitType
  | NUnit
  | NConstruct of string * normal list
  | NNeutral of normal_neutral
and normal_neutral =
  | NVar of int 
  | NFunctionApplication of (normal_pattern * normal) list * neutral
  | NApplication of normal_neutral * normal
  | NProj1 of normal_neutral
  | NProj2 of normal_neutral
and normal_pattern =
  | NPPair of normal_pattern * normal_pattern
  | NPApplication of string * normal_pattern list
  | NPBinder of int
  | NPUnderscore

let rec readback i = 
  let rec convert_pattern env i = function
  | PatternPair (p1, p2) -> 
      let (np1, env, i) = convert_pattern env i p1 in
      convert_pattern env i p2
  | PatternApplication (c, patterns) ->
      let (ps, env, i) = List.fold_left (fun (ps, env, i) p ->
        let (np, env, i) = convert_pattern env i p in
        (np::ps, env, i)) ([], env, i) patterns in
      (NPApplication (c, List.rev ps), env, i)
  | PatternBinder _ ->
      (NPBinder i, Environment.add env (VNeutral (VVar i)), i + 1) 
  | PatternUnderscore -> (NPUnderscore, env, i) in

  let convert_case env (p, e) = 
    let (np, env, i) = convert_pattern env i p in
    (np, readback i (eval env e)) in

  let convert_cases env = List.map (convert_case env) in

  let rec readback_neutral i = function
  | VVar i -> NVar i
  | VFunctionApplication (cases, env, v) ->
                  NFunctionApplication (convert_cases env cases, v)
  | VApplication (v1, v2) ->
      NApplication (readback_neutral i v1, readback i v2)
  | VProj1 v -> NProj1 (readback_neutral i v)
  | VProj2 v -> NProj2 (readback_neutral i v) in

  function
  | VPair (v1, v2) -> NPair (readback i v1, readback i v2)
  | VLambda (Underscore, e, env) ->
      NLambda (None, readback i (eval env e))
  | VLambda (_, e, env) -> 
      NLambda (Some i, readback (i + 1)
        (eval (Environment.add env (VNeutral (VVar i))) e))
  | VPi (Underscore, v, e, env) -> 
      NPi (None, readback i v, readback i (eval env e))
  | VPi (_, v, e, env) -> 
      NPi (Some i, readback i v, readback (i + 1)
        (eval (Environment.add env (VNeutral (VVar i))) e))
  | VSigma (Underscore, v, e, env) ->
      NSigma (None, readback i v, readback i (eval env e))
  | VSigma (_, v, e, env) ->
      NSigma (Some i, readback i v, readback (i + 1)
        (eval (Environment.add env (VNeutral (VVar i))) e))
  | VFunction (l, env) -> NFunction (convert_cases env l)
  | VUniverse -> NUniverse
  | VUnitType -> NUnitType
  | VUnit -> NUnit
  | VConstruct (c, vs) -> NConstruct (c, List.map (readback i) vs)
  | VNeutral n -> NNeutral (readback_neutral i n)

let are_equal env x y = (readback 0 (eval env x)) = (readback 0 (eval env y))
