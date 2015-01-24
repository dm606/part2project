open Abstract
open Eval
open Value

type normal_envt = [`N of normal | `D of declaration list] list
and normal =
  | NPair of normal * normal
  | NLambda of int * normal
  | NPi of int * normal * normal
  | NSigma of int * normal * normal
  | NFunction of (pattern * expression) list 
               * normal_envt
  | NUniverse of int
  | NUnitType
  | NUnit
  | NConstruct of string * normal list
  | NNeutral of normal_neutral
and normal_neutral =
  | NVar of int 
  | NFunctionApplication of (pattern * expression) list
                          * normal_envt
                          * normal
  | NApplication of normal_neutral * normal
  | NProj1 of normal_neutral
  | NProj2 of normal_neutral

let empty_envt = []

let rec readback i = 
  let readback_env i =
    Environment.map_to_list (fun v -> (`N (readback i v))) (fun d -> `D d) in
  let rec readback_neutral i = function
  | VVar (_, i) -> NVar i
  | VFunctionApplication (cases, env, v) ->
      NFunctionApplication (cases, readback_env i env, readback i v)
  | VApplication (v1, v2) ->
      NApplication (readback_neutral i v1, readback i v2)
  | VProj1 v -> NProj1 (readback_neutral i v)
  | VProj2 v -> NProj2 (readback_neutral i v) in

  function
  | VPair (v1, v2) -> NPair (readback i v1, readback i v2)
  | VLambda (Underscore, e, env) -> NLambda (i, readback (i + 1) (eval env e))
  | VLambda (Name x, e, env) -> 
      NLambda (i, readback (i + 1)
        (eval (Environment.add env (VNeutral (VVar (x, i)))) e))
  | VArrow (a, b) ->
      NPi (i, readback i a, readback (i + 1) b)
  | VPi (x, v, e, env) -> 
      NPi (i, readback i v, readback (i + 1)
        (eval (Environment.add env (VNeutral (VVar (x, i)))) e))
  | VTimes (a, b) ->
      NSigma (i, readback i a, readback (i + 1) b)
  | VSigma (x, v, e, env) ->
      NSigma (i, readback i v, readback (i + 1)
        (eval (Environment.add env (VNeutral (VVar (x, i)))) e))
  | VFunction (l, env) -> NFunction (l, readback_env i env)
  | VUniverse i -> NUniverse i
  | VUnitType -> NUnitType
  | VUnit -> NUnit
  | VConstruct (c, vs) -> NConstruct (c, List.map (readback i) vs)
  | VNeutral n -> NNeutral (readback_neutral i n)

let are_values_equal x y = readback 0 x = readback 0 y
let are_equal env x y = (readback 0 (eval env x)) = (readback 0 (eval env y))
