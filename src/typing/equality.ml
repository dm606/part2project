open Abstract
open Eval
open Value

type normal =
  | NPair of normal * normal
  | NLambda of int * normal
  | NPi of int * normal * normal
  | NSigma of int * normal * normal
  | NFunction of (pattern * expression) list 
               * [`N of normal | `D of declaration list] list
  | NUniverse
  | NUnitType
  | NUnit
  | NConstruct of string * normal list
  | NNeutral of normal_neutral
and normal_neutral =
  | NVar of int 
  | NFunctionApplication of (pattern * expression) list
                          * [`N of normal | `D of declaration list] list
                          * normal_neutral
  | NApplication of normal_neutral * normal
  | NProj1 of normal_neutral
  | NProj2 of normal_neutral

let rec readback i = 
  let readback_env i =
    Environment.map (fun v -> (`N (readback i v))) (fun d -> `D d) in
  let rec readback_neutral i = function
  | VVar i -> NVar i
  | VFunctionApplication (cases, env, v) ->
      NFunctionApplication (cases, readback_env i env, readback_neutral i v)
  | VApplication (v1, v2) ->
      NApplication (readback_neutral i v1, readback i v2)
  | VProj1 v -> NProj1 (readback_neutral i v)
  | VProj2 v -> NProj2 (readback_neutral i v) in

  function
  | VPair (v1, v2) -> NPair (readback i v1, readback i v2)
  | VLambda (Underscore, e, env) -> NLambda (i, readback (i + 1) (eval env e))
  | VLambda (_, e, env) -> 
      NLambda (i, readback (i + 1)
        (eval (Environment.add env (VNeutral (VVar i))) e))
  | VPi (Underscore, v, e, env) ->
      NPi (i, readback i v, readback (i + 1) (eval env e))
  | VPi (_, v, e, env) -> 
      NPi (i, readback i v, readback (i + 1)
        (eval (Environment.add env (VNeutral (VVar i))) e))
  | VSigma (Underscore, v, e, env) ->
      NSigma (i, readback i v, readback (i + 1) (eval env e))
  | VSigma (_, v, e, env) ->
      NSigma (i, readback i v, readback (i + 1)
        (eval (Environment.add env (VNeutral (VVar i))) e))
  | VFunction (l, env) -> NFunction (l, readback_env i env)
  | VUniverse -> NUniverse
  | VUnitType -> NUnitType
  | VUnit -> NUnit
  | VConstruct (c, vs) -> NConstruct (c, List.map (readback i) vs)
  | VNeutral n -> NNeutral (readback_neutral i n)

let are_equal env x y = (readback 0 (eval env x)) = (readback 0 (eval env y))
