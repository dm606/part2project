open Abstract

exception Cannot_reify of string

type value =
  | VPair of value * value
  | VLambda of binder * expression * value Environment.t
  | VPi of binder * value * expression * value Environment.t
  | VSigma of binder * value * expression * value Environment.t
  | VFunction of (pattern * expression) list * value Environment.t
  | VUniverse
  | VUnitType
  | VUnit
  | VConstruct of string * value list
  | VNeutral of neutral
and neutral =
  | VVar of int
  | VFunctionApplication of (pattern * expression) list
                          * value Environment.t * neutral
  | VApplication of neutral * value
  | VProj1 of neutral
  | VProj2 of neutral

let reify eval = 
  let rec reify = function
    | VPair (v1, v2) -> Pair (reify v1, reify v2)
    | VLambda _ -> raise (Cannot_reify "Cannot reify lambda abstractions")
    | VPi (Underscore, a, b, env) -> 
        Pi (Underscore, reify a, reify (eval env b)) 
    | VPi (Name _, _, _, _) ->
        raise (Cannot_reify
          "Cannot reify pi types where the LHS is bound to a name")
    | VSigma _ -> raise (Cannot_reify "Cannot reify sigma types")
    | VFunction _ -> 
        raise (Cannot_reify "Cannot reify pattern-matching functions")
    | VUniverse -> Universe
    | VUnitType -> UnitType
    | VUnit -> Unit
    | VConstruct (c, l) ->
        List.fold_left (fun e v -> Application (e, reify v)) (Constructor c) l
    | VNeutral _ -> raise (Cannot_reify "Cannot reify neutral terms") in
  reify

let rec neutral_substitute_neutral_variable i n = function
  | VVar j when j = i -> n
  | VVar j -> VVar j
  | VFunctionApplication (l, env, n1) ->
      VFunctionApplication (l, env, neutral_substitute_neutral_variable i n n1)
  | VApplication (n1, v) ->
      VApplication (neutral_substitute_neutral_variable i n n1
                  , substitute_neutral_variable i (VNeutral n) v)
  | VProj1 n1 -> VProj1 (neutral_substitute_neutral_variable i n n1)
  | VProj2 n1 -> VProj2 (neutral_substitute_neutral_variable i n n1)
and substitute_neutral_variable i v =
  let subst_env env =
    Environment.map (substitute_neutral_variable i v) (fun x -> x) env in

  function
  | VPair (v1, v2) ->
      VPair (substitute_neutral_variable i v v1
           , substitute_neutral_variable i v v2)
  | VLambda _ as l -> l
  | VPi (b, v1, e, env) ->
      VPi (b, substitute_neutral_variable i v v1, e, subst_env env)
  | VSigma (b, v1, e, env) ->
      VSigma (b, substitute_neutral_variable i v v1, e, subst_env env)
  | VFunction _ as f -> f
  | VUniverse -> VUniverse
  | VUnitType -> VUnitType
  | VUnit -> VUnit
  | VConstruct (c, l) ->
      VConstruct (c, List.map (substitute_neutral_variable i v) l)
  | VNeutral (VVar j) when i = j -> v
  | VNeutral n ->
      let rec contains = function
        | VVar j when i = j -> true
        | VVar i -> false
        | VFunctionApplication (_, _, n) -> contains n
        | VApplication (n, _) -> contains n
        | VProj1 n -> contains n
        | VProj2 n -> contains n in
      if contains n then
        match v with
        | VNeutral n1 -> VNeutral (neutral_substitute_neutral_variable i n1 n)
        | _ -> raise (Failure "substitute_neutral_variable")
      else VNeutral n
