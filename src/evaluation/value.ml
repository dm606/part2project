open Abstract

exception Cannot_reify of string

type value =
  | VPair of value * value
  | VLambda of binder * expression * value Environment.t
  | VPi of string * value * expression * value Environment.t
  | VArrow of value * value (* Π (_ : A) . B *)
  | VSigma of string * value * expression * value Environment.t
  | VTimes of value * value (* Σ (_ : A) . B *)
  | VFunction of (pattern * expression) list * value Environment.t
  | VUniverse of int
  | VUnitType
  | VUnit
  | VConstruct of string * value list
  | VNeutral of neutral
and neutral =
  | VVar of int
  (* the value should contain a neutral variable *)
  | VFunctionApplication of (pattern * expression) list
                          * value Environment.t * value
  | VApplication of neutral * value
  | VProj1 of neutral
  | VProj2 of neutral

let reify eval = 
  let rec reify = function
    | VPair (v1, v2) -> Pair (reify v1, reify v2)
    | VLambda _ -> raise (Cannot_reify "Cannot reify lambda abstractions")
    | VArrow (a, b) -> 
        Pi (Underscore, reify a, reify b) 
    | VPi (_, _, _, _) ->
        raise (Cannot_reify
          "Cannot reify pi types where the LHS is bound to a name")
    | VTimes (a, b) ->
        Sigma (Underscore, reify a, reify b)
    | VSigma _ -> raise (Cannot_reify "Cannot reify sigma types")
    | VFunction _ -> 
        raise (Cannot_reify "Cannot reify pattern-matching functions")
    | VUniverse i -> Universe i
    | VUnitType -> UnitType
    | VUnit -> Unit
    | VConstruct (c, l) ->
        List.fold_left (fun e v -> Application (e, reify v)) (Constructor c) l
    | VNeutral _ -> raise (Cannot_reify "Cannot reify neutral terms") in
  reify

let rec neutral_contains i = function
  | VVar j when i = j -> true
  | VVar i -> false
  | VFunctionApplication (_, _, n) -> contains i n
  | VApplication (n, v) -> neutral_contains i n || contains i v
  | VProj1 n -> neutral_contains i n
  | VProj2 n -> neutral_contains i n
and contains i = function 
  | VPair (v1, v2) -> contains i v1 || contains i v2
  | VLambda _ -> false
  | VArrow (a, b) -> contains i a || contains i b
  | VPi (_, a, _, _) -> contains i a
  | VTimes (a, b) -> contains i a || contains i b
  | VSigma (_, a, _, _) -> contains i a
  | VFunction (_, _) -> false
  | VUniverse i -> false
  | VUnitType -> false
  | VUnit -> false
  | VConstruct (_, l) -> List.exists (contains i) l
  | VNeutral n -> neutral_contains i n

let rec neutral_substitute_neutral_variable i n = function
  | VVar j when j = i -> n
  | VVar j -> VVar j
  | VFunctionApplication (l, env, n1) ->
      VFunctionApplication (l, env
                          , substitute_neutral_variable i (VNeutral n) n1)
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
  | VArrow (a, b) ->
      VArrow (substitute_neutral_variable i v a
            , substitute_neutral_variable i v b)
  | VPi (b, v1, e, env) ->
      VPi (b, substitute_neutral_variable i v v1, e, subst_env env)
  | VTimes (a, b) ->
      VTimes (substitute_neutral_variable i v a
            , substitute_neutral_variable i v b)
  | VSigma (b, v1, e, env) ->
      VSigma (b, substitute_neutral_variable i v v1, e, subst_env env)
  | VFunction _ as f -> f
  | VUniverse i -> VUniverse i
  | VUnitType -> VUnitType
  | VUnit -> VUnit
  | VConstruct (c, l) ->
      VConstruct (c, List.map (substitute_neutral_variable i v) l)
  | VNeutral (VVar j) when i = j -> v
  | VNeutral n ->
      if neutral_contains i n then
        match v with
        | VNeutral n1 -> VNeutral (neutral_substitute_neutral_variable i n1 n)
        | _ -> raise (Failure "substitute_neutral_variable")
      else VNeutral n

let rec lift_neutral a = function
  | VVar i -> VVar (i + a)
  | VFunctionApplication _ -> raise (Failure "lift_neutral")
  | VApplication (n, v) -> VApplication (lift_neutral a n, lift a v)
  | VProj1 n -> VProj1 (lift_neutral a n)
  | VProj2 n -> VProj2 (lift_neutral a n)
and lift a = function
  | VPair (v1, v2) -> VPair (lift a v1, lift a v2)
  | VArrow (v1, v2) -> VArrow (lift a v1, lift a v2)
  | VTimes (v1, v2) -> VTimes (lift a v1, lift a v2)
  | VUniverse i -> VUniverse i
  | VUnitType -> VUnitType
  | VUnit -> VUnit
  | VConstruct (c, l) -> VConstruct (c, List.map (lift a) l)
  | VNeutral n -> VNeutral (lift_neutral a n)
  | VLambda _ | VPi _ | VSigma _ | VFunction _ -> raise (Failure "lift")
