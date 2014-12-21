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

let rec reify = function
  | VPair (v1, v2) -> Pair (reify v1, reify v2)
  | VLambda _ -> raise (Cannot_reify "Cannot reify lambda abstractions")
  | VPi _ ->  raise (Cannot_reify "Cannot reify pi types")
  | VSigma _ -> raise (Cannot_reify "Cannot reify sigma types")
  | VFunction _ -> 
      raise (Cannot_reify "Cannot reify pattern-matching functions")
  | VUniverse -> Universe
  | VUnitType -> UnitType
  | VUnit -> Unit
  | VConstruct (c, l) ->
      List.fold_left (fun e v -> Application (e, reify v)) (Constructor c) l
  | VNeutral _ -> raise (Cannot_reify "Cannot reify neutral terms")

