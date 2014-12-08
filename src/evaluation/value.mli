open Abstract

(* the values associated with declarations need to be evaluated lazily; other
 * constructs evaluate to EnvValues *)
type value =
  | VPair of value * value
  | VLambda of binder * expression * value Environment.t
  | VPi of binder * value * expression * value Environment.t
  | VSigma of binder * value * expression * value Environment.t
  | VFunction of (pattern * expression) list * value Environment.t
  | VUniverse
  | VUnitType
  | VUnit
  (* constructor applied to arguments
   * values are in reverse order for efficiency, so the head of the list is the
   * last value applied to the constructor *)
  | VConstruct of string * value list
  | VNeutral of neutral
and neutral =
  | VVar of int

