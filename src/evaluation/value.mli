open Abstract

exception Cannot_reify of string

(* the values associated with declarations need to be evaluated lazily; other
 * constructs evaluate to EnvValues *)
type value =
  | VPair of value * value
  | VLambda of binder * expression * value Environment.t
  | VPi of string * value * expression * value Environment.t
  | VArrow of value * value (* Π (_ : A) . B *)
  | VSigma of string * value * expression * value Environment.t
  | VTimes of value * value (* Σ (_ : A) . B *)
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
  (* application of a neutral value to a function defined by pattern matching *)
  | VFunctionApplication of (pattern * expression) list
                          * value Environment.t * value
  | VApplication of neutral * value
  | VProj1 of neutral
  | VProj2 of neutral

val reify : (value Environment.t -> expression -> value) -> value -> expression
val substitute_neutral_variable : int -> value -> value -> value
