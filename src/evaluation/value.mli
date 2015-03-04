open Abstract

exception Cannot_reify of string

(* the values associated with declarations need to be evaluated lazily; other
 * constructs evaluate to EnvValues *)
type value =
  | VPair of value * value
  | VLambda of binder * expression * value Environment.t
  | VLambdaImplicit of binder * expression * value Environment.t
  | VPi of string * value * expression * value Environment.t
  | VPiImplicit of string * value * expression * value Environment.t
  | VArrow of value * value (* Π (_ : A) . B *)
  | VSigma of string * value * expression * value Environment.t
  | VTimes of value * value (* Σ (_ : A) . B *)
  | VFunction of (pattern * expression) list * value Environment.t
  | VUniverse of int
  | VUnitType
  | VUnit
  (* Constructor applied to arguments.
   * Values are in reverse order for efficiency, so the head of the list is the
   * last value applied to the constructor. The booleans indicate whether the
   * application is implicit *)
  | VConstruct of string * (bool * value) list
  | VNeutral of neutral
and neutral =
  (* neutral variables are named for pretty-printing *)
  | VVar of string * int
  (* application of a neutral value to a function defined by pattern matching *)
  | VFunctionApplication of (pattern * expression) list
                          * value Environment.t * value
  | VFunctionApplicationImplicit of (pattern * expression) list
                          * value Environment.t * value
  | VApplication of neutral * value
  | VApplicationImplicit of neutral * value
  | VProj1 of neutral
  | VProj2 of neutral
  | VMeta of meta_id

val reify : (value Environment.t -> expression -> value) -> value -> expression
val substitute_neutral_variable : int -> value -> value -> value
val lift : int -> value -> value
