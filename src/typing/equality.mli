open Abstract
open Value

type normal =
  | NPair of normal * normal
  | NLambda of int * normal
  | NPi of int * normal * normal
  | NSigma of int * normal * normal
  | NFunction of (pattern * expression) list * [`N of normal | `D of declaration list] list
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

val readback : int -> value -> normal

val are_equal : value Environment.t -> Abstract.expression
             -> Abstract.expression -> bool
