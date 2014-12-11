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

 val are_equal : value Environment.t -> Abstract.expression
              -> Abstract.expression -> bool
