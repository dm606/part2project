open Abstract
open Value

type normal_envt

val empty_envt : normal_envt

type normal =
  | NPair of normal * normal
  | NLambda of string * int * normal
  | NPi of string * int * normal * normal
  | NSigma of string * int * normal * normal
  | NFunction of (pattern * expression) list * normal_envt
  | NUniverse of int
  | NUnitType
  | NUnit
  | NConstruct of string * normal list
  | NNeutral of normal_neutral
and normal_neutral =
  | NVar of string * int 
  | NFunctionApplication of (pattern * expression) list
                          * normal_envt
                          * normal
  | NApplication of normal_neutral * normal
  | NProj1 of normal_neutral
  | NProj2 of normal_neutral
  | NMeta of meta_id

(** the type of a unification problem *)
type constraints

(** a collection of constraints which are always satisfied *)
val no_constraints : constraints

(** [always_satisfied c] returns true iff the constraints in [c] are always
    satisfied, irrespective of the values of metavariables *)
val always_satisfied : constraints -> bool 

(** [never_satisfied c] returns true iff the constraints in [c] are never
    satisfied, irrespective of the values of metavariables *)
val never_satisfied : constraints -> bool 

(** [add_metavariable c id typ] adds a metavariable with id [id] and type [typ] to
    [c]. If [c] already has a type for the metavariable, it is overwritten *)
val add_metavariable : constraints -> meta_id -> value -> constraints

(** [has_metavariable c id] returns true iff [c] has a type for the metavariable
    [id] *)
val has_metavariable : constraints -> meta_id -> bool

(** [get_metavariable c id] returns the type of metavariable [id], or raises
    [Not_found] if [c] does not have a type. *)
val get_metavariable : constraints -> meta_id -> value

(** [get_metavariable_assignment constraints id] returns None if metavariable
    [id] has not been assigned in [constraints], or [Some value] if the
    metavariable has been assigned to [value] in constraints *)
val get_metavariable_assignment : constraints -> meta_id -> value option

(** [test_value_equality i c x y] returns constraints, where [x] and [y] are equal
    if the constraints in [constraints] are satisfied. There must be no neutral
    variables in [x] or [y] with a value greater than or equal to [i]. The constraints
    returned contains all constraints in [c]. *)
val test_equality : int -> constraints -> value -> value -> constraints

(** [test_expression_equality env e1 e2] returns constraints, where [x] and [y] are
    equal iff the constraints in [constraints] are satisfied *)
val test_expression_equality :
      value Environment.t -> Abstract.expression -> Abstract.expression ->
        constraints 

(** prints the constraints to stdout *)
val print_constraints : constraints -> unit
