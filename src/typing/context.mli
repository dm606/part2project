open Value

type v = [`V of value | `T of value Lazy.t]

(** Map from constructor names to pairs containing a type name and constructor
    type, and a list of pairs of binder names and the associated types. *)
type t = (string * v) list Map.Make(String).t * (string * v) list

(** The empty context. *)
val empty : t

(** Return the list of constructor names in the context, together with type
 *  names. *)
val get_constructor_names : t -> (string * string) list

(** Return the list of names of the binders in the context. *)
val get_binder_names : t -> string list

(** [add_binder context x typ] adds a binder with name [x] and type [typ] to
 *  [context]. *)
val add_binder : t -> string -> value -> t

(** [add_lazy_binder context x typ] adds a binder with name [x] and type [typ],
    computed lazily, to [context]. *)
val add_lazy_binder : t -> string -> value Lazy.t -> t

(** [add_constructor context x type_name typ] adds a constructor with name [x]
    and type [typ] to [context]. [type_name] should be the name of the type
    constructed.*)
val add_constructor : t -> string -> string -> value -> t

(** [add_lazy_constructor context x type_name typ] adds a constructor with name
    [x] and type [typ], computed lazily, to [context]. [type_name] should be the
    name of the type constructed. *)
val add_lazy_constructor : t -> string -> string -> value Lazy.t -> t

(** Removes all constructors with the given name from the context. *)
val remove_constructors_of_type : t -> string -> t

(** [get_binder_type context i] returns the type of the binder with de Bruijn
    index i *)
val get_binder_type : t -> int -> value option

(** Returns the types of the constructors with the given name. *)
val get_constructor_types : t -> string -> value list

(** Returns the type of the constructor with the given name, or None if there
    are either zero or several constructors with the name. *)
val get_unique_constructor_type : t -> string -> value option

(** Returns the names and types of all of the constructors with the given type
    name. *)
val get_constructors_of_type : t -> string -> (string * value) list

(** Substitutions of values for neutral variables. *)
type subst

(** [subst_find i subst] returns the value that [i] will be replaced with when
    [subst] is applied. *)
val subst_find : int -> subst -> value

(** [subst_add i v subst] returns a substitution which maps [i] to [v], and
    otherwise acts as [subst]. *)
val subst_add : int -> value -> subst -> subst

(** The empty substitution. *)
val subst_empty : subst

(** [subst_mem i subst] returns true iff [subst] contains an entry for [i]. *)
val subst_mem : int -> subst -> bool

(** Applies a substitution to all of the values in a context. *)
val subst_apply : t -> subst -> t

(** Applies a substitution to a value. *)
val subst_value : subst -> value -> value

(** Applies a substitution to all of the values in the environment. *)
val subst_env : subst -> value Environment.t -> value Environment.t

(** Returns a representation of the substitution as a list. *)
val subst_to_list : subst -> (int * value) list

(** [mgu subst v1 v2] returns the most general substitution s of the form s'
    composed with [subst] such that s applied to [v1] is equal to s applied to
    [v2], or None if the values cannot be unified. *)
val mgu : subst -> value -> value -> subst option

(** [unify subst v1 v2] returns true iff [v1] can be unified with [v2]
    respecting [subst]. *)
val unify : value -> value -> bool

