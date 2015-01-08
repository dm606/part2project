open Value

type t

val empty : t
val get_constructor_names : t -> (string * string) list
val get_binder_names : t -> string list
val add_binder : t -> string -> value -> t
val add_lazy_binder : t -> string -> value Lazy.t -> t
val add_constructor : t -> string -> string -> value -> t
val add_lazy_constructor : t -> string -> string -> value Lazy.t -> t
val remove_constructors_of_type : t -> string -> t
val get_binder_type : t -> int -> value option
val check_constructor_type : t -> string -> value -> bool
val get_constructor_types : t -> string -> value list
val get_unique_constructor_type : t -> string -> value option
val get_constructors_of_type : t -> string -> (string * value) list

type subst

val subst_find : int -> subst -> value
val subst_add : int -> value -> subst -> subst
val subst_empty : subst
val subst_mem : int -> subst -> bool
val subst_apply : t -> subst -> t
val subst_value : subst -> value -> value
val subst_env : subst -> value Environment.t -> value Environment.t
val subst_to_list : subst -> (int * value) list
