open Value

type t

val empty : t
val get_constructor_names : t -> string list
val get_binder_names : t -> string list
val add_binder : t -> string -> value -> t
val add_lazy_binder : t -> string -> value Lazy.t -> t
val add_constructor : t -> string -> value -> t
val add_lazy_constructor : t -> string -> value Lazy.t -> t
val get_binder_type : t -> int -> value option
val check_constructor_type : t -> string -> value -> bool
val get_unique_constructor_type : t -> string -> value option
