type 'a t

val empty : 'a t
val add : 'a t -> 'a -> 'a t
val add_thunk : 'a t -> 'a Lazy.t -> 'a t
val add_thunks : 'a t -> 'a Lazy.t list -> 'a t
val get : 'a t -> int -> 'a
