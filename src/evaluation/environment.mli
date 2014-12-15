type 'a t

val empty : 'a t
val add : 'a t -> 'a -> 'a t
val add_declarations : 'a t -> Abstract.declaration list -> 'a t
val get : 'a t -> ('a t -> Abstract.expression -> 'a) -> int -> 'a
val map : ('a -> 'b) -> (Abstract.declaration list -> 'b) -> 'a t -> 'b list
