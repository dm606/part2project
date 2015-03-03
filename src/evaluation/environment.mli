open Abstract

type 'a elem = Val of 'a | Decl of declaration list

type 'a t = 'a elem list

val empty : 'a t
val add : 'a t -> 'a -> 'a t
val add_declarations : 'a t -> Abstract.declaration list -> 'a t
val get : 'a t -> ('a t -> Abstract.expression -> 'a) -> int -> 'a
val map_to_list : ('a -> 'b) -> (Abstract.declaration list -> 'b) -> 'a t
               -> 'b list
val map : ('a -> 'b) -> (Abstract.declaration list -> Abstract.declaration list)
       -> 'a t -> 'b t
val find : ('a -> bool) -> 'a t -> int option
