open Abstract
open Value

exception Cannot_evaluate of string
exception Pattern_match
exception Match_neutral

val eval' : (value Environment.t -> meta_id -> expression option)
         -> (value Environment.t -> declaration list -> unit)
         -> value Environment.t -> expression -> value
val eval : (value Environment.t -> meta_id -> expression option) -> value Environment.t -> expression
         -> value
