open Abstract
open Value

exception Cannot_evaluate of string
exception Pattern_match
exception Match_neutral

val eval' : (meta_id -> value option)
         -> (value Environment.t -> declaration list -> unit)
         -> value Environment.t -> expression -> value
val eval : (meta_id -> value option) -> value Environment.t -> expression
         -> value
