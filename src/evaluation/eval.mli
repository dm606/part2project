open Abstract
open Value

exception Cannot_evaluate of string
exception Pattern_match

val eval : value Environment.t -> expression -> value
