open Abstract
open Value

exception Cannot_evaluate of string

val add_declarations : value Environment.t -> declaration list
  -> value Environment.t

val eval : value Environment.t -> expression -> value
