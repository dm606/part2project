open Abstract
open Value

val add_declarations : value Environment.t -> declaration list
  -> value Environment.t

val eval : value Environment.t -> expression -> value
