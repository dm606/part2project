open Abstract
open Value

val add_declarations : environment_element list -> declaration list
  -> environment_element list

val eval : environment_element list -> expression -> value
