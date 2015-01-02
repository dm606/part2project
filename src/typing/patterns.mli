open Abstract
open Value

val add_binders : int -> Context.t -> value Environment.t -> value -> pattern
               -> (int * Context.t * value Environment.t * Context.subst) option
