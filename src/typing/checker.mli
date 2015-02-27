open Abstract
open Value

type typing_result

val succeeded : typing_result -> bool
val get_type : typing_result -> value
val get_binder_types : typing_result -> (string * value) list
val get_expression : typing_result -> expression
val get_declarations : typing_result -> declaration list
val get_constructor_types : typing_result -> (string * string * value) list
val get_constraints : typing_result -> Equality.constraints
val print_error : out_channel -> typing_result -> unit
val print_trace : out_channel -> typing_result -> unit

val infer_type : Equality.constraints -> value Environment.t -> Context.t
                 -> expression -> typing_result

val check_type : Equality.constraints -> value Environment.t -> Context.t
                 -> expression -> value -> typing_result

val check_declarations : Equality.constraints -> value Environment.t
                 -> Context.t -> declaration list -> typing_result

