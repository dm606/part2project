open Abstract
open Environment
open Value

(** raised when an issue (such as a typing error) with the declaration means
 * that the termination checker cannot determine if it terminates or not *)
exception Cannot_check_termination of string * string 

(** check_termination env l returns None if all of the declarations in l
 * terminate, and Some x if the declaration of x may not terminate *)
val check_termination : value Environment.t -> declaration list -> string option
