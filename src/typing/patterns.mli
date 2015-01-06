open Abstract
open Value

(** type checks a single pattern
 * add_binders checker i context env typ patt returns None, if the pattern does
 * not match typ, or Some (matched_value, i', context', env', subst), where
 *   * matched_value is a value which is matched by the patterns, with neutral
 *     variables for all binders
 *   * i' is the level to be used in checking the mody of the clause
 *   * context' is the context with all of the binders in the pattern added
 *   * env' is the environment with all of the binders in the pattern bound to
 *     fresh neutral variables 
 *   * subst is a substitution which maps neutral variables to a more specific
 *     type *)
val add_binders
  : (int -> Context.t -> value Environment.t -> expression -> value -> bool)
 -> int -> Context.t -> value Environment.t -> value -> pattern
 -> (value * int * Context.t * value Environment.t * Context.subst) option
