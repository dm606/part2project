open Abstract
open Value

exception Cannot_pattern_match

(** type checks a single pattern
    add_binders checker i constraints context env typ patt returns None, if the
    pattern does not match typ, or Some (matched_value, i', context', env',
    subst), where
     * matched_value is a value which is matched by the patterns, with neutral
       variables for all binders
     * i' is the level to be used in checking the mody of the clause context' is
     * the context with all of the binders in the pattern added env' is the
     * environment with all of the binders in the pattern bound to
       fresh neutral variables 
     * subst is a substitution which maps neutral variables to a more specific
       type *)
      
val add_binders :
  (int -> Equality.constraints -> Context.t -> value Environment.t -> expression
    -> value -> (expression * Equality.constraints) option)
  -> int -> Equality.constraints -> Context.t -> value Environment.t -> value
  -> pattern
  -> (value * int * Equality.constraints * Context.t * value Environment.t
      * Context.subst) option

(** checks that the list of patterns form a covering
    cover i patterns typ value returns None if, for each value v of type typ and
    of the form value, there is at least one patterns in patterns which matches
    v. i must be such that all neutral variables j with j >= i are fresh. A
    return value of Some value indicates that values of the form value are not
    covered.
   
    The implementation is based on the algorithm given by Norell *)
val cover : int -> Equality.constraints -> Context.t -> pattern list -> value -> value option
