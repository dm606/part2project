open AbsConcrete

(** raised when an invalid value of type expr is used *)
exception Invalid_expression of string

(** raised when a construtor which has not been declared is used *)
exception Constructor_not_defined of string

(** the type of environments used for desugaring and resugaring *)
type envt

(** the empty environment *)
val empty_env : envt

(* mk_env (binders, constructors) returns the environment which contains the
 * names of binders in binders, and all of the constructors in constructors *)
val mk_env : string list * (string * string) list -> envt

(** The type of desugared expressions.
 * Expressions use de Bruijn indices, which are allocated as follows:
 * * One index is allocated in the body of a lambda abstraction, if the binder
 *     is not Underscore
 * * One index is allocated on the right of a pi or sigma type, if the binder is
 *     not underscore
 * * On the right hand side of a case, one index is allocated for every binder
 *     in the corresponding pattern; the indices increase from right to left
 * * In the body of a let or let rec, one index is allocated per let rec
 *     in the same declaration, only including the current declaration for a let
 *     rec. Declarations which appear before the current one get a lower index
 *     than those after it.
 * * In the body of a declaration, one index is allocated per let or let rec;
 *     closer lets get smaller indices.
 * * In the indices of a type or the type of a constructor, one index is
 *     assigned for each binder in the parameters of the type. The indices
 *     increase from right to left. *)
type expression =
  | Pair of expression * expression
  | Lambda of binder * expression
  | Pi of binder * expression * expression
  | Sigma of binder * expression * expression
  | Function of (pattern * expression) list
  | LocalDeclaration of declaration list * expression
  | Application of expression * expression
  | Universe
  | UnitType
  | Unit
  | Index of int (* de Bruijn index *)
  | Constructor of string
  | Proj1 of expression
  | Proj2 of expression
and binder =
  | Underscore
  (* Since de Bruijn indices are used, the name used is not necessary; it is
   * only kept for pretty-printing *)
  | Name of string 
and pattern =
  | PatternPair of pattern * pattern 
  | PatternApplication of string * pattern list (* Constructor application *)
  | PatternBinder of string (* name only needed for pretty-printing *)
  | PatternUnderscore
  | PatternInaccessible of expression
and declaration =
  (* Names only used for pretty-printing, except for constructor names *)
  | Let of string * expression * expression
  | LetRec of string * expression * expression
  | Type of string * (binder * expression) list
          * expression * (string * expression) list

(** determines if an expression references a constructor *)
val does_not_mention : string -> expression -> bool

(** adds each of the lets and let recs in the list to the environment *)
val add_all_declaration_binders : envt -> decl list -> envt

(** removes the syntactic sugar from the expression, in the given environment *)
val desugar_expression : envt -> exp -> expression

(** removes the syntactic sugar from the declarations, in the given environment *)
val desugar_declarations : envt -> decl list -> declaration list

(** adds syntactic sugar to the expression in the given environment for pretty
 * printing *)
val resugar_expression : envt -> expression -> exp

(** adds syntactic sugar to the declarations in the given environment for pretty
 * printing *)
val resugar_declarations : envt -> declaration list -> decl list

(** converts the given expression to a string *)
val print_expression : envt -> expression -> string

(** converts the given pattern to a string *)
val print_pattern : envt -> pattern -> string
