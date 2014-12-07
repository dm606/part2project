open AbsConcrete

(* The type of desugared expressions.
 * Expressions use de Bruijn indices, which are allocated as follows:
 * * One index is allocated in the body of a lambda abstraction, if the binder
 *     is not Underscore
 * * One index is allocated on the right of a pi or sigma type, if the binder is
 *     not underscore
 * * On the right hand side of a case, one index is allocated for every binder
 *     in the corresponding pattern; the indices increase from right to left
 * * In the body of a let or let rec, one index is allocated per let and let rec
 *     in the same declaration, only including the current declaration for a let
 *     rec. Declarations which appear the current one get a lower index than
 *     those after it.
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
and declaration =
  (* Names only used for pretty-printing, except for constructor names *)
  | Let of string * expression * expression
  | LetRec of string * expression * expression
  | Type of string * (binder * expression) list
          * expression * (string * expression) list

val add_all_declaration_binders : string list * string list -> decl list
  -> string list * string list
val desugar_expression : string list * string list -> exp -> expression
val desugar_declarations : string list * string list -> decl list
  -> declaration list
val resugar_declarations : string list * string list -> declaration list
  -> decl list
