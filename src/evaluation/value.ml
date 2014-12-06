open List
open Printf

open Abstract

(* the values associated with declarations need to be evaluated lazily; other
 * constructs evaluate to EnvValues *)
type environment_element = EnvValue of value | EnvThunk of value lazy_t
and value =
  | VPair of value * value
  | VLambda of binder * expression * environment_element list
  | VPi of binder * value * expression * environment_element list
  | VSigma of binder * value * expression * environment_element list
  | VFunction of (pattern * expression) list * environment_element list
  | VUniverse
  | VUnitType
  | VUnit
  (* constructor applied to arguments
   * values are in reverse order for efficiency, so the head of the list is the
   * last value applied to the constructor *)
  | VConstruct of string * value list

(* declarations in which types and bodies have been evaluated *)
type declaration_value =
  (* a seperate constructor for let rec is not needed here, so this constructor
   * is used for both let and let rec *)
  | VLet of string * value * value
  | VType of string * (binder * value) list * value * (string * value) list

