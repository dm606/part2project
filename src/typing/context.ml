open Value

module M = Map.Make(String)

type v = [`V of value | `T of value Lazy.t]

(* map from constructor names to pairs containing a type name and constructor
 * type, and a list of pairs of binder names and the associated types *)
type t = (string * v) list M.t * (string * v) list

let empty = (M.empty, [])

let get_constructor_names (m, l) =
  let conv ctor = List.map (fun (typ, _) -> (ctor, typ)) in
  M.fold (fun ctor l rest -> List.rev_append (conv ctor l) rest) m []

let get_binder_names (m, l) = List.map (fun (x, y) -> x) l

let add_binder (m, l) x v = (m, (x, `V v)::l)

let add_lazy_binder (m, l) x t = (m, (x, `T t)::l)

let add_constructor (m, l) x type_name v =
    if M.mem x m then (M.add x ((type_name, `V v)::M.find x m) m, l)
    else (M.add x [type_name, `V v] m, l)

let add_lazy_constructor (m, l) x type_name t =
    if M.mem x m then (M.add x ((type_name, `T t)::M.find x m) m, l)
    else (M.add x [type_name, `T t] m, l)

let remove_constructors_of_type (m, l) type_name = 
    M.map (List.filter (fun (t, _) -> t <> type_name)) m, l

let get_binder_type (m, l) i = match List.nth l i with
  | _, `V v -> Some v
  | _, `T t -> Some (Lazy.force t)
  | exception (Failure _) -> None

let compare_types t = function
  | _, `V t2 -> t = t2
  | _, `T thunk -> t = (Lazy.force thunk)

let check_constructor_type (m, l) c t =
  M.mem c m && List.exists (compare_types t) (M.find c m)

let get_constructor_types (m, l) c =
  if M.mem c m then List.map (fun (x, v) -> 
    match v with
    | `V v -> v
    | `T v -> Lazy.force v) (M.find c m) else []

let get_unique_constructor_type (m, l) c =
  if M.mem c m
  then match M.find c m with
  | [_, `V t] -> Some t
  | [_, `T t] -> Some (Lazy.force t)
  | _ -> None
  else None

(* maps from ints to 'as *)
module IM = Map.Make(struct
  type t = int
  let compare : int -> int -> int = compare
end)

type subst = value IM.t

let subst_find = IM.find
let subst_mem = IM.mem
let subst_empty = IM.empty
let subst_add = IM.add
let subst_to_list subst = IM.fold (fun i v l -> (i, v)::l) subst []

let subst_value = IM.fold substitute_neutral_variable

let subst_apply context subst = 
  let s i value = List.map (function
    | s, `V v -> s, `V (substitute_neutral_variable i value v)
    | s, `T _ -> raise (Failure "subst_apply")) in
  let apply i value (m, l) =
    (M.map (s i value) m, s i value l) in
  IM.fold apply subst context

let subst_env subst env = 
  Environment.map (subst_value subst) (fun x -> x) env
