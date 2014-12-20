open Value

module M = Map.Make(String)

type v = [`V of value | `T of value Lazy.t]

type t = v list M.t * (string * v) list

let empty = (M.empty, [])

let get_constructor_names (m, l) = List.map (fun (x, y) -> x) (M.bindings m)

let get_binder_names (m, l) = List.map (fun (x, y) -> x) l

let add_binder (m, l) x v = (m, (x, `V v)::l)

let add_lazy_binder (m, l) x t = (m, (x, `T t)::l)

let add_constructor (m, l) x v =
    if M.mem x m then (M.add x ((`V v)::M.find x m) m, l)
    else (M.add x [`V v] m, l)

let add_lazy_constructor (m, l) x t =
    if M.mem x m then (M.add x ((`T t)::M.find x m) m, l)
    else (M.add x [`T t] m, l)

let get_binder_type (m, l) i = match List.nth l i with
  | _, `V v -> Some v
  | _, `T t -> Some (Lazy.force t)
  | exception (Failure _) -> None

let compare_types t = function
  | `V t2 -> t = t2
  | `T thunk -> t = (Lazy.force thunk)

let check_constructor_type (m, l) c t =
  M.mem c m && List.exists (compare_types t) (M.find c m)

let get_unique_constructor_type (m, l) c =
  if M.mem c m
  then match M.find c m with
  | [`V t] -> Some t
  | [`T t] -> Some (Lazy.force t)
  | _ -> None
  else None
