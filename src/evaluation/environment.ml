type 'a elem = Val of 'a | Thunk of 'a Lazy.t

type 'a t = 'a elem list

let empty = []
let add env v = (Val v)::env
let add_thunk env t = (Thunk t)::env
(* eta-expanded because of the value restriction *)
let add_thunks env l = List.fold_left add_thunk env l
let get env i = match List.nth env i with
  | Val v -> v
  | Thunk t -> Lazy.force t
