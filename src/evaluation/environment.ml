open Abstract

type 'a elem = Val of 'a | Decl of declaration list | Thunk of 'a Lazy.t

type 'a t = 'a elem list

let empty = []

let add env v = (Val v)::env

let add_declarations env declarations = Decl (List.filter
  (function
   | Type (_, _, _, _) -> false
   | _ -> true) declarations) :: env

let get_declarations rest_decls xs = Decl xs

let rec add_declarations_as_thunks eval env =
  let rec add_decls rest rest_decls = function
    | [] -> List.fold_right (fun t env -> (Thunk t)::env) rest env
    | (Let (_, _, e) as d)::xs ->
        let new_env = (Decl (xs @ (List.rev rest_decls)))::env in
        add_decls ((lazy (eval new_env e))::rest) rest_decls xs
    | (LetRec (_, _, e) as d)::xs as l ->
        let new_env = (Decl (xs @ (List.rev (d::rest_decls))))::env in
        add_decls ((lazy (eval new_env e))::rest) (d::rest_decls) xs 
    | _::xs -> add_decls rest rest_decls xs in
  add_decls [] []

let rec get env eval i = match env, i with
  | [], i when i < 0 -> raise (Invalid_argument "get")
  | [], i -> raise (Failure "get")
  | (Val v)::_, 0 -> v
  | (Val _)::tl, i -> get tl eval (i - 1)
  | (Thunk t)::_, 0 -> Lazy.force t
  | (Thunk _)::tl, i -> get tl eval (i - 1)
  | (Decl d)::tl, i -> 
      let l = List.length d in
      if l > i
      then
        (match List.nth (add_declarations_as_thunks eval tl d) i with
         | Thunk t -> Lazy.force t
         | _ -> assert false)
      else get tl eval (i - l)

let map value decl = List.map (function
  | Val v -> value v
  | Thunk t -> value (Lazy.force t)
  | Decl d -> decl d)
