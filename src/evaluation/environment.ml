open Abstract

type 'a elem = Val of 'a | Decl of declaration list

type 'a t = 'a elem list

let empty = []

let add env v = (Val v)::env

let add_declarations env declarations = 
  let ds = List.filter
    (function
     | Type (_, _, _, _) -> false
     | _ -> true) declarations in
  if ds = [] then env else Decl ds :: env

let rec add_declarations_as_values eval env =
  let add l env = if l = [] then env else (Decl l)::env in
  let rec add_decls rest rest_decls = function
    | [] -> List.fold_right (fun v env -> (Val v)::env) rest env
    | (Let (_, _, e))::xs ->
        let new_env = add (xs @ (List.rev rest_decls)) env in
        add_decls ((eval new_env e)::rest) rest_decls xs
    | (LetRec (_, _, e) as d)::xs ->
        let new_env = add (xs @ (List.rev (d::rest_decls))) env in
        add_decls ((eval new_env e)::rest) (d::rest_decls) xs 
    | _::xs -> add_decls rest rest_decls xs in
  add_decls [] []

let rec get env eval i = match env, i with
  | [], i when i < 0 -> raise (Invalid_argument "get")
  | [], i -> raise (Failure "get")
  | (Val v)::_, 0 -> v
  | (Val _)::tl, i -> get tl eval (i - 1)
  | (Decl d)::tl, i -> 
      let l = List.length d in
      if l > i
      then
        (match List.nth (add_declarations_as_values eval tl d) i with
         | Val v -> v
         | _ -> assert false)
      else get tl eval (i - l)

let map_to_list value decl = List.map (function
  | Val v -> value v
  | Decl d -> decl d)

let map value decl = List.map (function
  | Val v -> Val (value v)
  | Decl d -> Decl (decl d))

let find p =
  let rec aux index = function
    | [] -> None
    | (Val x)::xs when p x -> Some index
    | (Val _)::xs -> aux (index + 1) xs
    | (Decl d)::xs -> aux (index + (List.length d)) xs in
  aux 0
