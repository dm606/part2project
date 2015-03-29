open Abstract
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

let rec refresh_neutral = function
  | VProj1 n1 -> VProj1 (refresh_neutral n1)
  | VProj2 n1 -> VProj2 (refresh_neutral n1)
  | VMeta id when Abstract.is_implicit id ->
      VMeta (Abstract.create_implicit_metavariable ())
  | VMeta _ | VVar _ as n -> n
  | _ as l -> l
and refresh =
  function
  | VPair (v1, v2) ->
      VPair (refresh v1, refresh v2)
  | VLambda _ as l -> l
  | VLambdaImplicit _ as l -> l
  | VArrow (a, b) ->
      VArrow (refresh a, refresh b)
  | VPi (b, v1, e, env) ->
      VPi (b, refresh v1, refresh_exp e, env)
  | VPiImplicit (b, v1, e, env) ->
      VPiImplicit (b, refresh v1, refresh_exp e, env)
  | VTimes (a, b) ->
      VTimes (refresh a, refresh b)
  | VSigma (b, v1, e, env) ->
      VSigma (b, refresh v1, refresh_exp e, env)
  | VFunction _ as l -> l
  | VUniverse i -> VUniverse i
  | VUnitType -> VUnitType
  | VUnit -> VUnit
  | VConstruct (c, l) ->
      VConstruct (c, List.map (fun (b, e) -> (b, refresh e)) l)
  | VNeutral n -> VNeutral (refresh_neutral n)
and refresh_exp = function
  | Pair (e1, e2) ->
      Pair (refresh_exp e1, refresh_exp e2)
  | Lambda (b, e) ->
      Lambda (b, refresh_exp e)
  | LambdaImplicit (b, e) ->
      LambdaImplicit (b, refresh_exp e)
  | Pi (b, e1, e2) ->
      Pi (b, refresh_exp e1, refresh_exp e2)
  | PiImplicit (b, e1, e2) ->
      PiImplicit (b, refresh_exp e1, refresh_exp e2)
  | Sigma (b, e1, e2) ->
      Sigma (b, refresh_exp e1, refresh_exp e2)
  | Function l -> Function (List.map (fun (p, e) -> (p, refresh_exp e)) l)
  | LocalDeclaration (d, e) -> raise (Failure "refresh_exp")
  | Application (e1, e2) -> Application (refresh_exp e1, refresh_exp e2)
  | ApplicationImplicit (e1, e2) ->
      ApplicationImplicit (refresh_exp e1, refresh_exp e2)
  | Universe i -> Universe i
  | UnitType -> UnitType
  | Unit -> Unit
  | Index i -> Index i
  | Constructor c -> Constructor c
  | Proj1 e -> Proj1 (refresh_exp e)
  | Proj2 e -> Proj2 (refresh_exp e)
  | Meta id when is_implicit id -> Meta (create_implicit_metavariable ())
  | Meta id -> Meta id

let get_binder_type (m, l) i = match List.nth l i with
  | _, `V v -> Some (refresh v)
  | _, `T t -> Some (refresh (Lazy.force t))
  | exception (Failure _) -> None

let get_constructor_types (m, l) c =
  if M.mem c m then List.map (fun (x, v) -> 
    match v with
    | `V v -> v
    | `T v -> Lazy.force v) (M.find c m) else []

let get_constructors_of_type (m, l) t =
  M.fold (fun ctor l rest ->
    let l = List.filter (fun (typ, _) -> typ = t) l in
    let l = List.rev_map (fun (typ, v) ->
      match v with
      | `V v -> ctor, v
      | `T v -> ctor, Lazy.force v) l in
    List.rev_append l rest) m []

let get_unique_constructor_type (m, l) c =
  if M.mem c m
  then match M.find c m with
  | [_, `V t] -> Some (refresh t)
  | [_, `T t] -> Some (refresh (Lazy.force t))
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
let subst_to_list subst = IM.fold (fun i v l -> (i, v)::l) subst []

let subst_value = IM.fold substitute_neutral_variable


let subst_add i v subst =
  (* doing this instead of simply IM.add means that the right hand of each
   * substitution does not contain the left hand side of any substitution *)
  IM.map (fun v2 -> Value.substitute_neutral_variable i v v2)
    (IM.add i (subst_value subst v) subst)

let subst_apply context subst = 
  let s i value = List.map (function
    | s, `V v -> s, `V (substitute_neutral_variable i value v)
    | s, `T _ -> raise (Failure "subst_apply")) in
  let apply i value (m, l) =
    (M.map (s i value) m, s i value l) in
  IM.fold apply subst context

let subst_env subst env = 
  Environment.map (subst_value subst) (fun x -> x) env

let (>>=) m f = match m with
  | None -> None
  | Some a -> f a

let rec occurs v i = match v with
  | VPair (v1, v2) -> occurs v1 i || occurs v2 i
  | VLambda _ -> false
  | VLambdaImplicit _ -> false
  | VArrow (a, b) -> occurs a i || occurs b i
  | VPi (_, v, _, _) -> occurs v i
  | VPiImplicit (_, v, _, _) -> occurs v i
  | VTimes (a, b) -> occurs a i || occurs b i
  | VSigma (_, v, _, _) -> occurs v i
  | VFunction _ -> false
  | VUniverse _ -> false
  | VUnitType -> false
  | VUnit -> false
  | VConstruct (_, l) -> List.exists (fun (_, v) -> occurs v i) l
  | VNeutral n -> neutral_occurs n i
and neutral_occurs n i = match n with
  | VVar (_, j) when i = j -> true
  | VVar _ -> false
  | VFunctionApplication (_, _, n) -> occurs n i
  | VFunctionApplicationImplicit (_, _, n) -> occurs n i
  | VApplication (n, v) -> neutral_occurs n i || occurs v i
  | VApplicationImplicit (n, v) -> neutral_occurs n i || occurs v i
  | VProj1 n -> neutral_occurs n i
  | VProj2 n -> neutral_occurs n i
  | VMeta _ -> false

let rec add_unify subst x i = function
  | VNeutral (VVar (x1, j)) when j > i ->
      add_unify subst x1 j (VNeutral (VVar (x, i)))
  | VNeutral (VVar (_, j)) when i = j -> Some subst
  | v ->
    if subst_mem i subst
    then mgu subst (subst_find i subst) v
    else Some (subst_add i v subst)

(* unification *)
and mgu subst v1 v2 = match v1, v2 with
  | VNeutral (VVar (x1, i)), VNeutral (VVar (x2, j)) when i = j ->
      Some subst
  (* variables unify than anything, unless they are already in the
   * substitution *)
  | VNeutral (VVar (x1, i)), v ->
      if occurs v i then None (* occurs check *)
      else add_unify subst x1 i v
   | v, VNeutral (VVar (x1, i)) ->
      if occurs v i then None (* occurs check *)
      else add_unify subst x1 i v
  (* atoms unify than themselves *)
  | VUniverse i, VUniverse j when i = j -> Some subst
  | VUnitType, VUnitType -> Some subst
  | VUnit, VUnit -> Some subst
  (* terms unify if they have the same structure and all subterms
   * are unify *)
  | VLambda (Underscore, e, env), VLambda (Underscore, e', env') ->
      if e = e' && env = env' then Some subst else None
  | VLambda (Name _, e, env), VLambda (Name _, e', env') ->
      if e = e' && env = env' then Some subst else None
  | VArrow (a, b), VArrow (a', b') ->
      mgu subst a a' >>= fun subst ->
      mgu subst b b'
  | VPi (_, v, e, env), VPi (_, v', e', env') ->
      mgu subst v v' >>= fun u ->
      if e = e' && env = env' then Some u else None
  | VTimes (a, b), VTimes (a', b') ->
      mgu subst a a' >>= fun subst ->
      mgu subst b b'
  | VSigma (_, v, e, env), VSigma (_, v', e', env') ->
      mgu subst v v' >>= fun u ->
      if e = e' && env = env' then Some u else None
  | VFunction _, VFunction _ -> if v1 = v2 then Some subst else None
  | VConstruct (c,  l), VConstruct (c', l') ->
      if c = c'
      then List.fold_left2
        (fun r (b, v) (b2, v2) ->
          if b = b2 then r >>= fun u -> mgu u v v2 else None) (Some subst) l l'
      else None
  | VNeutral (VFunctionApplication (l, env, n))
  , VNeutral (VFunctionApplication (l', env', n')) ->
      if l = l' && env = env'
      then mgu subst n n'
      else None
  | VNeutral (VApplication (n, v)), VNeutral (VApplication (n', v')) ->
      mgu subst (VNeutral n) (VNeutral n')
      >>= fun u ->
      mgu u v v'
  | VNeutral (VProj1 n), VNeutral (VProj1 n') ->
      mgu subst (VNeutral n) (VNeutral n')
  | VNeutral (VProj2 n), VNeutral (VProj2 n') ->
      mgu subst (VNeutral n) (VNeutral n')
  | VNeutral (VMeta _), _ | _, VNeutral (VMeta _) ->
      (* assume that the metavariables might unify *)
      Some subst
  (* if none of the above cases match, v1 cannot be unified with v2 *)
  | _ -> None

let unify v1 v2 = match mgu subst_empty v1 v2 with
  | None -> false
  | Some _ -> true

