open Abstract
open Eval
open Format
open Value

module MM = Map.Make(struct
  type t = Abstract.meta_id
  let compare = Abstract.meta_id_compare
end)

exception Constraint_function

type normal_envt = [`N of normal | `D of declaration list] list
and normal =
  | NPair of normal * normal
  (* strings are names of binders; they are used for pretty-printing only *)
  | NLambda of string * int * normal
  | NLambdaImplicit of string * int * normal
  | NPi of string * int * normal * normal
  | NPiImplicit of string * int * normal * normal
  | NSigma of string * int * normal * normal
  | NFunction of (pattern * expression) list 
               * normal_envt
  | NUniverse of int
  | NUnitType
  | NUnit
  | NConstruct of string * (bool * normal) list
  | NNeutral of normal_neutral
and normal_neutral =
  | NVar of string * int
  | NFunctionApplication of (pattern * expression) list
                          * normal_envt
                          * normal
  | NFunctionApplicationImplicit of (pattern * expression) list
                                  * normal_envt
                                  * normal
  | NApplication of normal_neutral * normal
  | NApplicationImplicit of normal_neutral * normal
  | NProj1 of normal_neutral
  | NProj2 of normal_neutral
  | NMeta of meta_id

let rec no_neutral_variables_pred_neutral p = function
  | NVar (_, i) -> not (p i)
  | NFunctionApplication (_, _, n) -> no_neutral_variables_pred p n
  | NFunctionApplicationImplicit (_, _, n) -> no_neutral_variables_pred p n
  | NApplication (x, y) -> no_neutral_variables_pred_neutral p x && no_neutral_variables_pred p y
  | NApplicationImplicit (x, y) -> no_neutral_variables_pred_neutral p x && no_neutral_variables_pred p y
  | NProj1 x -> no_neutral_variables_pred_neutral p x
  | NProj2 x -> no_neutral_variables_pred_neutral p x
  | NMeta id -> true
and no_neutral_variables_pred p = function
  | NPair (x, y) -> no_neutral_variables_pred p x && no_neutral_variables_pred p y
  | NLambda (_, _, n) -> no_neutral_variables_pred p n
  | NLambdaImplicit (_, _, n) -> no_neutral_variables_pred p n
  | NPi (_, _, x, y) -> no_neutral_variables_pred p x && no_neutral_variables_pred p y
  | NPiImplicit (_, _, x, y) -> no_neutral_variables_pred p x && no_neutral_variables_pred p y
  | NSigma (_, _, x, y) -> no_neutral_variables_pred p x && no_neutral_variables_pred p y
  | NFunction _ -> true
  | NUniverse _ | NUnitType | NUnit -> true
  | NConstruct (_, l) -> List.for_all (fun (_, v) -> no_neutral_variables_pred p v) l
  | NNeutral n -> no_neutral_variables_pred_neutral p n

let no_neutral_variables = no_neutral_variables_pred (fun _ -> true)
let no_neutral_variables_neutral = no_neutral_variables_pred_neutral (fun _ -> true)

let rec no_neutral_value = function
  | VPair (v1, v2) -> no_neutral_value v1 && no_neutral_value v2
  | VLambda (_, _, env) -> no_neutral_env env
  | VLambdaImplicit (_, _, env) -> no_neutral_env env
  | VPi (_, v, _, env) -> no_neutral_value v && no_neutral_env env
  | VPiImplicit (_, v, _, env) -> no_neutral_value v && no_neutral_env env
  | VArrow (v1, v2) -> no_neutral_value v1 && no_neutral_value v2
  | VSigma (_, v, _, env) -> no_neutral_value v && no_neutral_env env
  | VTimes (v1, v2) -> no_neutral_value v1 && no_neutral_value v2
  | VFunction (_, env) -> no_neutral_env env
  | VUniverse _ | VUnitType | VUnit -> true
  | VConstruct (_, l) -> List.for_all (fun (_, v) -> no_neutral_value v) l
  | VNeutral _ -> false
and no_neutral_env env =
  List.for_all (fun x -> x)
    (Environment.map_to_list no_neutral_value (fun _ -> false) env)

let rec no_metavariables_pred_expression p = function
  | Pair (e1, e2) ->
      no_metavariables_pred_expression p e1 && no_metavariables_pred_expression p e2
  | Lambda (_, e) -> no_metavariables_pred_expression p e
  | LambdaImplicit (_, e) -> no_metavariables_pred_expression p e
  | Pi (_, e1, e2) ->
      no_metavariables_pred_expression p e1 && no_metavariables_pred_expression p e2
  | PiImplicit (_, e1, e2) ->
      no_metavariables_pred_expression p e1 && no_metavariables_pred_expression p e2
  | Sigma (_, e1, e2) ->
      no_metavariables_pred_expression p e1 && no_metavariables_pred_expression p e2
  | Function l -> List.for_all (fun (_, e) -> no_metavariables_pred_expression p e) l
  | LocalDeclaration (d, e) -> List.for_all (no_metavariables_pred_decl p) d && no_metavariables_pred_expression p e
  | Application (e1, e2) -> no_metavariables_pred_expression p e1 && no_metavariables_pred_expression p e2
  | ApplicationImplicit (e1, e2) -> no_metavariables_pred_expression p e1 && no_metavariables_pred_expression p e2
  | Universe _ | UnitType | Unit | Index _ | Constructor _ -> true
  | Proj1 e -> no_metavariables_pred_expression p e
  | Proj2 e -> no_metavariables_pred_expression p e
  | Meta id -> not (p id)
and no_metavariables_pred_decl p = function
  | Let (x, e1, e2) -> no_metavariables_pred_expression p e1 && no_metavariables_pred_expression p e2
  | LetRec (x, e1, e2) -> no_metavariables_pred_expression p e1 && no_metavariables_pred_expression p e2
  | Type (x, ps, e, cs) -> List.for_all (no_metavariables_pred_param p) ps && no_metavariables_pred_expression p e && List.for_all (fun (_, e) -> no_metavariables_pred_expression p e) cs
and no_metavariables_pred_param p = function
  | Parameter (_, e) -> no_metavariables_pred_expression p e
  | ParameterImplicit (_, e) -> no_metavariables_pred_expression p e

let rec no_metavariables_pred_value p = function
  | VPair (v1, v2) -> no_metavariables_pred_value p v1 && no_metavariables_pred_value p v2
  | VLambda (_, e, env) -> no_metavariables_pred_expression p e && no_metavariables_pred_env p env
  | VLambdaImplicit (_, e, env) -> no_metavariables_pred_expression p e && no_metavariables_pred_env p env
  | VPi (_, v, e, env) -> no_metavariables_pred_value p v && no_metavariables_pred_expression p e && no_metavariables_pred_env p env
  | VPiImplicit (_, v, e, env) -> no_metavariables_pred_value p v && no_metavariables_pred_expression p e && no_metavariables_pred_env p env
  | VArrow (v1, v2) -> no_metavariables_pred_value p v1 && no_metavariables_pred_value p v2
  | VSigma (_, v, e, env) -> no_metavariables_pred_value p v && no_metavariables_pred_expression p e && no_metavariables_pred_env p env
  | VTimes (v1, v2) -> no_metavariables_pred_value p v1 && no_metavariables_pred_value p v2
  | VFunction (l, env) -> List.for_all (fun (_, e) -> no_metavariables_pred_expression p e) l && no_metavariables_pred_env p env
  | VUniverse _ | VUnit | VUnitType -> true
  | VConstruct (x, l) -> List.for_all (fun (_, v) -> no_metavariables_pred_value p v) l
  | VNeutral n -> no_metavariables_pred_neutral p n
and no_metavariables_pred_neutral p = function
  | VVar (x, i) -> true
  | VFunctionApplication (l, env, v) ->
      List.for_all (fun (_, e) -> no_metavariables_pred_expression p e) l && no_metavariables_pred_env p env && no_metavariables_pred_value p v
  | VFunctionApplicationImplicit (l, env, v) ->
      List.for_all (fun (_, e) -> no_metavariables_pred_expression p e) l && no_metavariables_pred_env p env && no_metavariables_pred_value p v
  | VApplication (x, y) -> no_metavariables_pred_neutral p x && no_metavariables_pred_value p y
  | VApplicationImplicit (x, y) -> no_metavariables_pred_neutral p x && no_metavariables_pred_value p y
  | VProj1 n -> no_metavariables_pred_neutral p n
  | VProj2 n -> no_metavariables_pred_neutral p n
  | VMeta id -> not (p id)
and no_metavariables_pred_env p env = List.for_all (fun x -> x) (Environment.map_to_list (no_metavariables_pred_value p) (List.for_all (no_metavariables_pred_decl p)) env)
let rec no_metavariables_pred_neutral p = function
  | NVar _ -> true
  | NFunctionApplication (_, _, n) -> no_metavariables_pred p n
  | NFunctionApplicationImplicit (_, _, n) -> no_metavariables_pred p n
  | NApplication (x, y) -> no_metavariables_pred_neutral p x && no_metavariables_pred p y
  | NApplicationImplicit (x, y) -> no_metavariables_pred_neutral p x && no_metavariables_pred p y
  | NProj1 x -> no_metavariables_pred_neutral p x
  | NProj2 x -> no_metavariables_pred_neutral p x
  | NMeta id -> not (p id)
and no_metavariables_pred p = function
  | NPair (x, y) -> no_metavariables_pred p x && no_metavariables_pred p y
  | NLambda (_, _, n) -> no_metavariables_pred p n
  | NLambdaImplicit (_, _, n) -> no_metavariables_pred p n
  | NPi (_, _, x, y) -> no_metavariables_pred p x && no_metavariables_pred p y
  | NPiImplicit (_, _, x, y) -> no_metavariables_pred p x && no_metavariables_pred p y
  | NSigma (_, _, x, y) -> no_metavariables_pred p x && no_metavariables_pred p y
  | NFunction _ -> true
  | NUniverse _ | NUnitType | NUnit -> true
  | NConstruct (_, l) -> List.for_all (fun (_, v) -> no_metavariables_pred p v) l
  | NNeutral n -> no_metavariables_pred_neutral p n

let no_metavariables = no_metavariables_pred (fun _ -> true)
let no_metavariables_neutral = no_metavariables_pred_neutral (fun _ -> true)

let rec eq_structure n e = match n, e with
  | NPair (n1, n2), VPair (e1, e2) -> eq_structure n1 e2 && eq_structure n2 e2
  | NUniverse i, VUniverse j -> i = j
  | NUnit, VUnit | NUnitType, VUnitType -> true
  | NConstruct (c, tl), VConstruct (d, tl2) -> c = d
      && List.length tl = List.length tl2 && List.for_all2 (fun (b1, v1) (b2, v2) -> b1 = b2 && eq_structure v1 v2) tl tl2
  | NNeutral n, VNeutral e -> eq_structure_neutral n e
  | _ -> false
and eq_structure_neutral n e = match n, e with
  | NVar (_, i), VVar (_, j) -> i = j
  | NApplication (n1, n2), VApplication (v1, v2) -> eq_structure (NNeutral n1) v2 && eq_structure n2 v2
  | NApplicationImplicit (n1, n2), VApplicationImplicit (v1, v2) -> eq_structure (NNeutral n1) v2 && eq_structure n2 v2
  | NProj1 n, VProj1 v -> eq_structure_neutral n v
  | NProj2 n, VProj2 v -> eq_structure_neutral n v
  | NMeta n, VMeta v -> n = v
  | _ -> false

let try_find env exp = Environment.find (fun n -> eq_structure exp n) env 

let rec expression_of_normal2 env (exp : normal) =
  let add i = Environment.add env (VNeutral (VVar ("", i))) in
  match try_find env exp with
  | Some i -> Index i
  | None ->
  match exp with
  | NPair (x, y) ->
      Pair (expression_of_normal2 env x, expression_of_normal2 env y)
  | NLambda (s, i, x) -> Lambda (Name s, expression_of_normal2 (add i) x)
  | NLambdaImplicit (s, i, x) -> LambdaImplicit (Name s, expression_of_normal2 (add i) x)
  | NPi (s, i, x, y) ->
      Pi (Name s, expression_of_normal2 env x, expression_of_normal2 (add i) y)
  | NPiImplicit (s, i, x, y) ->
      PiImplicit (s, expression_of_normal2 env x, expression_of_normal2 (add i) y)
  | NSigma (s, i, x, y) ->
      Sigma (Name s, expression_of_normal2 env x
        , expression_of_normal2 (add i) y)
  | NFunction _ -> raise Constraint_function
  | NUniverse i -> Universe i
  | NUnitType -> UnitType 
  | NUnit -> Unit
  | NConstruct (c, l) ->
      List.fold_right (fun (b, n) c -> if b then ApplicationImplicit (c, expression_of_normal2 env n) else Application (c, expression_of_normal2 env n))
        l (Constructor c)
  | NNeutral n -> expression_of_normal_neutral2 env n
and expression_of_normal_neutral2 env = function
  | NVar (s, i) -> (
      match Environment.find (function VNeutral (VVar (_, j)) -> i = j | _ -> false) env with
      | Some i -> Index i
      | None -> raise (Failure "expression_of_normal_neutral2"))
  | NFunctionApplication _ -> raise Constraint_function
  | NFunctionApplicationImplicit _ -> raise Constraint_function
  | NApplication (x, y) ->
      Application (expression_of_normal_neutral2 env x, expression_of_normal2 env y)
  | NApplicationImplicit (x, y) ->
      ApplicationImplicit (expression_of_normal_neutral2 env x, expression_of_normal2 env y)
  | NProj1 x -> Proj1 (expression_of_normal_neutral2 env x)
  | NProj2 x -> Proj2 (expression_of_normal_neutral2 env x)
  | NMeta id -> Meta id

let rec value_of_normal env = function
  | NPair (x, y) -> VPair (value_of_normal env x, value_of_normal env y)
  | NLambda (s, i, x) ->
      let env' = Environment.add env (VNeutral (VVar (s, i))) in
      VLambda (Name s, expression_of_normal2 env' x, env)
  | NLambdaImplicit (s, i, x) ->
      let env' = Environment.add env (VNeutral (VVar (s, i))) in
      VLambdaImplicit (Name s, expression_of_normal2 env' x, env)
  | NPi ("_", i, x, y) ->
      VArrow (value_of_normal env x, value_of_normal env y)
  | NPi (s, i, x, y) ->
      let env' = Environment.add env (VNeutral (VVar (s, i))) in
      VPi (s, value_of_normal env x, expression_of_normal2 env' y
        , env)
  | NPiImplicit (s, i, x, y) ->
      let env' = Environment.add env (VNeutral (VVar (s, i))) in
      VPiImplicit (s, value_of_normal env x, expression_of_normal2 env' y
        , env)
  | NSigma ("_", i, x, y) ->
      VTimes (value_of_normal env x, value_of_normal env y)
  | NSigma (s, i, x, y) ->
      let env' = Environment.add env (VNeutral (VVar (s, i))) in
      VSigma (s, value_of_normal env x, expression_of_normal2 env' y
        , env)
  | NFunction _ -> raise Constraint_function
  | NUniverse i -> VUniverse i
  | NUnitType -> VUnitType
  | NUnit -> VUnit
  | NConstruct (c, l) -> VConstruct (c, List.map (fun (b, v) -> (b, value_of_normal env v)) l)
  | NNeutral n -> VNeutral (value_of_normal_neutral env n)
and value_of_normal_neutral env = function
  | NVar (s, i) -> VVar (s, i)
  | NFunctionApplication _ -> raise Constraint_function
  | NFunctionApplicationImplicit _ -> raise Constraint_function
  | NApplication (x, y) ->
      VApplication (value_of_normal_neutral env x, value_of_normal env y)
  | NApplicationImplicit (x, y) ->
      VApplicationImplicit (value_of_normal_neutral env x, value_of_normal env y)
  | NProj1 n -> VProj1 (value_of_normal_neutral env n)
  | NProj2 n -> VProj1 (value_of_normal_neutral env n)
  | NMeta i -> VMeta i

type state = Active | Failed

type constraints =
  (* typing contexts *)
  ((int * Context.t * value Environment.t) list) MM.t
  (* types of metavariables *)
  * value MM.t
  (* assignments of metavariables to normals *)
  * normal MM.t
  (* equations *)
  * (state * normal * normal) list
let checker = ref (fun _ _ _ _ -> assert false)
let split = ref (fun _ _ _ _ _ -> assert false)
let no_constraints = ( MM.empty, MM.empty, MM.empty, [])
let always_satisfied (_, _, _, c) = c = []
let never_satisfied (_, _, _, c) = List.exists (fun (s, _, _) -> s = Failed) c
let has_metavariable (_, m, _, _) id = MM.mem id m
let get_metavariable (_, m, _, _) id = MM.find id m
let first_env (c, _, _, _) id =
  let l = if MM.mem id c then MM.find id c else [] in
  match l with
  | [_, _, env] -> env
  | _ -> Environment.empty
let get_metavariable_assignment_no_env ((c, _, a, _) as con) id =
  if MM.mem id a
  then Some (expression_of_normal2 (first_env con id) (MM.find id a))
  else None
let get_metavariable_assignment ((c, _, a, _) as con) env id =
  if MM.mem id a
  then try Some (expression_of_normal2 env (MM.find id a))
    with _ -> get_metavariable_assignment_no_env con id
  else None
let add_typing_context ((con, m, a, c):constraints) (id:meta_id) context =
  if MM.mem id con then ((MM.add id (context::(MM.find id con)) con, m, a, c) :
    constraints)
  else ( MM.add id [] con, m, a, c)

let get_metavariable_assignment_value ((c, _, a, _) as con) id =
  if MM.mem id a
  then
    let env = first_env con id in
    Some (eval (get_metavariable_assignment con) env (expression_of_normal2 env (MM.find id a)))
  else None

let add_typing_context ((con, m, a, c):constraints) (id:meta_id) context =
  if MM.mem id con then ((MM.add id (context::(MM.find id con)) con, m, a, c) :
    constraints)
  else ( MM.add id [] con, m, a, c)

let remove_implicit_metavariables ( cont, types, assigments, equations) =
  let cont = MM.filter (fun id _ -> not (is_implicit id)) cont in
  let types = MM.filter (fun id _ -> not (is_implicit id)) types in
  let assigments = MM.filter (fun id _ -> not (is_implicit id)) assigments in
  let equations = List.filter (fun (s, x, y) -> no_metavariables_pred is_implicit x && no_metavariables_pred is_implicit y) equations in
  (cont, types, assigments, equations)

let rec readback constraints i =
  let readback = readback constraints in
  let eval = eval (get_metavariable_assignment constraints) in
  let readback_env i =
    Environment.map_to_list (fun v -> (`N (readback i v))) (fun d -> `D d) in
  let rec readback_neutral i = function
  | VVar (name, i) -> NVar (name, i)
  | VFunctionApplication (cases, env, v) ->
      NFunctionApplication (cases, readback_env i env, readback i v)
  | VFunctionApplicationImplicit (cases, env, v) ->
      NFunctionApplicationImplicit (cases, readback_env i env, readback i v)
  | VApplication (v1, v2) ->
      NApplication (readback_neutral i v1, readback i v2)
  | VApplicationImplicit (v1, v2) ->
      NApplicationImplicit (readback_neutral i v1, readback i v2)
  | VProj1 v -> NProj1 (readback_neutral i v)
  | VProj2 v -> NProj2 (readback_neutral i v) 
  | VMeta i -> NMeta i in 

  function
  | VPair (v1, v2) -> NPair (readback i v1, readback i v2)
  | VLambda (Underscore, e, env) -> NLambda ("_", i, readback (i + 1) (eval env e))
  | VLambda (Name x, e, env) -> 
      NLambda (x, i, readback (i + 1)
        (eval (Environment.add env (VNeutral (VVar (x, i)))) e))
  | VLambdaImplicit (Underscore, e, env) -> NLambdaImplicit ("_", i, readback (i + 1) (eval env e))
  | VLambdaImplicit (Name x, e, env) -> 
      NLambdaImplicit (x, i, readback (i + 1)
        (eval (Environment.add env (VNeutral (VVar (x, i)))) e))
  | VArrow (a, b) ->
      NPi ("_", i, readback i a, readback (i + 1) b)
  | VPi (x, v, e, env) -> 
      NPi (x, i, readback i v, readback (i + 1)
        (eval (Environment.add env (VNeutral (VVar (x, i)))) e))
  | VPiImplicit (x, v, e, env) -> 
      NPiImplicit (x, i, readback i v, readback (i + 1)
        (eval (Environment.add env (VNeutral (VVar (x, i)))) e))
  | VTimes (a, b) ->
      NSigma ("_", i, readback i a, readback (i + 1) b)
  | VSigma (x, v, e, env) ->
      NSigma (x, i, readback i v, readback (i + 1)
        (eval (Environment.add env (VNeutral (VVar (x, i)))) e))
  | VFunction (l, env) -> NFunction (l, readback_env i env)
  | VUniverse i -> NUniverse i
  | VUnitType -> NUnitType
  | VUnit -> NUnit
  | VConstruct (c, vs) -> NConstruct (c, List.map (fun (b, v) -> (b, readback i v)) vs)
  | VNeutral n -> NNeutral (readback_neutral i n)

(* these functions do some evaluation, so that the results are returned in
 * normal form *)
let rec subst_var id n = function
  | NPair (x, y) -> NPair (subst_var id n x, subst_var id n y)
  | NLambda (s, i, x) -> NLambda (s, i, subst_var id n x)
  | NLambdaImplicit (s, i, x) -> NLambdaImplicit (s, i, subst_var id n x)
  | NPi (s, i, x, y) -> NPi (s, i, subst_var id n x, subst_var id n y)
  | NPiImplicit (s, i, x, y) -> NPiImplicit (s, i, subst_var id n x, subst_var id n y)
  | NSigma (s, i, x, y) -> NSigma (s, i, subst_var id n x, subst_var id n y)
  | NFunction _ -> raise Constraint_function
  | NUniverse _ | NUnitType | NUnit as n -> n
  | NConstruct (c, l) -> NConstruct (c, List.map (fun (b, v) -> (b, subst_var id n v)) l)
  | NNeutral x -> subst_var_neutral id n x
and subst_var_neutral id n = function
  | NVar (_, id2) when id = id2 -> n
  | NVar _ as x -> NNeutral x
  | NFunctionApplication _ -> raise Constraint_function
  | NFunctionApplicationImplicit _ -> raise Constraint_function
  | NApplication (x, y) -> (
      let x = subst_var_neutral id n x in
      let y = subst_var id n y in
      match x with
      | NConstruct (c, l) -> NConstruct (c, (false , y)::l)
      | NLambda (b, i, x) -> subst_var i y x
      | NNeutral x -> NNeutral (NApplication (x, y))
      | _ ->
          (* should only happen if the normals do not type check *)
          assert false)
  | NApplicationImplicit (x, y) -> (
      let x = subst_var_neutral id n x in
      let y = subst_var id n y in
      match x with
      | NConstruct (c, l) -> NConstruct (c, (true, y)::l)
      | NLambda (b, i, x) -> subst_var i y x
      | NNeutral x -> NNeutral (NApplicationImplicit (x, y))
      | _ ->
          (* should only happen if the normals do not type check *)
          assert false)
  | NProj1 x -> (
      match subst_var_neutral id n x with
      | NPair (x, y) -> x
      | NNeutral x -> NNeutral (NProj1 x)
      | _ ->
          (* should only happen if the normals do not type check *)
          assert false)
  | NProj2 x -> (
      match subst_var_neutral id n x with
      | NPair (x, y) -> y
      | NNeutral x -> NNeutral (NProj2 x)
      | _ ->
          (* should only happen if the normals do not type check *)
          assert false)
  | NMeta _ as x -> NNeutral x

(* this function does some evaluation, so that the results are returned in
 * normal form *)
let rec subst id n = function
  | NPair (x, y) -> NPair (subst id n x, subst id n y)
  | NLambda (s, i, x) -> NLambda (s, i, subst id n x)
  | NLambdaImplicit (s, i, x) -> NLambdaImplicit (s, i, subst id n x)
  | NPi (s, i, x, y) -> NPi (s, i, subst id n x, subst id n y)
  | NPiImplicit (s, i, x, y) -> NPiImplicit (s, i, subst id n x, subst id n y)
  | NSigma (s, i, x, y) -> NSigma (s, i, subst id n x, subst id n y)
  | NFunction _ -> raise Constraint_function
  | NUniverse _ | NUnitType | NUnit as n -> n
  | NConstruct (c, l) -> NConstruct (c, List.map (fun (b, e) -> (b, subst id n e)) l)
  | NNeutral x -> subst_neutral id n x
and subst_neutral id n = function
  | NVar _ as x -> NNeutral x
  | NFunctionApplication _ as x -> if no_metavariables_neutral x then NNeutral x else raise Constraint_function
  | NFunctionApplicationImplicit _ as x -> if no_metavariables_neutral x then NNeutral x else raise Constraint_function
  | NApplication (x, y) -> (
      let x = subst_neutral id n x in
      let y = subst id n y in
      match x with
      | NConstruct (c, l) -> NConstruct (c, (false, y)::l)
      | NLambda (b, i, x) -> subst_var i y x
      | NNeutral x -> NNeutral (NApplication (x, y))
      | _ ->
          (* should only happen if the normals do not type check *)
          (* in particular, the case NLambdaImplicit should not occur *)
          assert false)
  | NApplicationImplicit (x, y) -> (
      let x = subst_neutral id n x in
      let y = subst id n y in
      match x with
      | NConstruct (c, l) -> NConstruct (c, (true, y)::l)
      | NLambdaImplicit (b, i, x) -> subst_var i y x
      | NNeutral x -> NNeutral (NApplicationImplicit (x, y))
      | _ ->
          (* should only happen if the normals do not type check *)
          (* in particular, the case NLambdaImplicit should not occur *)
          assert false)
  | NProj1 x -> (
      match subst_neutral id n x with
      | NPair (x, y) -> x
      | NNeutral x -> NNeutral (NProj1 x)
      | _ ->
          (* should only happen if the normals do not type check *)
          assert false)
  | NProj2 x -> (
      match subst_neutral id n x with
      | NPair (x, y) -> y
      | NNeutral x -> NNeutral (NProj2 x)
      | _ ->
          (* should only happen if the normals do not type check *)
          assert false)
  | NMeta id2 when id = id2 -> n
  | NMeta _ as x -> NNeutral x

let subst_equation id n (s, x, y) = (s, subst id n x, subst id n y)

let apply_subst_equation a eq =
  MM.fold (fun id n eq -> subst_equation id n eq) a eq 

let add hd tl = if List.mem hd tl then tl else hd::tl
let add_equation s x y ( con, m, a, c) =
  let eq =
    try apply_subst_equation a (s, x, y)
    with Constraint_function -> (Failed, x, y) in
  ( con, m, a, add eq c)


let rec head_is_metavariable = function
  | NNeutral (NMeta _) -> true
  | NNeutral (NApplication (x, y)) -> head_is_metavariable (NNeutral x)
  | _ -> false

let (++) c1 c2 =
  List.fold_right (fun c tl -> match c with
  | (_, x, y) when x = y -> tl
  | (Active, x, y) when no_metavariables x && no_metavariables y ->
      (* x cannot be the same as y *)
      add (Failed, x, y) tl
  | _ -> add c tl) c1 c2

let rec test_eq_no_metavariables x y = match x, y with
  | NPair (x1, x2), NPair (y1, y2) ->
      test_eq_no_metavariables x1 y1 && test_eq_no_metavariables x2 y2
  | NLambda (_, i, x), NLambda (_, j, y) ->
      i = j && test_eq_no_metavariables x y
  | NPi (_, i, x1, x2), NPi (_, j, y1, y2) ->
      i = j && test_eq_no_metavariables x1 y1 && test_eq_no_metavariables x2 y2
  | NSigma (_, i, x1, x2), NSigma (_, j, y1, y2) ->
      i = j && test_eq_no_metavariables x1 y1 && test_eq_no_metavariables x2 y2
  | NFunction _, NFunction _ -> x = y
  | NUniverse i, NUniverse j -> i = j
  | NUnitType, NUnitType -> true
  | NUnit, NUnit -> true
  | NConstruct (xc, xl), NConstruct (yc, yl) ->
      let rec aux ls = match ls with
        | [], [] -> true 
        | (bx, x)::xs, (by, y)::ys -> bx = by && test_eq_no_metavariables x y && aux (xs, ys)
        | _ -> false in
      xc = yc && aux (xl, yl)
  | NNeutral x, NNeutral y -> test_eq_no_metavariables_neutral x y
  | _ -> false
and test_eq_no_metavariables_neutral x y = match x, y with
  | NVar (_, i), NVar (_, j) -> i = j
  | NFunctionApplication (xl, xe, xn), NFunctionApplication (yl, ye, yn) ->
      xl = yl && xe = ye && test_eq_no_metavariables xn yn
  | NApplication (x1, x2), NApplication (y1, y2) -> 
      test_eq_no_metavariables_neutral x1 y1 && test_eq_no_metavariables x2 y2
  | NProj1 x, NProj1 y -> test_eq_no_metavariables_neutral x y
  | NProj2 x, NProj2 y -> test_eq_no_metavariables_neutral x y
  | _ -> false

(* perform local simplification on a single equation *)
let simplify x y =
  let apply x i = function
    | NNeutral n -> NNeutral (NApplication (n, NNeutral (NVar (x, i))))
    (* TODO: check order of applications *)
    | NConstruct (c, l) -> NConstruct (c, ((false, NNeutral (NVar (x, i)))::l))
    | _ ->
        (* this case should only happen if x and y have different types *)
        assert false in
  let proj1 = function
    | NNeutral n -> NNeutral (NProj1 n)
    | _ ->
        (* this case should only happen if x and y have different types *)
        assert false in
  let proj2 = function
    | NNeutral n -> NNeutral (NProj2 n)
    | _ ->
        (* this case should only happen if x and y have different types *)
        assert false in

  match x, y with
  (* no metavariables -- can compare both sides  *)
  | x, y when no_metavariables x && no_metavariables y ->
      (true, if test_eq_no_metavariables x y then [] else [Failed, x, y])
  (* decomposition of functions -- remove lambda abstractions *)
  | NLambda (_, i, x), NLambda (_, j, y) ->
      (* readback should have assigned the same indices here *)
      assert (i = j);
      (true, [Active, x, y])
  | NLambda (b, i, x), y -> (true, [Active, x, apply b i y])
  | x, NLambda (b, i, y) -> (true, [Active, apply b i x, y])

  (* decomposition of pairs *)
  | NPair (x1, x2), NPair (y1, y2) -> (true, [Active, x1, y1; Active, x2, y2])
  | NPair (x1, x2), y -> (true, [Active, x1, proj1 y; Active, x2, proj2 y])
  | x, NPair (y1, y2) -> (true, [Active, proj1 x, y1; Active, proj2 x, y2])

  (* decomposition of neutrals *)
  (* TODO *)

  (* decomposition of evaluation contexts *)
  (* TODO *)

  (* orientation *)
  | x, y when head_is_metavariable y && not (head_is_metavariable x) ->
      (true, [Active, y, x])

  | x, y when head_is_metavariable x ->
      let rec aux_neutral = function
        | NVar _ as x -> (false, x, y)
        | NFunctionApplication (l, env, x) ->
            let b, x, y = aux x in
            (b, NFunctionApplication (l, env, x), y)
        | NFunctionApplicationImplicit (l, env, x) ->
            let b, x, y = aux x in
            (b, NFunctionApplicationImplicit (l, env, x), y)
        | NApplication (x1, x2) -> 
            let b, x1, y = aux_neutral x1 in
            if b then (true, NApplication (x1, x2), y)
            else
              let b, x2, y = aux x2 in
              (b, NApplication (x1, x2), y)
        | NApplicationImplicit (x1, x2) -> 
            let b, x1, y = aux_neutral x1 in
            if b then (true, NApplicationImplicit (x1, x2), y)
            else
              let b, x2, y = aux x2 in
              (b, NApplicationImplicit (x1, x2), y)
        | NProj1 x ->
            let b, x, y = aux_neutral x in
            (b, NProj1 x, y)
        | NProj2 x ->
            let b, x, y = aux_neutral x in
            (b, NProj2 x, y)
        | NMeta _ as x -> (false, x, y)
      and aux = function
        (* eta-contraction *)
        | NLambda (_, i, NNeutral (NApplication (x1, NNeutral (NVar (_, j)))))
          when i = j ->
            (true, NNeutral x1, y)
        | NLambdaImplicit (_, i, NNeutral (NApplicationImplicit (x1, NNeutral (NVar (_, j)))))
          when i = j ->
            (true, NNeutral x1, y)
        | NPair (NNeutral (NProj1 x1), NNeutral (NProj2 x2)) when x1 = x2 ->
            (true, NNeutral x1, y)

        (* eliminating projections *)
        (* TODO *)

        | NPair (x1, x2) ->
            let b, x1, y = aux x1 in
            if b then (true, NPair (x1, x2), y)
            else
              let b, x2, y = aux x2 in
              (b, NPair (x1, x2), y)
        | NLambda (name, i, x) ->
            let b, x, y = aux x in
            (b, NLambda (name, i, x), y)
        | NLambdaImplicit (name, i, x) ->
            let b, x, y = aux x in
            (b, NLambdaImplicit (name, i, x), y)
        | NPi (name, i, x1, x2) ->
            let b, x1, y = aux x1 in
            if b then (true, NPi (name, i, x1, x2), y)
            else
              let b, x2, y = aux x2 in
              (b, NPi (name, i, x1, x2), y)
        | NPiImplicit (name, i, x1, x2) ->
            let b, x1, y = aux x1 in
            if b then (true, NPiImplicit (name, i, x1, x2), y)
            else
              let b, x2, y = aux x2 in
              (b, NPiImplicit (name, i, x1, x2), y)
        | NSigma (name, i, x1, x2) ->
            let b, x1, y = aux x1 in
            if b then (true, NSigma (name, i, x1, x2), y)
            else
              let b, x2, y = aux x2 in
              (b, NSigma (name, i, x1, x2), y)
        | NFunction _ as x -> (false, x, y)
        | NUniverse _ | NUnitType | NUnit as x -> (false, x, y)
        | NConstruct (c, l) ->
            let b, l, y = List.fold_left (fun (b, l, y) (is_imp, x) ->
              if b then (true, (is_imp, x)::l, y) else
                let b, x, y = aux x in
                (b, (is_imp, x)::l, y)) (false, [], y) l in
            (b, NConstruct (c, l), y)
        | NNeutral n -> 
            let b, x, y = aux_neutral n in
            (b, NNeutral x, y) in
      let b, x, y = aux x in
      (b, [Active, x, y])

  | x, y -> (false, [Active, x, y])

(* local simplification examines equations in isolation, until it finds one
 * which can be simplified *)
let rec perform_local_simplification (( cont, m, a, c) : constraints) = match c with
  | [] -> (false, ( cont, m, a, []))
  | (Active, x, y)::tl -> (
      match simplify x y with
      | false, _ ->
          let b, ( cont, m, a, tl) = perform_local_simplification ( cont, m, a, tl) in
          (b, ( cont, m, a, (Active, x, y)::tl))
      | true, con ->
          (true, ( cont, m, a, con ++ tl)))
  | (Failed, x, y)::tl ->
      (* do not attempt to simplify equations which cannot be satisfied *)
      let b, ( con, m, a, tl) = perform_local_simplification ( cont, m, a, tl) in
      (b, ( con, m, a, (Failed, x, y)::tl))

let flatten = 
  let rec aux l = function
    | NNeutral (NApplication (n1, n2)) -> aux (n2 :: l) (NNeutral n1)
    | n -> (n, l) in
  aux []

let get_metavariable_application n = 
  let n, tl = flatten n in
  match n with
  | NNeutral (NMeta id) -> Some (id, tl)
  | _ -> None

let get_free_rigid_variables =
  let rec aux ignore l = function
    | NPair (n1, n2) -> aux ignore (aux ignore l n1) n2
    | NLambda (_, i, n) -> aux (i::ignore) l n 
    | NLambdaImplicit (_, i, n) -> aux (i::ignore) l n 
    | NPi (_, i, x, y) -> aux (i::ignore) (aux ignore l x) y
    | NPiImplicit (_, i, x, y) -> aux (i::ignore) (aux ignore l x) y
    | NSigma (_, i, x, y) -> aux (i::ignore) (aux ignore l x) y
    | NFunction _ -> raise Constraint_function
    | NUniverse _ | NUnit | NUnitType -> l
    | NConstruct (_, tl) -> List.fold_left (fun l (_, v) -> aux ignore l v) l tl
    | NNeutral n -> aux_neutral ignore l n
  and aux_neutral ignore l = function
    | NVar (_, i) -> if List.mem i ignore then l else i::l
    | NFunctionApplication _ -> raise Constraint_function
    | NFunctionApplicationImplicit _ -> raise Constraint_function
    | NApplication _ as n -> (
        let n, tl = flatten (NNeutral n) in
        match n with
        | NNeutral (NMeta _) -> 
            (* variables are flexible if they are applied to a metavariable *)
            l 
        | _ -> List.fold_left (aux ignore) [] tl)
    | NApplicationImplicit _ as n -> (
        let n, tl = flatten (NNeutral n) in
        match n with
        | NNeutral (NMeta _) -> 
            (* variables are flexible if they are applied to a metavariable *)
            l 
        | _ -> List.fold_left (aux ignore) [] tl)
    | NProj1 n -> aux_neutral ignore l n
    | NProj2 n -> aux_neutral ignore l n
    | NMeta n -> l in
  aux [] []

(* checks for strong rigid occurences of ?id *)
let rec occurs_check id = function
  | NPair (x, y) -> occurs_check id x || occurs_check id y
  | NLambda (_, _, x) -> occurs_check id x
  | NLambdaImplicit (_, _, x) -> occurs_check id x
  | NPi (_, _, x, y) -> occurs_check id x || occurs_check id y
  | NPiImplicit (_, _, x, y) -> occurs_check id x || occurs_check id y
  | NSigma (_, _, x, y) -> occurs_check id x || occurs_check id y
  | NFunction _ -> raise Constraint_function
  | NUniverse _ | NUnitType | NUnit -> false
  | NConstruct (_, l) -> List.exists (fun (_, v) -> occurs_check id v) l
  | NNeutral n -> occurs_check_neutral id n
and occurs_check_neutral id = function
  | NVar _ -> false
  | NFunctionApplication _ -> raise Constraint_function
  | NFunctionApplicationImplicit _ -> raise Constraint_function
  | NApplication (x, y) ->
     (* rigid occurrences in y are not strong *)
     occurs_check_neutral id x 
  | NApplicationImplicit (x, y) ->
     (* rigid occurrences in y are not strong *)
     occurs_check_neutral id x 
  | NProj1 n -> occurs_check_neutral id n 
  | NProj2 n -> occurs_check_neutral id n
  | NMeta id2 -> id = id2

let check_assign ((con, m, a, c) : constraints) id n =
  if MM.mem id m then
    let cons = if MM.mem id con then MM.find id con else [] in
    let typ = MM.find id m in
    List.fold_left (fun prev (i, context, env) -> match prev with
      | None -> None
      | Some constraints ->
          try
            let exp = expression_of_normal2 env n in
            !checker (i, context, env) constraints exp typ
          with Failure _ -> Some (con, m, a, c)) (Some (con, m, a, c)) cons
  else Some ((con, m, a, c): constraints)

let assign ( con, m, a, c) id n = 
  match check_assign (con, m, a, c) id n with
  | None ->
      (* n does not have the correct type *)
      ((con, m, a, (Failed, NNeutral (NMeta id), n)::c) : constraints)
  | Some (con, m, a, c) ->
    let a = MM.map (fun x -> subst id n x) a in
    let c = List.map (subst_equation id n) c in
    (con, m, MM.add id n a, c)

let maybe_add ((con, m, a, c) : constraints) e =
  if List.mem e c then false, (con, m, a, c)
  else true, (con, m, a, (e::c))

let case_split (id:meta_id) (typ:value) ((b:bool), constraints) (i, context, env) =
  if b then b, constraints else
  if typ = VUnitType then
    maybe_add constraints (Active, NNeutral (NMeta id), NUnit)
  else try
    match !split (i + 1) constraints context typ (VNeutral (VVar ("", i))) i with
    | [j, v, _] when j < i  -> (*
        let rec s j = if j >= i then
          let id = if Abstract.is_implicit id
            then Abstract.create_implicit_metavariable ()
            else Abstract.create_metavariable () in
          substitute_neutral_variable j (VNeutral (VMeta id)) (s (j - 1))
        else v in*)
        maybe_add constraints (Active, NNeutral (NMeta id), readback constraints i v)
    | [] when no_neutral_value typ ->
        maybe_add constraints (Failed, NNeutral (NMeta id), NNeutral (NVar ("anything", 0)))
    | _ -> false, constraints
  with _ -> false, constraints

let try_case_split (con, m, a, c) =
  MM.fold (fun id typ (b, (con, m, a, c)) ->
    if b then true, (con, m, a, c)
    else
      (* only attempt a case split if a context is available and the
       * metavariable has not been solved *)
      if MM.mem id con && not (MM.mem id a) then
        List.fold_left (case_split id typ) (false, (con, m, a, c)) (MM.find id con)
      else false, (con, m, a, c)) m (false, (con, m, a, c))

let rec no_duplicates = function
  | [] -> true
  | hd::tl -> (not (List.mem hd tl)) && no_duplicates tl

let rec solve_metavariable ( con, m, a, c) =
  let solve ( con, m, a, c) x y = match get_metavariable_application x with
    | None -> None
    | Some (id, l) ->
        (* the equation can only be solved at this point if all of the
         * arguments of the metavariable are variables *)
        if List.for_all (function | NNeutral (NVar _) -> true | _ -> false) l
        then
          let rho =
            List.map (function | NNeutral (NVar (_, i)) -> i | _ -> assert false) l in
          if no_duplicates rho then
            let rig = get_free_rigid_variables y in
            (* if there is a universally quantified rigid variable in y which does
             * not appear as an argument to the metavariable, then the equation 
             * has no solution *)
            (* TODO: Fix this check *)
            if (*List.for_all (fun i -> List.mem i rho) rig*) true then
              (* if there is a strong rigid occurence of the metavariable on the
               * right hand side, then the equation has no (finite) solutions *)
              if occurs_check id y then
                Some ( con, m, a, [Failed, x, y] ++ c)
              else
                let rec add_lambdas = function
                  | [] -> y
                  | (NNeutral (NVar (s, i)))::tl ->
                      NLambda (s, i, add_lambdas tl)
                  | _ -> assert false in
                Some (assign ( con, m, a, c) id (add_lambdas l))
            else Some ( con, m, a, [Failed, x, y] ++ c)
          else None
        else None in

  match c with
  | [] -> (false, ( con, m, a, []))
  | (Active, x, y)::tl -> (
    match solve ( con, m, a, tl) x y with
    | None ->
        let b, ( con, m, a, tl) = solve_metavariable ( con, m, a, tl) in
        (b, ( con, m, a, (Active, x, y)::tl))
    | Some ( con, m, a, c) -> (true, ( con, m, a, c))
    | exception Constraint_function ->
        let b, ( con, m, a, tl) = solve_metavariable ( con, m, a, tl) in
        (b, ( con, m, a, (Active, x, y)::tl)))

  | (Failed, x, y)::tl ->
      (* do not attempt to simplify equations which cannot be satisfied *)
      let b, ( con, m, a, tl) = solve_metavariable ( con, m, a, tl) in
      (b, (con, m, a, (Failed, x, y)::tl))

(* refine the constraints by one step *)
let refine constraints = 
  if never_satisfied constraints then
    (* if the constraints are known to be always or never satisfied, then they
     * are considered to be solved, so no refinement is performed *)
    (false, constraints)
  else
    let b, constraints = perform_local_simplification constraints in
    if b then (true, constraints) else
    let b, constraints = solve_metavariable constraints in
    if b then (true, constraints) else
    let b, constraints = try_case_split constraints in
    if b then (true, constraints) else
    (false, constraints)

let add_equation s x y constraints =
  let rec aux c = 
    let b, c = refine c in
    if b then aux c else c in
  aux (add_equation s x y constraints)

let add_metavariable (con, m, a, c) context id typ =
  let _, c = refine ( MM.add id [context] con, MM.add id typ m, a, c) in
  c

let (>>=) c f = f c

let empty_envt = []

let rec test_normal_equality c x y =
  let test x y c = test_normal_equality c x y in
  let test_neutral x y c = test_neutral_equality c x y in

  match x, y with
  | NPair (x1, x2), NPair (y1, y2) ->
      c >>= test x1 y1 >>= test x2 y2
  | NLambda (_, i, x), NLambda (_, j, y) when i = j -> c >>= test x y
  | NPi (_, i, x1, x2), NPi (_, j, y1, y2) when i = j ->
      c >>= test x1 y1 >>= test x2 y2
  | NPiImplicit (_, i, x1, x2), NPiImplicit (_, j, y1, y2) when i = j ->
      c >>= test x1 y1 >>= test x2 y2
  | NSigma (_, i, x1, x2), NSigma (_, j, y1, y2) when i = j ->
      c >>= test x1 y1 >>= test x2 y2
  | NFunction _, NFunction _ when x = y -> c 
  | NUniverse i, NUniverse j when i = j -> c 
  | NUnitType, NUnitType -> c 
  | NUnit, NUnit -> c
  | NConstruct (xc, xl), NConstruct (yc, yl) when xc = yc ->
      let rec aux ls c = match ls with
        | [], [] -> c 
        | (bx, x)::xs, (by, y)::ys when bx = by -> c >>= test x y >>= aux (xs, ys)
        | _ -> c >>= add_equation Failed x y in
      aux (xl, yl) c 
  | NNeutral x, NNeutral y -> c >>= test_neutral x y
  | _ when not (no_metavariables x && no_metavariables y) ->
      (* if x or y has a metavariable, then they maay be equal if constraints
       * are satisfied *)
      c >>= add_equation Active x y
  | _ -> c >>= add_equation Failed x y
and test_neutral_equality c x y =
  let test x y c = test_neutral_equality c x y in
  let test_normal x y c = test_normal_equality c x y in
  
  match x, y with
  | NVar (_, i), NVar (_, j) when i = j -> c 
  | NFunctionApplication (xc, xe, xn), NFunctionApplication (yc, ye, yn)
      when xc = yc && xe = ye -> c >>= test_normal xn yn
  | NApplication (x1, x2), NApplication (y1, y2) ->
      c >>= test x1 y1 >>= test_normal x2 y2
  | NProj1 x, NProj1 y -> c >>= test x y
  | NProj2 x, NProj2 y -> c >>= test x y
  | _ when not (no_metavariables_neutral x && no_metavariables_neutral y) ->
      (* if x or y has a metavariable, then they may be equal if constraints
       * are satisfied *)
      c >>= add_equation Active (NNeutral x) (NNeutral y)
  | _ -> c >>= add_equation Failed (NNeutral x) (NNeutral y) 

let test_equality i constraints x y =
  test_normal_equality constraints
    (readback constraints i x) (readback constraints i y)
let test_expression_equality env x y =
  test_equality 0 no_constraints (eval (fun _ _ -> None) env x) (eval (fun _ _ -> None) env y)

(* the following functions are numbered according to the precedence of the
 * values which they print *)
let rec pr_neutral fmt = function
  | v -> pr_neutral4 fmt v
and pr_neutral4 fmt = function
  | NApplication (n, v) ->
      fprintf fmt "@[<hov2>%a@ %a@]" pr_neutral4 n pr_normal5 v
  | NApplicationImplicit (n, v) ->
      fprintf fmt "@[<hov2>%a@ {%a}@]" pr_neutral4 n pr_normal v
  | NFunctionApplication (_, _, n) ->
      fprintf fmt "@[<hov2>%s@ %a@]" "<function>" pr_normal5 n
  | NFunctionApplicationImplicit (_, _, n) ->
      fprintf fmt "@[<hov2>%s@ %a@]" "<function>" pr_normal5 n
  | v -> pr_neutral5 fmt v
and pr_neutral5 fmt = function
  | NProj1 v -> fprintf fmt "%a.1" pr_neutral5 v
  | NProj2 v -> fprintf fmt "%a.2" pr_neutral5 v
  | NVar ("", i) -> fprintf fmt "%i" i
  | NVar (x, _) -> fprintf fmt "%s" x
  | NMeta i -> fprintf fmt "?%s" (Abstract.string_of_id i)
  | v -> fprintf fmt "(%a)" pr_neutral v

and pr_normal fmt = function
  | NPair (v1, v2) -> fprintf fmt "@[<hov2>%a,@ %a@]" pr_normal3 v1 pr_normal v2
  | v -> pr_normal1 fmt v
and pr_normal1 fmt = function
  | NLambda ("", i, x) -> fprintf fmt "@[<hov2>fun %i@ -> %a@]" i pr_normal1 x
  | NLambda (b, _, x) -> fprintf fmt "@[<hov2>fun %s@ -> %a@]" b pr_normal1 x
  | NLambdaImplicit ("", i, x) -> fprintf fmt "@[<hov2>fun {%i}@ -> %a@]" i pr_normal1 x
  | NLambdaImplicit (b, _, x) -> fprintf fmt "@[<hov2>fun {%s}@ -> %a@]" b pr_normal1 x
  | NFunction (_, _) -> fprintf fmt "<function>"
  | v -> pr_normal2 fmt v
and pr_normal2 fmt = function
  | NPi ("", i, a, b) -> fprintf fmt "@[<hov2>(%i : %a)@ -> %a@]" i pr_normal3 a pr_normal2 b
  | NPi (name, _, a, b) -> fprintf fmt "@[<hov2>(%s : %a)@ -> %a@]" name pr_normal3 a pr_normal2 b
  | NPiImplicit ("", i, a, b) -> fprintf fmt "@[<hov2>{%i : %a}@ -> %a@]" i pr_normal3 a pr_normal2 b
  | NPiImplicit (name, _, a, b) -> fprintf fmt "@[<hov2>{%s : %a}@ -> %a@]" name pr_normal3 a pr_normal2 b
  | v -> pr_normal3 fmt v
and pr_normal3 fmt = function
  | NSigma ("", i, a, b) -> fprintf fmt "@[<hov2>(%i : %a)@ * %a@]" i pr_normal4 a pr_normal3 b
  | NSigma (name, _, a, b) -> fprintf fmt "@[<hov2>(%s : %a)@ * %a@]" name pr_normal4 a pr_normal3 b
  | v -> pr_normal4 fmt v
and pr_normal4 fmt = function
  | NConstruct (c, (_::_ as l)) ->
      let rec pr_normals fmt = function
        | [] -> assert false
        | [false, v] -> pr_normal5 fmt v
        | [true, v] -> fprintf fmt "@[<hov2>{%a}@]" pr_normal5 v
        | (false, v)::tl ->
            fprintf fmt "@[<hov2>%a@ %a@]" pr_normal5 v pr_normals tl 
        | (true, v)::tl ->
            fprintf fmt "@[<hov2>{%a}@ %a@]" pr_normal5 v pr_normals tl in
      fprintf fmt "@[%s@ %a@]" c pr_normals (List.rev l)
  | v -> pr_normal5 fmt v
and pr_normal5 fmt = function
  | NConstruct (c, []) -> fprintf fmt "%s" c
  | NUniverse 0 -> fprintf fmt "Type"
  | NUniverse i -> fprintf fmt "Type %i" i
  | NUnitType -> fprintf fmt "Unit"
  | NUnit -> fprintf fmt "()"
  | NNeutral n -> fprintf fmt "[%a]" pr_neutral n
  | v -> fprintf fmt "(%a)" pr_normal v

let print_normal v = pr_normal std_formatter v; print_newline ()

let string_of_normal v =
  Buffer.clear stdbuf;
  pr_normal str_formatter v;
  pp_print_flush str_formatter ();
  Buffer.contents stdbuf

let string_of_constraints_for_metavariables mvs (_, m, a, c) =
  let is_in id = List.mem id mvs in
  let print_type id typ s =
    if is_in id || not (no_metavariables_pred_value is_in typ)
    then sprintf "%s?%s : %s\n" s (string_of_id id) (Print_value.string_of_value typ)
    else s in
  let print_assign id n s =
    if is_in id || not (no_metavariables_pred is_in n)
    then sprintf "%s?%s := %s\n" s (string_of_id id) (string_of_normal n)
    else s in
  let print_equation s (state, x, y) =
    if no_metavariables_pred is_in x && no_metavariables_pred is_in y then s
    else
      let state = match state with Active -> "" | Failed -> "Failed: " in
      sprintf "%s%s%s = %s\n" s state (string_of_normal x) (string_of_normal y) in

  let s = MM.fold print_type m "" in
  let s = MM.fold print_assign a s in
  List.fold_left print_equation s c

let print_constraints_for_metavariables fmt mvs constraints =
  Format.fprintf fmt "%s" (string_of_constraints_for_metavariables mvs constraints);
  Format.pp_print_flush fmt ()

let string_of_constraints (_, m, a, c) =
  let s = MM.fold (fun id typ s -> if is_implicit id then s else sprintf "%s?%s : %s\n" s (string_of_id id)
    (Print_value.string_of_value typ)) m "" in
  let s = MM.fold (fun id typ s -> if is_implicit id then s else sprintf "%s?%s := %s\n" s (string_of_id id)
    (string_of_normal typ)) a s in
  List.fold_left (fun s -> function
    | (Active, x, y) -> sprintf "%s%s = %s\n" s (string_of_normal x) (string_of_normal y)
    | (Failed, x, y) -> sprintf "%sFailed: %s = %s\n" s (string_of_normal x) (string_of_normal y))
    s c

let print_constraints fmt constraints =
  Format.fprintf fmt "%s" (string_of_constraints constraints);
  Format.pp_print_flush fmt ()
