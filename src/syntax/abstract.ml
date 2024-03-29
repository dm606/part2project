open AbsConcrete
open Format

module MS = Map.Make(String)
module SS = Set.Make(String)

exception Invalid_expression of string
exception Constructor_not_defined of string

(* is implicit, id *)
type meta_id = bool * int

let string_of_id (b, i) = if b then sprintf "I%i" i else string_of_int i

let meta_id_compare = compare

let metavariable_id = ref 0
let metavariable_implicit_id = ref 0

let create_implicit_metavariable () =
  let id = !metavariable_implicit_id in
  incr metavariable_implicit_id;
  (true, id)

let create_metavariable () =
  let id = !metavariable_id in
  incr metavariable_id;
  (false, id)

let is_implicit (b, _) = b

type envt = string list * SS.t MS.t

let empty_env = ([], MS.empty)

let inc m (ctor, type_name) =
  if MS.mem ctor m then MS.add ctor (SS.add type_name (MS.find ctor m)) m
  else MS.add ctor (SS.singleton type_name) m

let mk_env (names, cs) = names, List.fold_left inc MS.empty cs

(* The type of desugared expressions.
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
 *   closer lets get smaller indices.
 * * In the indices of a type or the type of a constructor, one index is
 *     assigned for each binder in the parameters of the type. The indices
 *     increase from right to left. *)
type expression =
  | Pair of expression * expression
  | Lambda of binder * expression
  | LambdaImplicit of binder * expression
  | Pi of binder * expression * expression
  | PiImplicit of string * expression * expression
  | Sigma of binder * expression * expression
  | Function of (pattern * expression) list
  | LocalDeclaration of declaration list * expression
  | Application of expression * expression
  | ApplicationImplicit of expression * expression
  | Universe of int
  | UnitType
  | Unit
  | Index of int (* de Bruijn index *)
  | Constructor of string
  | Proj1 of expression
  | Proj2 of expression
  (* A metavariable. Each metavariable is assigned a unique ID for use in the
   * constraints generated by the type checker *)
  | Meta of meta_id
and binder =
  | Underscore
  (* Since de Bruijn indices are used, the name used is not necessary; it is
   * only kept for pretty-printing *)
  | Name of string
and pattern =
  | PatternPair of pattern * pattern
  | PatternApplication of string * (bool * pattern) list (* Constructor application *)
  | PatternBinder of string (* name only needed for pretty-printing *)
  | PatternUnderscore
  | PatternInaccessible of expression
and declaration =
  (* Names only used for pretty-printing, except for constructor names *)
  | Let of string * expression * expression
  | LetRec of string * expression * expression
  | Type of string * parameter list * expression * (string * expression) list
and parameter =
  | Parameter of string * expression
  | ParameterImplicit of string * expression

let rec get_metavariables = function
  | Pair (e1, e2) -> (get_metavariables e1) @ (get_metavariables e2)
  | Lambda (_, e) -> get_metavariables e
  | LambdaImplicit (_, e) -> get_metavariables e
  | Pi (_, e1, e2) -> (get_metavariables e1) @ (get_metavariables e2)
  | PiImplicit (_, e1, e2) -> (get_metavariables e1) @ (get_metavariables e2)
  | Sigma (_, e1, e2) -> (get_metavariables e1) @ (get_metavariables e2)
  | Function l -> List.concat (List.map (fun (_, e) -> get_metavariables e) l)
  | LocalDeclaration (l, e) ->
      List.concat (List.map get_metavariables_decl l) @ get_metavariables e
  | Application (e1, e2) -> (get_metavariables e1) @ (get_metavariables e2)
  | ApplicationImplicit (e1, e2) -> (get_metavariables e1) @ (get_metavariables e2)
  | Universe _ | UnitType | Unit | Index _ | Constructor _ -> []
  | Proj1 e -> get_metavariables e
  | Proj2 e -> get_metavariables e
  | Meta id when is_implicit id -> []
  | Meta id -> [id]
and get_metavariables_decl = function
  | Let (_, e1, e2) -> (get_metavariables e1) @ (get_metavariables e2)
  | LetRec (_, e1, e2) -> (get_metavariables e1) @ (get_metavariables e2)
  | Type (_, ps, e, cs) -> 
      (List.concat (List.map get_metavariables_param ps))
      @ (get_metavariables e)
      @ (List.concat (List.map (fun (_, e) -> get_metavariables e) cs))
and get_metavariables_param = function
  | Parameter (_, e) -> get_metavariables e
  | ParameterImplicit (_, e) -> get_metavariables e

let remove_type cs x = MS.map (SS.remove x) cs

let rec does_not_mention c =
  let decl = function
    | Let (_, a, e) -> does_not_mention c a && does_not_mention c e
    | LetRec (_, a, e) -> does_not_mention c a && does_not_mention c e
    | Type (_, ps, e, cs) ->
        let param = function
          | Parameter (_, e) -> does_not_mention c e
          | ParameterImplicit (_, e) -> does_not_mention c e in
        does_not_mention c e
        && List.for_all param ps
        && List.for_all (fun (_, e) -> does_not_mention c e) cs in
    
  function
  | Constructor c1 when c = c1 -> false
  | Pair (e1, e2) -> does_not_mention c e1 && does_not_mention c e2
  | Lambda (_, e) -> does_not_mention c e
  | Pi (_, e1, e2) -> does_not_mention c e1 && does_not_mention c e2
  | Sigma (_, e1, e2) -> does_not_mention c e1 && does_not_mention c e2
  | Function l -> List.for_all (fun (_, e) -> does_not_mention c e) l
  | LocalDeclaration (l, e) -> List.for_all decl l && does_not_mention c e
  | Application (e1, e2) -> does_not_mention c e1 && does_not_mention c e2
  | Proj1 e -> does_not_mention c e
  | Proj2 e -> does_not_mention c e
  | _ -> true

let add_binder (names, cs) = function
  | BUnderscore -> (names, cs)
  | BName (Ident x) -> (x::names, cs)

let add_constructors type_name constructors m = 
  let m = List.fold_left inc m constructors in
  inc m (type_name, "Type")

(* adds all of the bound variables to env in reverse order *)
let rec add_all_declaration_binders (names, cs) =
  let remove_type = remove_type cs in 

  function
  | [] -> (names, cs) 
  | x::xs ->
      let get_name type_name (Constr (Ident x, _)) = x, type_name in
      match x with
      | DLet (Ident x, _, _, _) ->
          add_all_declaration_binders (x::names, cs) xs
      | DLetRec (Ident x, _, _, _) ->
          add_all_declaration_binders (x::names, cs) xs
      | DType (Ident x, _, _, l) ->
          let cs = remove_type x in
          add_all_declaration_binders
            (names, add_constructors x (List.map (get_name x) l) cs)
            xs
      | DSimpleType (Ident x, l) ->
          let cs = remove_type x in
          add_all_declaration_binders
            (names, add_constructors x (List.map (get_name x) l) cs) xs

(* adds all of the bound variables to env in reverse order *)
let rec add_all_let_recs (names, cs) =
  let remove_type = remove_type cs in

  function
  | [] -> (names, cs) 
  | x::xs ->
      let get_name type_name (Constr (Ident x, _)) = x, type_name in
      match x with
      | DLet (Ident x, _, _, _) ->
          add_all_let_recs (names, cs) xs
      | DLetRec (Ident x, _, _, _) ->
          add_all_let_recs (x::names, cs) xs
      | DType (Ident x, _, _, l) ->
          let cs = remove_type x in
          add_all_let_recs
            (names, add_constructors x (List.map (get_name x) l) cs)
            xs
      | DSimpleType (Ident x, l) ->
          let cs = remove_type x in
          add_all_let_recs
            (names, add_constructors x (List.map (get_name x) l) cs)
            xs

(* adds all of the bound variables to env in reverse order *)
let rec add_local_declaration_binders (names, cs) = function
  | [] -> (names, cs) 
  | x::xs ->
      match x with
      | Let (x, _, _) -> add_local_declaration_binders (x::names, cs) xs
      | LetRec (x, _, _) -> add_local_declaration_binders (x::names, cs) xs
      | Type (x, _, _, l) ->
          let cs = remove_type cs x in
          add_local_declaration_binders
            (names, add_constructors x (List.map (fun (c, _) -> c, x) l) cs) xs

(* adds all of the bound variables to env in reverse order *)
let rec add_local_let_recs (names, cs) = function
  | [] -> (names, cs) 
  | x::xs ->
      match x with
      | Let (x, _, _) -> add_local_let_recs (x::names, cs) xs
      | LetRec (x, _, _) -> add_local_let_recs (x::names, cs) xs
      | Type (x, _, _, l) ->
          let cs = remove_type cs x in
          add_local_let_recs
            (names, add_constructors x (List.map (fun (c, _) -> c, x) l) cs) xs

let is_constructor_defined (env, cs) x =
  MS.mem x cs && not (SS.is_empty (MS.find x cs))

let add_pattern_binders (names, cs) p =
  let rec add names = function
    | PPair (p1, p2) -> add (add names p1) p2
    | PApplication (_, l) -> List.fold_left add_applicand names l
    | PIdentifier (Ident x) when is_constructor_defined (names, cs) x -> names
    | PIdentifier (Ident x) -> x::names
    | PInaccessible _ -> names
    | PUnderscore -> names
  and add_applicand names = function
    | PANormal p -> add names p
    | PAImplicit p -> add names p in
  (add names p, cs)

(* Find the de Bruijn index used to refer to x in env *)
let lookup_index (env, cs) x =
  let rec lookup_index_from env x i =
    match env with
    | [] -> None
    | y::l when y = x -> Some i
    | y::l -> lookup_index_from l x (i + 1) in
  lookup_index_from env x 0

(* Get the name associated with a de Bruijn index *)
let get_binder_name (env, cs) = List.nth env

let rec desugar_expression env = function
  | EPair (e1, e2) ->
      Pair (desugar_expression env e1, desugar_expression env e2)
  | ELambda ([], _) ->
      raise
        (Invalid_expression "Lambda abstractions must have at least one binder")
  | ELambda ([LBinder x], e1) ->
      Lambda (desugar_binder x, desugar_expression (add_binder env x) e1)
  | ELambda ([LImplicit x], e1) ->
      LambdaImplicit (desugar_binder x
        , desugar_expression (add_binder env x) e1)
  | ELambda (x::xs, e1) ->
      desugar_expression env (ELambda ([x], ELambda (xs, e1)))
  | EPi (x, e1, e2) ->
      Pi (desugar_binder x, desugar_expression env e1
        , desugar_expression (add_binder env x) e2)
  | EPiImplicit (Ident x, e1, e2) ->
      PiImplicit (x, desugar_expression env e1
                , desugar_expression (add_binder env (BName (Ident x))) e2)
  | ESigma (x, e1, e2) ->
      Sigma (desugar_binder x, desugar_expression env e1
           , desugar_expression (add_binder env x) e2)
  | EFunction xs -> Function (List.map (desugar_case env) xs) 
  | EDeclaration (d, e1) ->
      (* Mutually recursive declarations *)
      let new_env = add_all_declaration_binders env d in
      LocalDeclaration
        (desugar_declarations env d, desugar_expression new_env e1)
  | EApplication (e1, e2) ->
      (* OCaml evaluates tuples from right-to-left. Using declarations forces
       * OCaml to desugar e1 first, so e1 will get smaller metavariable ids *)
      let e1 = desugar_expression env e1 in
      let e2 = desugar_expression env e2 in
      Application (e1, e2)
  | EApplicationImplicit (e1, e2) ->
      (* OCaml evaluates tuples from right-to-left. Using declarations forces
       * OCaml to desugar e1 first, so e1 will get smaller metavariable ids *)
      let e1 = desugar_expression env e1 in
      let e2 = desugar_expression env e2 in
      ApplicationImplicit (e1, e2)
  | EUniverse i when i >= 0 -> Universe i
  | EUniverse i ->
      raise (Invalid_expression "The universe level must be nonnegative.")
  | EUnindexedUniverse -> Universe 0
  | EUnitType -> UnitType
  | EUnit -> Unit
  | EIdentifier (Ident x) -> ( 
      match lookup_index env x with
      | Some i -> Index i (* x is bound to index i *)
      | None when not (is_constructor_defined env x) ->
          raise (Constructor_not_defined x)
      | None -> Constructor x)
  | EProj1 e1 -> Proj1 (desugar_expression env e1)
  | EProj2 e2 -> Proj2 (desugar_expression env e2)
  | EMeta -> let e = Meta (false, !metavariable_id) in incr metavariable_id; e
  | EMetaInternal _ ->
      raise (Invalid_expression "? must not be followed by an integer")
  | EMetaInternalImplicit _ ->
      raise (Invalid_expression "?I must not be followed by an integer")

  | EArrow (e1, e2) ->
      Pi (Underscore, desugar_expression env e1, desugar_expression env e2)
  | ETimes (e1, e2) ->
      Sigma (Underscore, desugar_expression env e1, desugar_expression env e2)
  | EMatch (e1, xs) ->
      Application
        (desugar_expression env (EFunction xs), desugar_expression env e1)
and desugar_declarations env =
  let rec desugar rest_names rest_cs =
    let add_constructors type_name cs = 
        add_constructors type_name
          (List.map (fun (Constr (Ident c, _)) -> c, type_name) cs)
          rest_cs in

    (* collects all of the parameters of the let or let rec *)
    let rec handle_parameters t e = function
      | [] -> (t, e)
      | (Param (x, e1))::ps ->
          handle_parameters (EPi (BName x, e1, t)) (ELambda ([LBinder (BName x)], e)) ps
      | (ParamImplicit (x, e1))::ps ->
          handle_parameters (EPiImplicit (x, e1, t))
            (ELambda ([LImplicit (BName x)], e)) ps in

    let add_all_constructor_names m names =
      let add a b = match a, b with
        | None, None -> None
        | Some i, None -> Some i
        | None, Some i -> Some i
        | Some i, Some j -> Some (SS.union i j) in
      MS.merge (fun _ -> add) m names in

    (* gets the environment in which all let recs in d are bound except x,
     * and one where all are bound *)
    let get_new_envs xs x = 
      let names, cs = add_all_let_recs env xs in
      let names, cs =
        (rest_names @ names, add_all_constructor_names rest_cs cs) in
      ((names, cs), (x :: names, cs)) in

    let get_new_env_type xs x = 
      let names, cs = add_all_let_recs env xs in
      let names, cs =
        (rest_names @ names, add_all_constructor_names rest_cs cs) in
      (names, inc cs (x, "Type")) in

    function
    | [] -> []
    | (DLet (Ident x, ps, e1, e2))::xs ->
        let t, e = handle_parameters e1 e2 (List.rev ps) in
        let env1, env2 = get_new_envs xs x in
        (Let (x, (desugar_expression env1 t), (desugar_expression env1 e)))
        :: (desugar rest_names rest_cs xs)
    | (DLetRec (Ident x, ps, e1, e2))::xs ->
        let t, e = handle_parameters e1 e2 (List.rev ps) in
        let env1, env2 = get_new_envs xs x in
        (LetRec (x, (desugar_expression env1 t), (desugar_expression env2 e)))
        :: (desugar (x::rest_names) rest_cs xs) 
    | (DType (Ident x, ps, e1, cs))::xs ->
        (* the name of the type is bound inside the parameters *)
        let rec desugar_parameters env = function
          | [] -> ([], env)
          | (Param (x, t))::ps -> 
              let r, e = desugar_parameters (add_binder env (BName x)) ps in
              ((desugar_parameter env (Param (x, t)))::r, e)
          | (ParamImplicit (Ident x, t))::ps ->
              let r, e =
                desugar_parameters (add_binder env (BName (Ident x))) ps in
              ((desugar_parameter env (ParamImplicit (Ident x, t)))::r, e) in
        let env2 = get_new_env_type xs x in
        let ps, new_env = desugar_parameters env2 ps in
        (Type (x, ps, desugar_expression new_env e1
             , List.map (desugar_constructor new_env) cs))
        :: (desugar rest_names (add_constructors x cs) xs)
    | (DSimpleType (Ident x, cs))::xs -> 
        let env2 = get_new_env_type xs x in
        (Type (x, [], Universe 0, List.map (desugar_constructor env2) cs))
        :: (desugar rest_names (add_constructors x cs) xs) in
  desugar [] MS.empty
and desugar_binder = function 
  | BName (Ident id) -> Name id
  | BUnderscore -> Underscore
and desugar_case env = function
  | CCase (p, e) ->
      (desugar_pattern env p, desugar_expression (add_pattern_binders env p) e)
and desugar_parameter env = function
  | Param (Ident x, e) -> Parameter (x, desugar_expression env e)
  | ParamImplicit (Ident x, e) ->
      ParameterImplicit (x, desugar_expression env e)
and desugar_constructor env = function
  | Constr (Ident x, e) -> (x, desugar_expression env e)
and desugar_pattern env pattern = 
  let rec d env = function
    | PPair (p1, p2) ->
        let p1, env = d env p1 in
        let p2, env = d env p2 in
        (PatternPair (p1, p2), env)
    | PApplication (Ident x, ps) when is_constructor_defined env x ->
        let aux = function
          | PANormal p -> false, p
          | PAImplicit p -> true, p in
        let ps, env = List.fold_left (fun (tl, env) p ->
            let b, p = aux p in
            let p, env = d env p in
            ((b, p)::tl, env)) ([], env) ps in
        (PatternApplication (x, List.rev ps), env)
    | PApplication (Ident x, _) -> raise (Constructor_not_defined x)
    | PIdentifier (Ident x) when is_constructor_defined env x ->
        (PatternApplication (x, []), env)
    | PIdentifier (Ident x as i) -> (PatternBinder x, add_binder env (BName i))
    (* Note: inaccessible patterns cannot refer to variables defined to the
     * right in the same pattern *)
    | PInaccessible exp -> (PatternInaccessible (desugar_expression env exp)
                          , env)
    | PUnderscore -> (PatternUnderscore, env) in

  let (desugared, _) = d env pattern in
  desugared

let rec collect_binders l env = function
  | Lambda (b, e) ->
      let b = resugar_binder b in
      collect_binders ((LBinder b)::l) (add_binder env b) e
  | LambdaImplicit (b, e) ->
      let b = resugar_binder b in
      collect_binders ((LImplicit b)::l) (add_binder env b) e
  | e -> (l, env, e)
and resugar_expression env = function
  | Pair (e1, e2) ->
      EPair (resugar_expression env e1, resugar_expression env e2)
  | Lambda (b, e) ->
      let bs, new_env, e = 
        collect_binders [LBinder (resugar_binder b)]
          (add_binder env (resugar_binder b)) e in
      ELambda (List.rev bs, resugar_expression new_env e)
  | LambdaImplicit (b, e) ->
      let bs, new_env, e =
        collect_binders [LImplicit (resugar_binder b)]
          (add_binder env (resugar_binder b)) e in
      ELambda (List.rev bs, resugar_expression new_env e)
  | Pi (Underscore, e1, e2) ->
      EArrow (resugar_expression env e1, resugar_expression env e2)
  | Pi (b, e1, e2) ->
      let b = resugar_binder b in
      EPi (b, resugar_expression env e1
         , resugar_expression (add_binder env b) e2)
  | PiImplicit (x, e1, e2) ->
      EPiImplicit (Ident x, resugar_expression env e1
         , resugar_expression (add_binder env (BName (Ident x))) e2)
  | Sigma (Underscore, e1, e2) ->
      ETimes (resugar_expression env e1, resugar_expression env e2)
  | Sigma (b, e1, e2) -> 
      let b = resugar_binder b in
      ESigma (b, resugar_expression env e1
            , resugar_expression (add_binder env b) e2)
  | Function cs ->
      EFunction (List.map (fun (p, e) ->
        CCase (resugar_pattern env p
             , resugar_expression
                 (add_pattern_binders env (resugar_pattern env p))
          e)) cs)
  | LocalDeclaration (ds, e) ->
      let new_env = add_local_declaration_binders env ds in
      EDeclaration (resugar_declarations env ds, resugar_expression new_env e)
  | Application (Function cs, e) ->
      EMatch (resugar_expression env e, List.map (fun (p, e)
      -> CCase (resugar_pattern env p
              , resugar_expression
                  (add_pattern_binders env (resugar_pattern env p))
           e)) cs)
  | Application (e1, e2) ->
      EApplication (resugar_expression env e1, resugar_expression env e2)
  | ApplicationImplicit (e1, e2) ->
      EApplicationImplicit (resugar_expression env e1, resugar_expression env e2)
  | Universe 0 -> EUnindexedUniverse
  | Universe i -> EUniverse i
  | UnitType -> EUnitType
  | Unit -> EUnit
  | Index i -> EIdentifier (Ident (get_binder_name env i))
  | Constructor x -> EIdentifier (Ident x)
  | Proj1 e -> EProj1 (resugar_expression env e)
  | Proj2 e -> EProj2 (resugar_expression env e)
  | Meta (false, i) -> EMetaInternal i
  | Meta (true, i) -> EMetaInternalImplicit i
and resugar_declarations env =
  let rec resugar rest_names rest_cs =
    let add_constructors type_name cs =
      add_constructors type_name
        (List.map (fun (x, _) -> (x, type_name)) cs) rest_cs in

    let add_all_constructor_names m names =
      let add a b = match a, b with
        | None, None -> None
        | Some i, None -> Some i
        | None, Some i -> Some i
        | Some i, Some j -> Some (SS.union i j) in
      MS.merge (fun _ -> add) m names in

    (* gets the environment in which all let recs in d are bound except x,
     * and one where all are bound *)
    let get_new_envs xs x =
      let names, cs = add_local_let_recs env xs in
      let names, cs =
        (rest_names @ names, add_all_constructor_names rest_cs cs) in
      ((names, cs), (x :: names, cs)) in

    let get_new_env_type xs x =
      let names, cs = add_local_let_recs env xs in
      let names, cs =
        (rest_names @ names, add_all_constructor_names rest_cs cs) in
      (names, inc cs (x, "Type")) in

    function
    | [] -> []
    | (Let (x, e1, e))::xs ->
        let env1, env2 = get_new_envs xs x in
        (match resugar_expression env1 e with
         | ELambda (bs, e) ->
             let rec collect_binders env ps t = function
               | [] -> (ps, t, env, [])
               | (LBinder (BName (Ident b)))::bs ->
                   (match t with
                    | Pi (Name b2, e1, e2) ->
                        let new_env = add_binder env (BName (Ident b2)) in
                        let e1 = resugar_expression env e1 in
                        if b = b2
                        then collect_binders new_env ((Param (Ident b, e1))::ps) e2 bs
                        else (ps, t, env, (LBinder (BName (Ident b)))::bs)
                    | _ -> (ps, t, env, (LBinder (BName (Ident b)))::bs))
               | (LImplicit (BName (Ident b)))::bs ->
                   (match t with
                    | PiImplicit (b2, e1, e2) ->
                        let new_env = add_binder env (BName (Ident b2)) in
                        let e1 = resugar_expression env e1 in
                        if b = b2
                        then collect_binders new_env ((ParamImplicit (Ident b, e1))::ps) e2 bs
                        else (ps, t, env, (LImplicit (BName (Ident b))::bs))
                    | _ -> (ps, t, env, (LImplicit (BName (Ident b)))::bs))
               | b::bs -> (ps, t, env, b::bs) in
             (match collect_binders env1 [] e1 bs with 
              | ps, t, type_env, [] -> 
                  DLet (Ident x, List.rev ps, resugar_expression type_env t, e)
              | ps, t, type_env, bs -> 
                  DLet (Ident x, List.rev ps
                      , resugar_expression type_env t, ELambda (bs, e)))
         | e -> DLet (Ident x, [], resugar_expression env1 e1, e))
                :: (resugar rest_names rest_cs xs)
    | (LetRec (x, e1, e))::xs ->
        let env1, env2 = get_new_envs xs x in
        (match resugar_expression env2 e with
         | ELambda (bs, e) ->
             let rec collect_binders env ps t = function
               | [] -> (ps, t, env, [])
               | (LBinder (BName (Ident b)))::bs ->
                   (match t with
                    | Pi (Name b2, e1, e2) ->
                        let new_env = add_binder env (BName (Ident b2)) in
                        let e1 = resugar_expression env e1 in
                        if b = b2
                        then collect_binders new_env ((Param (Ident x, e1))::ps) e2 bs
                        else (ps, t, env, (LBinder (BName (Ident b)))::bs)
                    | _ -> (ps, t, env, (LBinder (BName (Ident b)))::bs))
               | (LImplicit (BName (Ident b)))::bs ->
                   (match t with
                    | PiImplicit (b2, e1, e2) ->
                        let new_env = add_binder env (BName (Ident b2)) in
                        let e1 = resugar_expression env e1 in
                        if b = b2
                        then collect_binders new_env ((ParamImplicit (Ident b, e1))::ps) e2 bs
                        else (ps, t, env, (LImplicit (BName (Ident b))::bs))
                    | _ -> (ps, t, env, (LImplicit (BName (Ident b)))::bs))
             | b::bs -> (ps, t, env, b::bs) in
             (match collect_binders env1 [] e1 bs with 
              | ps, t, type_env, [] ->
                  DLetRec (Ident x, List.rev ps
                         , resugar_expression type_env t, e)
              | ps, t, type_env, bs ->
                  DLetRec (Ident x, List.rev ps
                         , resugar_expression type_env t, ELambda (bs, e)))
         | e -> DLetRec (Ident x, [], resugar_expression env1 e1, e))
        :: (resugar (x::rest_names) rest_cs xs)
    | (Type (x, [], Universe 0, cs))::xs ->
        let env2 = get_new_env_type xs x in
        (DSimpleType (Ident x, List.map (fun (x, e) ->
          Constr (Ident x, resugar_expression env2 e)) cs))
          :: (resugar rest_names (add_constructors x cs) xs)
    | (Type (x, ps, e, cs))::xs ->
      let rec resugar_parameters env = function
        | [] -> ([], env)
        | (Parameter (x, t))::ps -> 
            let b = BName (Ident x) in
            let r, e = resugar_parameters (add_binder env b) ps in
            (Param (Ident x, resugar_expression env t)::r, e)
        | (ParameterImplicit (x, t))::ps -> 
            let r, e = resugar_parameters (add_binder env (BName (Ident x))) ps in
            (ParamImplicit (Ident x, resugar_expression env t)::r, e) in
      let env2 = get_new_env_type xs x in
      let ps, env = resugar_parameters env2 ps in
      (DType (Ident x, ps, resugar_expression env e, List.map (fun (x, e) ->
        Constr (Ident x, resugar_expression env e)) cs))
      :: (resugar rest_names (add_constructors x cs) xs) in
  resugar [] MS.empty
and resugar_binder = function
  | Underscore -> BUnderscore
  | Name x -> BName (Ident x)
and resugar_pattern env pattern = 
  let rec r env = function
    | PatternPair (p1, p2) ->
        let (p1, env) = r env p1 in
        let (p2, env) = r env p2 in
        (PPair (p1, p2), env)
    | PatternApplication (x, []) ->
        (PIdentifier (Ident x), env)
    | PatternApplication (x, ps) ->
        let (ps, env) = List.fold_left (fun (tl, env) (b, p) ->
          let (p, env) = r env p in
          let p = if b then PAImplicit p else PANormal p in
          (p::tl, env)) ([], env) ps in
        (PApplication (Ident x, List.rev ps), env)
    | PatternBinder x ->
        (PIdentifier (Ident x), add_binder env (BName (Ident x)))
    | PatternUnderscore -> (PUnderscore, env)
    | PatternInaccessible e ->
        (PInaccessible (resugar_expression env e), env) in

  let (resugared, _) = r env pattern in
  resugared

(* exp printing functions -- should be modified if Concrete.cf is modified *)
let rec pr_exp fmt = function
  | EPair (e1, e2) -> fprintf fmt "@[<hov>%a,@ %a@]" pr_exp3 e1 pr_exp e2
  | e -> pr_exp1 fmt e
and pr_exp1 fmt = function
  | ELambda (l, e) ->
      fprintf fmt "@[<hov2>fun %a ->@ %a@]" pr_lambda_binders l pr_exp1 e
  | EFunction l -> fprintf fmt "@[<hov>function@ %a@]" pr_cases l
  | EMatch (e, l) ->
      fprintf fmt "@[<hov>match %a with@ %a" pr_exp e pr_cases l
  | e -> pr_exp2 fmt e
and pr_exp2 fmt = function
  | EArrow (e1, e2) -> fprintf fmt "@[<hov>%a@ -> %a@]" pr_exp3 e1 pr_exp2 e2
  | EPi (b, e1, e2) ->
      fprintf fmt "@[<hov>(%a : %a)@ -> %a@]" pr_binder b pr_exp e1 pr_exp2 e2
  | EPiImplicit (Ident x, e1, e2) ->
      fprintf fmt "@[<hov>{%s : %a}@ -> %a@]" x pr_exp e1 pr_exp2 e2
  | EDeclaration (l, e) -> fprintf fmt "@[<hov>%a in@ %a@]" pr_decls l pr_exp2 e
  | e -> pr_exp3 fmt e
and pr_exp3 fmt = function
  | ESigma (b, e1, e2) ->
      fprintf fmt "@[<hov>(%a : %a)@ * %a@]" pr_binder b pr_exp e1 pr_exp3 e2
  | ETimes (e1, e2) -> fprintf fmt "@[<hov>%a@ * %a@]" pr_exp4 e1 pr_exp3 e2
  | e -> pr_exp4 fmt e
and pr_exp4 fmt = function
  | EApplication (e1, e2) ->
      fprintf fmt "@[<hov2>%a@ %a@]" pr_exp4 e1 pr_exp5 e2
  | EApplicationImplicit (e1, e2) ->
      fprintf fmt "@[<hov2>%a@ {%a}@]" pr_exp4 e1 pr_exp e2
  | e -> pr_exp5 fmt e
and pr_exp5 fmt = function
  | EUniverse i -> fprintf fmt "Type %i" i
  | EUnindexedUniverse -> fprintf fmt "Type"
  | EUnit -> fprintf fmt "()"
  | EUnitType -> fprintf fmt "Unit"
  | EIdentifier (Ident i) -> fprintf fmt "%s" i
  | EProj1 e -> fprintf fmt "%a.1" pr_exp5 e
  | EProj2 e -> fprintf fmt "%a.2" pr_exp5 e
  | EMeta -> fprintf fmt "?"
  | EMetaInternal i -> fprintf fmt "?%i" i
  | EMetaInternalImplicit i -> fprintf fmt "?I%i" i
  | e -> fprintf fmt "(%a)" pr_exp e

and pr_binder fmt = function
  | BName (Ident i) -> fprintf fmt "%s" i
  | BUnderscore -> fprintf fmt "_"
and pr_lambda_binder fmt = function
  | LBinder x -> pr_binder fmt x
  | LImplicit x -> fprintf fmt "{%a}" pr_binder x
and pr_lambda_binders fmt = function
  | [] -> ()
  | [x] -> pr_lambda_binder fmt x
  | x::xs -> fprintf fmt "%a %a" pr_lambda_binder x pr_lambda_binders xs
and pr_binders fmt = function
  | [] -> ()
  | [x] -> pr_binder fmt x
  | x::xs -> fprintf fmt "%a %a" pr_binder x pr_binders xs

and pr_case fmt = function
  | CCase (p, e) -> fprintf fmt "@[<hov2>| %a ->@ %a@]" pr_pattern p pr_exp2 e
and pr_cases fmt = function
  | [] -> ()
  | [x] -> pr_case fmt x
  | x::xs -> fprintf fmt "@[<hov>%a@ %a@]" pr_case x pr_cases xs

and pr_pattern fmt = function
  | PPair (p1, p2) ->
      fprintf fmt "@[<hov>%a,@ %a@]" pr_pattern1 p1 pr_pattern p2
  | p -> pr_pattern1 fmt p
and pr_pattern1 fmt = function
  | PApplication (Ident i, l) -> fprintf fmt "@[<hov2>%s@ %a@]" i pr_applicands l
  | p -> pr_pattern2 fmt p
and pr_pattern2 fmt = function
  | PIdentifier (Ident i) -> fprintf fmt "%s" i
  | PUnderscore -> fprintf fmt "_"
  | PInaccessible e -> fprintf fmt ".%a" pr_exp5 e
  | p -> fprintf fmt "(%a)" pr_pattern p
and pr_applicands fmt = function
  | [] -> ()
  | [PANormal x] -> pr_pattern2 fmt x
  | [PAImplicit x] -> fprintf fmt "@[<hov>{%a}@]" pr_pattern x
  | (PANormal x)::xs -> fprintf fmt "@[<hov>%a@ %a@]" pr_pattern2 x pr_applicands xs
  | (PAImplicit x)::xs -> fprintf fmt "@[<hov>{%a}@ %a@]" pr_pattern x pr_applicands xs

and pr_decl fmt = function
  | DLet (Ident i, ps, a, e) ->
      fprintf fmt "let %s%a@ : %a =@ %a" i
        pr_params ps pr_exp a pr_exp e
  | DLetRec (Ident i, ps, a, e) ->
      fprintf fmt "let rec %s%a@ : %a =@ %a" i
        pr_params ps pr_exp a pr_exp e
  | DType (Ident i, ps, e, cs) -> 
      fprintf fmt "type %s%a@ : %a =@ %a" i
        pr_params ps pr_exp e pr_constructors cs
  | DSimpleType (Ident i, cs) ->
      fprintf fmt "type %s =@ %a" i pr_constructors cs
and pr_decls fmt = function
  | [] -> ()
  | [x] -> fprintf fmt "@[<hov2>%a@]" pr_decl x
  | x::xs -> fprintf fmt "@[<hov2>%a@]@ @[<hov2>and %a@]" pr_decl x pr_decls xs

and pr_param fmt = function
  | Param (Ident x, e) -> fprintf fmt "@ (%s : %a)" x pr_exp e
  | ParamImplicit (Ident x, e) -> fprintf fmt "@ {%s : %a}" x pr_exp e
and pr_params fmt = function
  | [] -> ()
  | [x] -> pr_param fmt x
  | x::xs -> fprintf fmt "%a%a" pr_param x pr_params xs

and pr_constructor fmt = function
  | Constr (Ident i, e) -> fprintf fmt "@[<hov>| %s@ : %a@]" i pr_exp2 e
and pr_constructors fmt = function
  | [] -> ()
  | [x] -> pr_constructor fmt x
  | x::xs -> fprintf fmt "@[<hov>%a@ %a@]" pr_constructor x pr_constructors xs

let print_expression env exp =
  Buffer.clear stdbuf;
  pr_exp str_formatter (resugar_expression env exp);
  pp_print_flush str_formatter ();
  Buffer.contents stdbuf

let print_pattern env patt = 
  Buffer.clear stdbuf;
  pr_pattern str_formatter (resugar_pattern env patt);
  pp_print_flush str_formatter ();
  Buffer.contents stdbuf

let print_declarations env decl = 
  Buffer.clear stdbuf;
  pr_decls str_formatter (resugar_declarations env decl);
  pp_print_flush str_formatter ();
  Buffer.contents stdbuf
 
