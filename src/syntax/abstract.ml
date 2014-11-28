open List

open AbsConcrete

exception Invalid_expression of string
exception Constructor_not_defined of string

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

let add_binder (names, cs) = function
  | BUnderscore -> (names, cs)
  | BName (Ident x) -> (x::names, cs)

(* adds all of the bound variables to env in reverse order *)
let rec add_all_declaration_binders (names, cs) = function
  | [] -> (names, cs) 
  | x::xs ->
      let get_name (Constr (Ident x, _)) = x in
      match x with
      | DLet (Ident x, _, _, _) ->
          add_all_declaration_binders (x::names, cs) xs
      | DLetRec (Ident x, _, _, _) ->
          add_all_declaration_binders (x::names, cs) xs
      | DType (Ident x, _, _, l) ->
          add_all_declaration_binders
            (x::names, rev_append (map get_name l) cs) xs
      | DSimpleType (Ident x, l) ->
          add_all_declaration_binders
            (x::names, rev_append (map get_name l) cs) xs

(* adds all of the vound variables to env in reverse order *)
let rec add_local_declaration_binders (names, cs) = function
  | [] -> (names, cs) 
  | x::xs ->
      match x with
      | Let (x, _, _) -> add_local_declaration_binders (x::names, cs) xs
      | LetRec (x, _, _) -> add_local_declaration_binders (x::names, cs) xs
      | Type (x, _, _, l) ->
          add_local_declaration_binders
            (x::names, rev_append (map (fun (x, _) -> x) l) cs) xs

let is_constructor_defined (env, cs) x = exists (fun y -> x = y) cs

let add_pattern_binders (names, cs) p =
  let rec add names = function
    | PPair (p1, p2) -> add (add names p1) p2
    | PApplication (_, l) -> fold_left add names l
    | PIdentifier (Ident x) ->
        if is_constructor_defined (names, cs) x then names else x::names
    | PUnderscore -> names in
  (add names p, cs)

(* Find the de Bruijn index used to refer to x in env *)
let lookup_index (env, cs) x =
  let rec lookup_index_from env x i =
    match env with
    | [] -> None
    | y::l -> if y = x then Some i else lookup_index_from l x (i + 1) in
  lookup_index_from env x 0

(* Find the name associated with a de Bruijn index *)
let get_binder_name (env, cs) = nth env

let rec desugar_expression env = function
  | EPair (e1, e2) ->
      Pair (desugar_expression env e1, desugar_expression env e2)
  | ELambda ([], _) ->
      raise
        (Invalid_expression "Lambda abstractions must have at least one binder")
  | ELambda ([x], e1) ->
      Lambda (desugar_binder x, desugar_expression (add_binder env x) e1)
  | ELambda (x::xs, e1) ->
      desugar_expression env (ELambda ([x], ELambda (xs, e1)))
  | EPi (x, e1, e2) ->
      Pi (desugar_binder x, desugar_expression env e1
        , desugar_expression (add_binder env x) e2)
  | ESigma (x, e1, e2) ->
      Sigma (desugar_binder x, desugar_expression env e1
           , desugar_expression (add_binder env x) e2)
  | EFunction xs -> Function (map (desugar_case env) xs) 
  | EDeclaration (d, e1) ->
      (* Mutually recursive declarations *)
      let new_env = add_all_declaration_binders env d in
      LocalDeclaration
        (desugar_declarations env d, desugar_expression new_env e1)
  | EApplication (e1, e2) ->
      Application (desugar_expression env e1, desugar_expression env e2)
  | EUniverse -> Universe
  | EUnitType -> UnitType
  | EUnit -> Unit
  | EIdentifier (Ident x) -> ( 
      match lookup_index env x with
      | Some i -> Index i (* x is bound to index i *)
      | None -> 
          if not (is_constructor_defined env x)
          then raise (Constructor_not_defined x)
          else Constructor x)
  | EProj1 e1 -> Proj1 (desugar_expression env e1)
  | EProj2 e2 -> Proj2 (desugar_expression env e2)
  | EArrow (e1, e2) ->
      Pi (Underscore, desugar_expression env e1, desugar_expression env e2)
  | ETimes (e1, e2) ->
      Sigma (Underscore, desugar_expression env e1, desugar_expression env e2)
  | EMatch (e1, xs) ->
      Application
        (desugar_expression env (EFunction xs), desugar_expression env e1)
and desugar_declarations env =
  let rec desugar rest_names rest_cs =
    let add_constructors cs = 
      rev_append (map (fun (Constr (Ident x, _)) -> x) cs) rest_cs in
    (* collects all of the parameter of the let or let rec *)
    let rec handle_parameters t e = function
      | [] -> (t, e)
      | (Param (b, e1))::ps ->
          handle_parameters (EPi (b, e1, t)) (ELambda ([b], e)) ps in
    (* gets the environment in which all declarations in d are bound except x,
     * and one where all are bound *)
    let get_new_envs xs x = 
      let names, cs = add_all_declaration_binders env xs in
      let names, cs = (rest_names @ names, rest_cs @ cs) in
      ((names, cs), (x :: names, cs)) in
    function
    | [] -> []
    | (DLet (Ident x, ps, e1, e2))::xs ->
        let t, e = handle_parameters e1 e2 (rev ps) in
        let env1, env2 = get_new_envs xs x in
        (Let (x, (desugar_expression env1 t), (desugar_expression env1 e)))
        :: (desugar (x::rest_names) rest_cs xs)
    | (DLetRec (Ident x, ps, e1, e2))::xs ->
        let t, e = handle_parameters e1 e2 (rev ps) in
        let env1, env2 = get_new_envs xs x in
        (LetRec (x, (desugar_expression env1 t), (desugar_expression env2 e)))
        :: (desugar (x::rest_names) rest_cs xs) 
    | (DType (Ident x, ps, e1, cs))::xs ->
        (* the name of the type is bound inside the parameters *)
        let rec desugar_parameters env = function
          | [] -> ([], env)
          | (Param (b, t))::ps -> 
              let r, e = desugar_parameters (add_binder env b) ps in
              ((desugar_parameter env (Param (b, t)))::r, e) in
        let env1, env2 = get_new_envs xs x in
        let ps, new_env = desugar_parameters env2 ps in
        (Type (x, ps, desugar_expression new_env e1
             , map (desugar_constructor new_env) cs))
        :: (desugar (x::rest_names) (add_constructors cs) xs)
    | (DSimpleType (Ident x, cs))::xs -> 
        let env1, env2 = get_new_envs xs x in
        (Type (x, [], Universe, map (desugar_constructor env2) cs))
        :: (desugar (x::rest_names) (add_constructors cs) xs) in
  desugar [] []
and desugar_binder = function 
  | BName (Ident id) -> Name id
  | BUnderscore -> Underscore
and desugar_case env = function
  | CCase (p, e) ->
      (desugar_pattern env p, desugar_expression (add_pattern_binders env p) e)
and desugar_parameter env = function
  | Param (x, e) -> (desugar_binder x, desugar_expression env e)
and desugar_constructor env = function
  | Constr (Ident x, e) -> (x, desugar_expression env e)
and desugar_pattern env = function
  | PPair (p1, p2) ->
      PatternPair (desugar_pattern env p1, desugar_pattern env p2)
  | PApplication (Ident x, ps) ->
      PatternApplication (x, map (desugar_pattern env) ps)
  | PIdentifier (Ident x) -> 
      if is_constructor_defined env x
      then PatternApplication (x, [])
      else PatternBinder x
  | PUnderscore -> PatternUnderscore

let rec resugar_expression env = function
  | Pair (e1, e2) ->
      EPair (resugar_expression env e1, resugar_expression env e2)
  | Lambda (b, e) ->
      let rec collect_binders l env = function
        | Lambda (b, e) -> 
            let b = resugar_binder b in
            collect_binders (b::l) (add_binder env b) e
        | e -> (l, env, e) in
      let bs, new_env, e =
        collect_binders [resugar_binder b]
          (add_binder env (resugar_binder b)) e in
      ELambda (rev bs, resugar_expression new_env e)
  | Pi (Underscore, e1, e2) ->
      EArrow (resugar_expression env e1, resugar_expression env e2)
  | Pi (b, e1, e2) ->
      let b = resugar_binder b in
      EPi (b, resugar_expression env e1
         , resugar_expression (add_binder env b) e2)
  | Sigma (Underscore, e1, e2) ->
      ETimes (resugar_expression env e1, resugar_expression env e2)
  | Sigma (b, e1, e2) -> 
      let b = resugar_binder b in
      ESigma (b, resugar_expression env e1
            , resugar_expression (add_binder env b) e2)
  | Function cs ->
      EFunction (map (fun (p, e) ->
        CCase (resugar_pattern p
             , resugar_expression (add_pattern_binders env (resugar_pattern p))
          e)) cs)
  | LocalDeclaration (ds, e) ->
      let new_env = add_local_declaration_binders env ds in
      EDeclaration (resugar_declarations env ds, resugar_expression new_env e)
  | Application (Function cs, e) ->
      EMatch (resugar_expression env e, map (fun (p, e)
      -> CCase (resugar_pattern p
              , resugar_expression (add_pattern_binders env (resugar_pattern p))
           e)) cs)
  | Application (e1, e2) ->
      EApplication (resugar_expression env e1, resugar_expression env e2)
  | Universe -> EUniverse
  | UnitType -> EUnitType
  | Unit -> EUnit
  | Index i -> EIdentifier (Ident (get_binder_name env i))
  | Constructor x -> EIdentifier (Ident x)
  | Proj1 e -> EProj1 (resugar_expression env e)
  | Proj2 e -> EProj2 (resugar_expression env e)
and resugar_declarations env =
  let rec resugar rest_names rest_cs =
    let add_constructors cs = rev_append (map (fun (x, _) -> x) cs) rest_cs in
    (* gets the environment in which all declarations in d are bound except x,
     * and one where all are bound *)
    let get_new_envs xs x = 
      let names, cs = add_local_declaration_binders env xs in
      let names, cs = (rest_names @ names, rest_cs @ cs) in
      ((names, cs), (x :: names, cs)) in
    function
    | [] -> []
    | (Let (x, e1, e))::xs ->
        let env1, env2 = get_new_envs xs x in
        (match resugar_expression env1 e with
         | ELambda (bs, e) ->
             let rec collect_binders env ps t = function
               | [] -> (ps, t, env, [])
               | b::bs ->
                   (match t with
                    | Pi (b2, e1, e2) ->
                        let b2 = resugar_binder b2 in
                        let new_env = add_binder env b2 in
                        let e1 = resugar_expression env e1 in
                        if b = b2
                        then collect_binders new_env ((Param (b, e1))::ps) e2 bs
                        else (ps, t, env, b::bs)
                    | _ -> (ps, t, env, b::bs)) in
             (match collect_binders env1 [] e1 bs with 
              | ps, t, type_env, [] -> 
                  DLet (Ident x, rev ps, resugar_expression type_env t, e)
              | ps, t, type_env, bs -> 
                  DLet (Ident x, rev ps
                      , resugar_expression type_env t, ELambda (bs, e)))
         | e -> DLet (Ident x, [], resugar_expression env1 e1, e))
                :: (resugar (x::rest_names) rest_cs xs)
    | (LetRec (x, e1, e))::xs ->
        let env1, env2 = get_new_envs xs x in
        (match resugar_expression env2 e with
         | ELambda (bs, e) ->
             let rec collect_binders env ps t = function
               | [] -> (ps, t, env, [])
               | b::bs ->
                   (match t with
                    | Pi (b2, e1, e2) ->
                        let b2 = resugar_binder b2 in
                        let new_env = add_binder env b2 in
                        let e1 = resugar_expression env e1 in
                        if b = b2
                        then collect_binders new_env ((Param (b, e1))::ps) e2 bs
                        else (ps, t, env, b::bs)
                    | _ -> (ps, t, env, b::bs)) in
             (match collect_binders env1 [] e1 bs with 
              | ps, t, type_env, [] ->
                  DLetRec (Ident x, rev ps, resugar_expression type_env t, e)
              | ps, t, type_env, bs ->
                  DLetRec (Ident x, rev ps
                         , resugar_expression type_env t, ELambda (bs, e)))
         | e -> DLetRec (Ident x, [], resugar_expression env1 e1, e))
        :: (resugar (x::rest_names) rest_cs xs)
    | (Type (x, [], Universe, cs))::xs ->
        let env1, env2 = get_new_envs xs x in
        (DSimpleType (Ident x, map (fun (x, e) ->
          Constr (Ident x, resugar_expression env2 e)) cs))
          :: (resugar (x::rest_names) (add_constructors cs) xs)
    | (Type (x, ps, e, cs))::xs ->
      let rec resugar_parameters env = function
        | [] -> ([], env)
        | (b, t)::ps -> 
            let b = resugar_binder b in
            let r, e = resugar_parameters (add_binder env b) ps in
            (Param (b, resugar_expression env t)::r, e) in
      let env1, env2 = get_new_envs xs x in
      let ps, env = resugar_parameters env2 ps in
      (DType (Ident x, ps, resugar_expression env e, map (fun (x, e) ->
        Constr (Ident x, resugar_expression env e)) cs))
      :: (resugar (x::rest_names) (add_constructors cs) xs) in
  resugar [] []
and resugar_binder = function
  | Underscore -> BUnderscore
  | Name x -> BName (Ident x)
and resugar_pattern = function
  | PatternPair (p1, p2) -> PPair (resugar_pattern p1, resugar_pattern p2)
  | PatternApplication (x, []) -> PIdentifier (Ident x)
  | PatternApplication (x, ps) -> PApplication (Ident x, map resugar_pattern ps)
  | PatternBinder x -> PIdentifier (Ident x)
  | PatternUnderscore -> PUnderscore

