open List

open AbsConcrete

exception Invalid_expression of string

type expression_or_declaration =
  | Expression of expression
  | Declaration of declaration list
and expression =
  | Pair of expression * expression
  | Lambda of binding * expression
  | Pi of binding * expression * expression
  | Sigma of binding * expression * expression
  | Function of (pattern * expression) list
  | LocalDeclaration of declaration list * expression
  | Application of expression * expression
  | Universe
  | UnitType
  | Unit
  | Identifier of string
  | Proj1 of expression
  | Proj2 of expression
and binding =
  | Underscore
  | Name of string 
and pattern =
  | PatternPair of pattern * pattern 
  | PatternApplication of string * pattern list
  | PatternIdentifier of string
  | PatternUnderscore
and declaration =
  | Let of string * expression * expression
  | LetRec of string * expression * expression
  | Type of string * (binding * expression) list
          * expression * (string * expression) list

let rec desugar = function
  | ReplExpression (e, _) -> Expression (desugar_expression e)
  | ReplDeclaration (d, _) -> Declaration (map desugar_declaration d)
and desugar_expression = function
  | EPair (e1, e2) -> Pair (desugar_expression e1, desugar_expression e2)
  | ELambda ([], _) ->
      raise (Invalid_expression "Lambda abstractions must have at least one 
      binding")
  | ELambda ([x], e1) -> Lambda (desugar_binding x, desugar_expression e1)
  | ELambda (x::xs, e1) ->
      Lambda (desugar_binding x, desugar_expression (ELambda (xs, e1)))
  | EPi (x, e1, e2) ->
      Pi (desugar_binding x, desugar_expression e1, desugar_expression e2)
  | ESigma (x, e1, e2) -> 
      Sigma (desugar_binding x, desugar_expression e1, desugar_expression e2)
  | EFunction xs -> Function (map desugar_case xs) 
  | EDeclaration (d, e1) ->
      LocalDeclaration (map desugar_declaration d, desugar_expression e1)
  | EApplication (e1, e2) ->
      Application (desugar_expression e1, desugar_expression e2)
  | EUniverse -> Universe
  | EUnitType -> UnitType
  | EUnit -> Unit
  | EIdentifier (Ident x) -> Identifier x
  | EProj1 e1 -> Proj1 (desugar_expression e1)
  | EProj2 e2 -> Proj2 (desugar_expression e2)
  | EArrow (e1, e2) ->
      Pi (Underscore, desugar_expression e1, desugar_expression e2)
  | ETimes (e1, e2) ->
      Sigma (Underscore, desugar_expression e1, desugar_expression e2)
  | EMatch (e1, xs) ->
      Application (desugar_expression (EFunction xs), desugar_expression e1)
and desugar_declaration = function
  | DLet (Ident x, ps, e1, e2) ->
      let rec handle_parameters t e = function
        | [] -> (t, e)
        | (Param (b, e1))::ps ->
            handle_parameters (Pi (desugar_binding b, desugar_expression e1, t))
            (Lambda (desugar_binding b, e)) ps in
      let t, e =
        handle_parameters (desugar_expression e1) (desugar_expression e2) (rev ps) in
      Let (x, t, e)
  | DLetRec (Ident x, ps, e1, e2) ->
      let rec handle_parameters t e = function
        | [] -> (t, e)
        | (Param (b, e1))::ps ->
            handle_parameters (Pi (desugar_binding b, desugar_expression e1, t))
            (Lambda (desugar_binding b, e)) ps in
      let t, e =
        handle_parameters (desugar_expression e1) (desugar_expression e2) (rev ps) in
      LetRec (x, t, e)
  | DType (Ident x, ps, e1, cs) -> Type (x, map desugar_parameter ps
      , desugar_expression e1, map desugar_constructor cs)
  | DSimpleType (Ident x, cs) -> 
      Type (x, [], Universe, map desugar_constructor cs)
and desugar_binding = function 
  | BName (Ident id) -> Name id
  | BUnderscore -> Underscore
and desugar_case = function
  | CCase (p, e) -> (desugar_pattern p, desugar_expression e)
and desugar_parameter = function
  | Param (x, e) -> (desugar_binding x, desugar_expression e)
and desugar_constructor = function
  | Constr (Ident x, e) -> (x, desugar_expression e)
and desugar_pattern = function
  | PPair (p1, p2) -> PatternPair (desugar_pattern p1, desugar_pattern p2)
  | PApplication (Ident x, ps) -> PatternApplication (x, map desugar_pattern ps)
  | PIdentifier (Ident x) -> PatternIdentifier x
  | PUnderscore -> PatternUnderscore

let rec resugar = function
  | Expression e -> ReplExpression ((resugar_expression e), SEMISEMI ";;")
  | Declaration ds ->
      ReplDeclaration ((map resugar_declaration ds), SEMISEMI ";;")
and resugar_expression = function
  | Pair (e1, e2) -> EPair (resugar_expression e1, resugar_expression e2)
  | Lambda (b, e) ->
      let rec collect_bindings l = function
        | Lambda (b, e) -> collect_bindings (b::l) e
        | e -> (l, e) in
      let bs, e = collect_bindings [b] e in
      ELambda (rev (map resugar_binding bs), resugar_expression e)
  | Pi (Underscore, e1, e2) -> 
      EArrow (resugar_expression e1, resugar_expression e2)
  | Pi (b, e1, e2) ->
      EPi (resugar_binding b, resugar_expression e1, resugar_expression e2)
  | Sigma (Underscore, e1, e2) ->
      ETimes (resugar_expression e1, resugar_expression e2)
  | Sigma (b, e1, e2) -> 
      ESigma (resugar_binding b, resugar_expression e1, resugar_expression e2)
  | Function cs -> EFunction
      (map (fun (p, e) -> CCase (resugar_pattern p, resugar_expression e)) cs)
  | LocalDeclaration (ds, e) ->
      EDeclaration (map resugar_declaration ds, resugar_expression e)
  | Application (Function cs, e) -> EMatch (resugar_expression e
      , map (fun (p, e) -> CCase (resugar_pattern p, resugar_expression e)) cs)
  | Application (e1, e2) ->
      EApplication (resugar_expression e1, resugar_expression e2)
  | Universe -> EUniverse
  | UnitType -> EUnitType
  | Unit -> EUnit
  | Identifier x -> EIdentifier (Ident x)
  | Proj1 e -> EProj1 (resugar_expression e)
  | Proj2 e -> EProj2 (resugar_expression e)
and resugar_declaration = function
  | Let (x, e1, e) ->
      (match resugar_expression e with
       | ELambda (bs, e) ->
           let rec collect_bindings ps t = function
             | [] -> (ps, t, [])
             | b::bs ->
                 (match t with
                  | Pi (b2, e1, e2) ->
                      let b2, e1 = resugar_binding b2, resugar_expression e1 in
                      if b = b2 then
                        collect_bindings ((Param (b, e1))::ps) e2 bs
                      else (ps, t, b::bs)
                  | _ -> (ps, t, b::bs)) in
           (match collect_bindings [] e1 bs with 
            | ps, t, [] -> DLet (Ident x, rev ps, resugar_expression t, e)
            | ps, t, bs ->
                DLet (Ident x, rev ps, resugar_expression t, ELambda (bs, e)))
       | e -> DLet (Ident x, [], resugar_expression e1, e))
  | LetRec (x, e1, e) ->
      (match resugar_expression e with
       | ELambda (bs, e) ->
           let rec collect_bindings ps t = function
             | [] -> (ps, t, [])
             | b::bs ->
                 (match t with
                  | Pi (b2, e1, e2) ->
                      let b2, e1 = resugar_binding b2, resugar_expression e1 in
                      if b = b2 then
                        collect_bindings ((Param (b, e1))::ps) e2 bs
                      else (ps, t, b::bs)
                  | _ -> (ps, t, b::bs)) in
           (match collect_bindings [] e1 bs with 
            | ps, t, [] -> DLetRec (Ident x, rev ps, resugar_expression t, e)
            | ps, t, bs -> DLetRec
                (Ident x, rev ps, resugar_expression t, ELambda (bs, e)))
       | e -> DLetRec (Ident x, [], resugar_expression e1, e)) 
  | Type (x, [], Universe, cs) ->
      DSimpleType (Ident x
      , map (fun (x, e) -> Constr (Ident x, resugar_expression e)) cs)
  | Type (x, ps, e, cs) ->
      DType (Ident x
      , map (fun (b, e) -> Param (resugar_binding b, resugar_expression e)) ps
      , resugar_expression e
      , map (fun (x, e) -> Constr (Ident x, resugar_expression e)) cs)
and resugar_binding = function
  | Underscore -> BUnderscore
  | Name x -> BName (Ident x)
and resugar_pattern = function
  | PatternPair (p1, p2) -> PPair (resugar_pattern p1, resugar_pattern p2)
  | PatternApplication (x, ps) -> PApplication (Ident x, map resugar_pattern ps)
  | PatternIdentifier x -> PIdentifier (Ident x)
  | PatternUnderscore -> PUnderscore

