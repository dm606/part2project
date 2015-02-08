open Abstract
open Eval
open Format
open Value

module MM = Map.Make(struct
  type t = Abstract.meta_id
  let compare = Abstract.meta_id_compare
end)

type normal_envt = [`N of normal | `D of declaration list] list
and normal =
  | NPair of normal * normal
  (* strings are names of binders; they are used for pretty-printing only *)
  | NLambda of string * int * normal
  | NPi of string * int * normal * normal
  | NSigma of string * int * normal * normal
  | NFunction of (pattern * expression) list 
               * normal_envt
  | NUniverse of int
  | NUnitType
  | NUnit
  | NConstruct of string * normal list
  | NNeutral of normal_neutral
and normal_neutral =
  | NVar of string * int 
  | NFunctionApplication of (pattern * expression) list
                          * normal_envt
                          * normal
  | NApplication of normal_neutral * normal
  | NProj1 of normal_neutral
  | NProj2 of normal_neutral
  | NMeta of meta_id

type state = Active | Failed

type constraints = (value MM.t) * (state * normal * normal) list
let no_constraints = (MM.empty, [])
let always_satisfied (_, c) = c = []
let never_satisfied (_, c) = List.exists (fun (s, _, _) -> s = Failed) c
let add_equation s x y (m, c) = (m, (s, x, y)::c)
let has_metavariable (m, _) id = MM.mem id m
let get_metavariable (m, _) id = MM.find id m
let add_metavariable (m, c) id typ = (MM.add id typ m, c)

let rec no_metavariables_neutral = function
  | NVar _ -> true
  | NFunctionApplication (_, _, n) -> no_metavariables n
  | NApplication (x, y) -> no_metavariables_neutral x && no_metavariables y
  | NProj1 x -> no_metavariables_neutral x
  | NProj2 x -> no_metavariables_neutral x
  | NMeta _ -> false
and no_metavariables = function
  | NPair (x, y) -> no_metavariables x && no_metavariables y
  | NLambda (_, _, n) -> no_metavariables n
  | NPi (_, _, x, y) -> no_metavariables x && no_metavariables y
  | NSigma (_, _, x, y) -> no_metavariables x && no_metavariables y
  | NFunction _ -> true
  | NUniverse _ | NUnitType | NUnit -> true
  | NConstruct (_, l) -> List.for_all no_metavariables l
  | NNeutral n -> no_metavariables_neutral n

let rec head_is_metavariable = function
  | NNeutral (NMeta _) -> true
  | NNeutral (NApplication (x, y)) -> head_is_metavariable (NNeutral x)
  | _ -> false

let (++) c1 c2 =
  let (+) hd tl = if List.mem hd tl then tl else hd::tl in

  List.fold_right (fun c tl -> match c with
  | (_, x, y) when x = y -> tl
  | (Active, x, y) when no_metavariables x && no_metavariables y ->
      (* x cannot be the same as y *)
      (Failed, x, y)+tl
  | _ -> c+tl) c1 c2

(* perform local simplification on a single constraint *)
let simplify x y =
  let apply x i = function
    | NNeutral n -> NNeutral (NApplication (n, NNeutral (NVar (x, i))))
    (* TODO: check order of applications *)
    | NConstruct (c, l) -> NConstruct (c, ((NNeutral (NVar (x, i)))::l))
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
        | NApplication (x1, x2) -> 
            let b, x1, y = aux_neutral x1 in
            if b then (true, NApplication (x1, x2), y)
            else
              let b, x2, y = aux x2 in
              (b, NApplication (x1, x2), y)
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
        | NPi (name, i, x1, x2) ->
            let b, x1, y = aux x1 in
            if b then (true, NPi (name, i, x1, x2), y)
            else
              let b, x2, y = aux x2 in
              (b, NPi (name, i, x1, x2), y)
        | NSigma (name, i, x1, x2) ->
            let b, x1, y = aux x1 in
            if b then (true, NSigma (name, i, x1, x2), y)
            else
              let b, x2, y = aux x2 in
              (b, NSigma (name, i, x1, x2), y)
        | NFunction _ as x -> (false, x, y)
        | NUniverse _ | NUnitType | NUnit as x -> (false, x, y)
        | NConstruct (c, l) ->
            let b, l, y = List.fold_left (fun (b, l, y) x ->
              if b then (true, x::l, y) else
                let b, x, y = aux x in
                (b, x::l, y)) (false, [], y) l in
            (b, NConstruct (c, l), y)
        | NNeutral n -> 
            let b, x, y = aux_neutral n in
            (b, NNeutral x, y) in
      let b, x, y = aux x in
      (b, [Active, x, y])

  | x, y -> (false, [Active, x, y])

(* local simplification examines constraints in isolation, until it finds one
 * which can be simplified *)
let rec perform_local_simplification (m, c) = match c with
  | [] -> (false, (m, []))
  | (Active, x, y)::tl -> (
      match simplify x y with
      | false, _ ->
          let b, (m, tl) = perform_local_simplification (m, tl) in
          (b, (m, (Active, x, y)::tl))
      | true, con ->
          (true, (m, con ++ tl)))
  | (Failed, x, y)::tl ->
      (* do not attempt to simplify constraints which cannot be satisfied *)
      let b, (m, tl) = perform_local_simplification (m, tl) in
      (b, (m, (Failed, x, y)::tl))

(* refine the constraints by one step *)
let refine constraints = 
  if never_satisfied constraints || always_satisfied constraints then
    (* if the constraints are known to be always or never satisfied, then they
     * are considered to be solved, so no refinement is performed *)
    (false, constraints)
  else
    let (b, constraints) = perform_local_simplification constraints in
    if b then (true, constraints) else
    (false, constraints)

let add_equation s x y (m, c) =
  let rec aux c = 
    let b, c = refine c in
    if b then aux c else c in
  aux (m, (s, x, y)::c)

let (>>=) c f = f c

let empty_envt = []

let rec readback i = 
  let readback_env i =
    Environment.map_to_list (fun v -> (`N (readback i v))) (fun d -> `D d) in
  let rec readback_neutral i = function
  | VVar (name, i) -> NVar (name, i)
  | VFunctionApplication (cases, env, v) ->
      NFunctionApplication (cases, readback_env i env, readback i v)
  | VApplication (v1, v2) ->
      NApplication (readback_neutral i v1, readback i v2)
  | VProj1 v -> NProj1 (readback_neutral i v)
  | VProj2 v -> NProj2 (readback_neutral i v) 
  | VMeta i -> NMeta i in 

  function
  | VPair (v1, v2) -> NPair (readback i v1, readback i v2)
  | VLambda (Underscore, e, env) -> NLambda ("_", i, readback (i + 1) (eval env e))
  | VLambda (Name x, e, env) -> 
      NLambda (x, i, readback (i + 1)
        (eval (Environment.add env (VNeutral (VVar (x, i)))) e))
  | VArrow (a, b) ->
      NPi ("_", i, readback i a, readback (i + 1) b)
  | VPi (x, v, e, env) -> 
      NPi (x, i, readback i v, readback (i + 1)
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
  | VConstruct (c, vs) -> NConstruct (c, List.map (readback i) vs)
  | VNeutral n -> NNeutral (readback_neutral i n)

let rec test_normal_equality c x y =
  let test x y c = test_normal_equality c x y in
  let test_neutral x y c = test_neutral_equality c x y in

  match x, y with
  | NPair (x1, x2), NPair (y1, y2) ->
      c >>= test x1 y1 >>= test x2 y2
  | NLambda (_, i, x), NLambda (_, j, y) when i = j -> c >>= test x y
  | NPi (_, i, x1, x2), NPi (_, j, y1, y2) when i = j ->
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
        | x::xs, y::ys -> c >>= test x y >>= aux (xs, ys)
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
      (* if x or y has a metavariable, then they maay be equal if constraints
       * are satisfied *)
      c >>= add_equation Active (NNeutral x) (NNeutral y)
  | _ -> c >>= add_equation Failed (NNeutral x) (NNeutral y) 

let test_equality i constraints x y =
  test_normal_equality constraints (readback i x) (readback i y)
let test_expression_equality env x y =
  test_equality 0 no_constraints (eval env x) (eval env y)


(* the following functions are numbered according to the precedence of the
 * values which they print *)
let rec pr_neutral fmt = function
  | v -> pr_neutral4 fmt v
and pr_neutral4 fmt = function
  | NApplication (n, v) ->
      fprintf fmt "@[<hov2>%a@ %a@]" pr_neutral4 n pr_normal5 v
  | NFunctionApplication (_, _, n) ->
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
  | NFunction (_, _) -> fprintf fmt "<function>"
  | v -> pr_normal2 fmt v
and pr_normal2 fmt = function
  | NPi ("", i, a, b) -> fprintf fmt "@[<hov2>(%i : %a)@ -> %a@]" i pr_normal3 a pr_normal2 b
  | NPi (name, _, a, b) -> fprintf fmt "@[<hov2>(%s : %a)@ -> %a@]" name pr_normal3 a pr_normal2 b
  | v -> pr_normal3 fmt v
and pr_normal3 fmt = function
  | NSigma ("", i, a, b) -> fprintf fmt "@[<hov2>(%i : %a)@ * %a@]" i pr_normal4 a pr_normal3 b
  | NSigma (name, _, a, b) -> fprintf fmt "@[<hov2>(%s : %a)@ * %a@]" name pr_normal4 a pr_normal3 b
  | v -> pr_normal4 fmt v
and pr_normal4 fmt = function
  | NConstruct (c, (_::_ as l)) ->
      let rec pr_normals fmt = function
        | [] -> assert false
        | [v] -> pr_normal5 fmt v
        | v::tl ->
            fprintf fmt "@[<hov2>%a@ %a@]" pr_normal5 v pr_normals tl in
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

let print_constraints (m, c) =
  MM.iter (fun id typ -> Printf.printf "?%s : %s\n" (string_of_id id)
  (Print_value.string_of_value typ)) m;
  List.iter (function
    | (Active, x, y) -> Printf.printf "%s = %s\n" (string_of_normal x) (string_of_normal y)
    | (Failed, x, y) -> Printf.printf "F: %s = %s\n" (string_of_normal x) (string_of_normal y)) c

