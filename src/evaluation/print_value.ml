open Format

open Value

(* the following functions are numbered according to the precedence of the
 * values which they print *)
let rec pr_neutral fmt = function
  | v -> pr_neutral4 fmt v
and pr_neutral4 fmt = function
  | VApplication (n, v) ->
      fprintf fmt "@[<hov2>%a@ %a@]" pr_neutral4 n pr_value5 v
  | VFunctionApplication (_, _, n) ->
      fprintf fmt "@[<hov2>%s@ %a@]" "<function>" pr_neutral5 n
  | v -> pr_neutral5 fmt v
and pr_neutral5 fmt = function
  | VProj1 v -> fprintf fmt "%a.1" pr_neutral5 v
  | VProj2 v -> fprintf fmt "%a.2" pr_neutral5 v
  | VVar i -> fprintf fmt "%i" i
  | v -> fprintf fmt "(%a)" pr_neutral v

and pr_value fmt = function
  | VPair (v1, v2) -> fprintf fmt "@[<hov2>%a,@ %a@]" pr_value3 v1 pr_value v2
  | v -> pr_value1 fmt v
and pr_value1 fmt = function
  | VLambda (_, _, _) -> fprintf fmt "<fun>"
  | VFunction (_, _) -> fprintf fmt "<function>"
  | v -> pr_value2 fmt v
and pr_value2 fmt = function
  | VPi (_, _, _, _) -> fprintf fmt "<pi>"
  | v -> pr_value3 fmt v
and pr_value3 fmt = function
  | VSigma (_, _, _, _) -> fprintf fmt "<sigma>"
  | v -> pr_value4 fmt v
and pr_value4 fmt = function
  | VConstruct (c, (_::_ as l)) ->
      let rec pr_values fmt = function
        | [] -> assert false
        | [v] -> pr_value5 fmt v
        | v::tl ->
            fprintf fmt "@[<hov2>%a@ %a@]" pr_value5 v pr_values tl in
      fprintf fmt "@[%s@ %a@]" c pr_values (List.rev l)
  | v -> pr_value5 fmt v
and pr_value5 fmt = function
  | VConstruct (c, []) -> fprintf fmt "%s" c
  | VUniverse -> fprintf fmt "U"
  | VUnitType -> fprintf fmt "Unit"
  | VUnit -> fprintf fmt "()"
  | VNeutral n -> fprintf fmt "[%a]" pr_neutral n
  | v -> fprintf fmt "(%a)" pr_value v

let print_value v = pr_value std_formatter v; print_newline ()
let string_of_value v =
  Buffer.clear stdbuf;
  pr_value str_formatter v;
  pp_print_flush str_formatter ();
  Buffer.contents stdbuf
