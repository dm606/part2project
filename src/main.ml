open Bytes 
open Lexing
open List
open Parsing
open Printf

open AbsConcrete
open Abstract
open BNFC_Util
open Eval
open Parser
open Value

exception Unknown_command of string

(* names of declared constants *)
let declared = ref ([], [])

(* list of all declared values *)
let env = ref []

let format_position s e =
  let sc = s.pos_cnum - s.pos_bol in
  let ec = e.pos_cnum - e.pos_bol in
  s.pos_fname ^ ":"
  ^ (if s.pos_lnum = e.pos_lnum then (string_of_int s.pos_lnum)
     else (string_of_int s.pos_lnum ^ "-" ^ string_of_int e.pos_lnum)) ^ ":"
  ^ (if sc = ec then string_of_int sc
     else string_of_int sc ^ "-" ^ string_of_int ec)

let reset_position lexbuf filename =
  lexbuf.lex_curr_p <- {
    pos_fname = filename;
    pos_lnum = 1;
    pos_cnum = 0;
    pos_bol = 0
  }

let name_counts = Hashtbl.create 256

let get_binder_name x = 
  try
    let c = Hashtbl.find name_counts x + 1 in
    Hashtbl.replace name_counts x c;
    x ^ string_of_int c
  with Not_found -> Hashtbl.add name_counts x 0; x

let rec rename_binders = function
  | PatternPair (p1, p2) -> PatternPair (rename_binders p1, rename_binders p2)
  | PatternApplication (x, l) -> PatternApplication (x, map rename_binders l)
  | PatternBinder x -> PatternBinder (get_binder_name x)
  | PatternUnderscore -> PatternUnderscore

let rec perform_substitutions nesting_level env = function
  | Pair (p1, p2) ->
      Pair (perform_substitutions nesting_level env p1
          , perform_substitutions nesting_level env p2)
  | Lambda (Underscore, e) ->
      Lambda (Underscore, perform_substitutions nesting_level env e)
  | Lambda (Name x, e) ->
      Lambda (Name (get_binder_name x)
            , perform_substitutions (nesting_level + 1) env e)
  | Pi (Underscore, e1, e2) ->
      Pi (Underscore, perform_substitutions nesting_level env e1
        , perform_substitutions nesting_level env e2)
  | Pi (Name x, e1, e2) ->
      Pi (Name (get_binder_name x), perform_substitutions nesting_level env e1
        , perform_substitutions (nesting_level + 1) env e2)
  | Sigma (Underscore, e1, e2) ->
      Sigma (Underscore, perform_substitutions nesting_level env e1
                      , perform_substitutions nesting_level env e2)
  | Sigma (Name x, e1, e2) ->
      Sigma (Name (get_binder_name x)
           , perform_substitutions nesting_level env e1
           , perform_substitutions (nesting_level + 1) env e2)
  | Function l -> 
      Function (map (fun (p, e) ->
        (rename_binders p
       , perform_substitutions (nesting_level + count_pattern_binders p)
           env e)) l)
  | LocalDeclaration (l, e) ->
      let binder_count = count_declaration_binders l in
      let subst_decl = function
        | Let (x, e1, e2) ->
            Let (get_binder_name x
               , perform_substitutions (nesting_level + binder_count - 1) env e1
               , perform_substitutions (nesting_level + binder_count - 1) env e2
            )
        | LetRec (x, e1, e2) ->
            LetRec (get_binder_name x
                  , perform_substitutions (nesting_level + binder_count - 1)
                      env e1
                  , perform_substitutions (nesting_level + binder_count) env e2) 
        | Type (x, ps, e, cs) ->
           let nl, ps = fold_left (fun (nl, l) (b, e) ->
               match b with
               | Underscore -> (nl, (b, perform_substitutions nl env e)::l)
               | Name _ -> (nl + 1, (b, perform_substitutions nl env e)::l))
            (nesting_level + binder_count, []) ps in
           let cs =
             map (fun (x, e) -> (x, perform_substitutions nl env e)) cs in
           Type (get_binder_name x, ps, perform_substitutions nl env e, cs)
      in
      LocalDeclaration (map subst_decl l
                      , perform_substitutions (nesting_level + binder_count)
                          env e)
  | Application (e1, e2) ->
      Application (perform_substitutions nesting_level env e1
                 , perform_substitutions nesting_level env e2)
  | Index i when i >= nesting_level ->
      let v = match nth env (i - nesting_level) with
        | EnvValue v -> v
        | EnvThunk l -> Lazy.force l in
      get_printable_expression nesting_level v 
  | Index i as e -> e
  | Proj1 e -> Proj1 (perform_substitutions nesting_level env e)
  | Proj2 e -> Proj2 (perform_substitutions nesting_level env e)
  | x -> x
(* convert a value into an expression which can be printed *)
and get_printable_expression nesting_level = function
  | VPair (v1, v2) ->
      Pair (get_printable_expression nesting_level v1, get_printable_expression
      nesting_level v2)
  | VLambda (b, e, env) ->
      Lambda (b, perform_substitutions (nesting_level + 1) env e)
  | VPi (b, v, e, env) ->
      Pi (b, get_printable_expression nesting_level v, perform_substitutions
      (nesting_level + 1) env e)
  | VSigma (b, v, e, env) ->
      Sigma (b, get_printable_expression nesting_level v, perform_substitutions
      (nesting_level + 1) env e)
  | VFunction (l, env) -> 
      Function (map (fun (p, e) -> (p, perform_substitutions
        (nesting_level + count_pattern_binders p) env e)) l) 
  | VUniverse -> Universe
  | VUnitType -> UnitType
  | VUnit -> Unit
  | VConstruct (s, l) ->
      fold_right (fun v e -> Application (e, get_printable_expression
      nesting_level v))
        l (Constructor s)

let get_printable_expression = get_printable_expression 0

let rec use_file filename =
  let file = open_in filename in
  try
    let lexbuf = from_channel file in
    reset_position lexbuf filename;
    parse parse_file lexbuf;
    close_in file
  with
  | e -> close_in_noerr file; raise e
and handle_command c =
  match c with
  | CommandString (Ident "use", arg) -> use_file arg
  | CommandString (Ident s, _) -> raise (Unknown_command s)
and parse f lexbuf = (
  try Lazy.force (handle_input (f lexbuf)) with
  | Parse_error (s, e) -> 
      fprintf stderr "%s: parse error \n" (format_position s e)
  | Unknown_command s -> fprintf stderr "Unknown command: \"%s\"\n" s);
  flush stdout;
  flush stderr;
  flush_input lexbuf;
  reset_position lexbuf lexbuf.lex_start_p.pos_fname;
  clear_parser ()
(* Lazy to stop the compiler from complaining about the Comm c case *)
and handle_input l = lazy ( 
  let handle = function
    | Exp e ->
        let exp = desugar_expression !declared e in
        let evaluated = get_printable_expression (eval !env exp) in
        print_endline (PrintConcrete.printTree PrintConcrete.prtReplStructure
          (ReplExpression ((resugar_expression !declared evaluated)
        , SEMISEMI ";;")))
    | Decl d ->
        let new_declared = add_all_declaration_binders !declared d in
        let decl = desugar_declarations !declared d in
        let new_env = add_declarations !env decl in
        (* TODO: What should be printed here?? *)
        print_endline (PrintConcrete.printTree PrintConcrete.prtReplStructure
          (ReplDeclarations (LLDCons
            (resugar_declarations !declared decl, LLDEmpty), SEMISEMI ";;")));
        declared := new_declared;
        env := new_env
    | Comm c ->
        handle_command c in
  iter handle l)

let prompt = ref ""

let rec repl lexbuf =
  try
    prompt := "# ";
    parse parse_repl lexbuf;
    repl lexbuf
  with
  | End_of_file -> print_newline () 
  | Sys.Break -> print_newline (); repl lexbuf (* handle sigint *)

let rec read_into_buffer index buffer length = 
  if !prompt <> "" then (print_string !prompt; flush stdout);

  let c = input_char stdin in
  set buffer index c;
  if c = '\n' then prompt := "  " else prompt := "";
  if c = '\n' && index > 0 then index + 1
  else if index = length - 1 then length
  else read_into_buffer (index + 1) buffer length

let () =
  if not !Sys.interactive then (
    (* Do not terminate the program on sigint: instead raise Sys.Break *)
    Sys.catch_break true;

    for i = 1 to Array.length Sys.argv - 1 do
      use_file Sys.argv.(1)
    done;

    repl (from_function (read_into_buffer 0)))
