open Bytes 
open Lexing
open List
open Parsing
open Printf

open AbsConcrete
open Abstract
open BNFC_Util
open Parser

exception Unknown_command of string

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
        print_endline (PrintConcrete.printTree PrintConcrete.prtReplStructure
          (ReplExpression ((resugar_expression (desugar_expression e))
        , SEMISEMI ";;")))
    | Decl d ->
        print_endline (PrintConcrete.printTree PrintConcrete.prtReplStructure
          (ReplDeclarations (LLDCons (map (
            fun d -> resugar_declaration (desugar_declaration d)) d, LLDEmpty),
            SEMISEMI ";;")))
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
  | End_of_file -> () 

let rec read_into_buffer index buffer length = (
  if !prompt <> "" then (print_string !prompt; flush stdout);

  let c = input_char stdin in
  set buffer index c;
  if c = '\n' then prompt := "  " else prompt := "";
  if c = '\n' && index > 0 then index + 1
  else if index = length - 1 then length
  else read_into_buffer (index + 1) buffer length)

let () =
  for i = 1 to Array.length Sys.argv - 1 do
   use_file Sys.argv.(1)
  done;

  repl (from_function (read_into_buffer 0))
