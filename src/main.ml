open Lexing
open List

open AbsConcrete
open Parser
open Abstract

let rec handle_input =
  let handle = function
  | Exp e ->
      print_endline (PrintConcrete.printTree PrintConcrete.prtReplStructure
        (ReplExpression ((resugar_expression (desugar_expression e))
      , SEMISEMI ";;")))
  | Decl d ->
      print_endline (PrintConcrete.printTree PrintConcrete.prtReplStructure
        (ReplDeclarations (LLDCons (map (
          fun d -> resugar_declaration (desugar_declaration d)) d, LLDEmpty),
          SEMISEMI ";;"))) in
  iter handle 

let rec mainloop lexbuf =
  try
    let i = parse_repl lexbuf in
    print_endline (string_of_int (length i));
    handle_input i;
    mainloop lexbuf
  with
  | End_of_file -> print_endline "Got end of file"
  
let _ =
  for i = 1 to Array.length Sys.argv - 1 do
    let file = open_in Sys.argv.(1) in
    try
      handle_input (parse_file (from_channel file));
      close_in file
    with
    | e -> close_in_noerr file; raise e
  done;

  mainloop (from_channel stdin)
