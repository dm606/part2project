open Lexing
open List

open AbsConcrete
open Parser
open Abstract

let rec listlistdeclaration_to_list = function
  | LLDEmpty -> []
  | LLDCons (d, l) -> d :: listlistdeclaration_to_list l

let rec listlistdeclaration_from_list = function
  | [] -> LLDEmpty
  | d::ds -> LLDCons (d, listlistdeclaration_from_list ds)

let rec mainloop lexbuf =
  try
    (match parse_repl lexbuf with
     | ReplExpression (e, s) ->
         print_endline (PrintConcrete.printTree PrintConcrete.prtReplStructure
           (ReplExpression ((resugar_expression (desugar_expression e)), s)))
     | ReplDeclarations (l, s) ->
         print_endline (PrintConcrete.printTree PrintConcrete.prtReplStructure
           (ReplDeclarations (listlistdeclaration_from_list (map (fun d -> map
           (fun d -> resugar_declaration (desugar_declaration d)) d)
           (listlistdeclaration_to_list l)), s))));
    mainloop lexbuf
  with
  | End_of_file -> print_endline "Got end of file"
  
let _ =
  for i = 1 to Array.length Sys.argv - 1 do
    let file = open_in Sys.argv.(1) in
    try
      mainloop (from_channel file);
      close_in file
    with
    | e -> close_in_noerr file; raise e
  done;

  mainloop (from_channel stdin)
