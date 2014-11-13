open Lexing
open List

open AbsConcrete
open Parser
open Abstract

exception Unknown_command

let rec use_file filename =
  let file = open_in filename in
    try
      Lazy.force (handle_input (parse_file (from_channel file)));
      close_in file
    with
    | e -> close_in_noerr file; raise e
and handle_command c =
  match c with
  | CommandString (Ident "use", arg) -> use_file arg
  | _ -> raise Unknown_command
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

let rec mainloop lexbuf =
  try
    Lazy.force (handle_input (parse_repl lexbuf));
    mainloop lexbuf
  with
  | End_of_file -> print_endline "Got end of file"
  
let () =
  for i = 1 to Array.length Sys.argv - 1 do
   use_file Sys.argv.(1)
  done;

  mainloop (from_channel stdin)
