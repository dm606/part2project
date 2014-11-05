open Lexing
open AbsConcrete
open Parser

let showTree (t : AbsConcrete.replInput) : string =
      "[Abstract syntax]\n\n"^
         (fun x -> ShowConcrete.show (ShowConcrete.showReplInput x)) t^
        "\n\n"^ "[Linearized tree]\n\n"^
        PrintConcrete.printTree PrintConcrete.prtReplInput t^ "\n"
;;


let rec mainloop lexbuf =
  try
    (match parse_repl lexbuf with
     | ReplExpression (e, f) -> (
       print_endline "Got expression";
       print_endline (showTree (ReplExpression (e, f))))
     | ReplDeclaration (d, f) -> (
       print_endline "Got declaration";
       print_endline (showTree (ReplDeclaration (d, f)))));
    mainloop lexbuf
  with
  | End_of_file -> print_endline "Got end of file"
  
let _ =
  mainloop (from_channel stdin)
