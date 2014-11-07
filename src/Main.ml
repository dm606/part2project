open Lexing

open AbsConcrete
open Parser
open Abstract

let showTree (t : AbsConcrete.replInput) : string =
      "[Abstract syntax]\n\n"^
         (fun x -> ShowConcrete.show (ShowConcrete.showReplInput x)) t^
        "\n\n"^ "[Linearized tree]\n\n"^
        PrintConcrete.printTree PrintConcrete.prtReplInput t^ "\n"
;;


let rec mainloop lexbuf =
  try
    print_endline (showTree (resugar (desugar (parse_repl (lexbuf)))));
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
