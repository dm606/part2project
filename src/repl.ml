open Lexing
open Parsing
open Printf

open AbsConcrete
open Abstract
open Equality

module SS = Set.Make(String)

exception Unknown_command of string
exception Declaration_type of Checker.typing_result

(* names of declared constants *)
let declared = ref empty_env 

(* list of all declared values *)
let env = ref Environment.empty

(* typing context *)
let context = ref Context.empty

let prompt = ref ""

let rec read_into_buffer index buffer length = 
  if !prompt <> "" then (print_string !prompt; flush stdout);

  let c = input_char stdin in
  Bytes.set buffer index c;
  if c = '\n' then prompt := "  " else prompt := "";
  if c = '\n' && index > 0 then index + 1
  else if index = length - 1 then length
  else read_into_buffer (index + 1) buffer length

let stdin_lexbuf = from_function (read_into_buffer 0)

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

let end_parse lexbuf =
  flush stdout;
  flush stderr;
  flush_input lexbuf;
  reset_position lexbuf lexbuf.lex_start_p.pos_fname;
  clear_parser ()

let parse_single_expression lexbuf = 
  let return_value = match Parser.parse_repl lexbuf with
    | (Parser.Exp e)::_ -> Some e
    | _ -> fprintf stderr "An expression was expected\n"; None
    | exception BNFC_Util.Parse_error (s, e) ->
      fprintf stderr "%s: parse error \n" (format_position s e); None in
  end_parse lexbuf;
  return_value

let print_typing_result r =
  (* TODO: only print the error here *)
  Checker.print_error stderr r;
  Checker.print_trace stderr r

let handle_are_equal () =
  print_string "Expression 1:";
  match parse_single_expression stdin_lexbuf with
  | None -> ()
  | Some e1 -> (
      let e1 = desugar_expression !declared e1 in
      print_string "Expression 2:";
      match parse_single_expression stdin_lexbuf with
      | None -> ()
      | Some e2 ->
          let e2 = desugar_expression !declared e2 in
          if Equality.are_equal !env e1 e2
          then print_endline "Expressions are equal"
          else print_endline "Expressions are not equal")

let handle_infer_type () =
  print_string "Expression: ";
  match parse_single_expression stdin_lexbuf with
  | None -> ()
  | Some exp ->
    let desugared = desugar_expression !declared exp in
    let result = Checker.infer_type !env !context desugared in
    if Checker.succeeded result
    then Print_value.print_value (Checker.get_type result)
    else print_typing_result result

let remove_types context = List.fold_left (fun c -> function 
  | Type (x, _, _, _) -> Context.remove_constructors_of_type c x
  | _ -> c) context

let add_declarations_to_context context d =
  let result = Checker.check_declarations !env context d in
  if Checker.succeeded result then
    let context = remove_types context d in
    let context = List.fold_right
                    (fun (s, v) c -> Context.add_binder c s v)
                    (Checker.get_binder_types result) context in
    let constructor_types = Checker.get_constructor_types result in
    (* the order of constructors does not matter -- use fold_left for
     * efficiency *)
    List.fold_left
      (fun c (s, type_name, v) -> Context.add_constructor c s type_name v)
      context constructor_types
  else raise (Declaration_type result)

let rec use_file filename =
  let file = open_in filename in
  try
    let lexbuf = from_channel file in
    reset_position lexbuf filename;
    parse Parser.parse_file lexbuf;
    close_in file
  with
  | e -> close_in_noerr file; raise e
and handle_command c =
  match c with
  | CommandString (Ident "use", arg) -> use_file arg
  | CommandString (Ident s, _) -> raise (Unknown_command s)
  | CommandNone (Ident "areequal") -> handle_are_equal ()
  | CommandNone (Ident "infertype") -> handle_infer_type ()
  | CommandNone (Ident s) -> raise (Unknown_command s)
and parse f lexbuf = (
  try Lazy.force (handle_input (f lexbuf)) with
  | BNFC_Util.Parse_error (s, e) -> 
      fprintf stderr "%s: parse error \n" (format_position s e)
  | Abstract.Constructor_not_defined s ->
      fprintf stderr "\"%s\" is not bound to anything\n" s
  | Eval.Cannot_evaluate s -> fprintf stderr "Can't evaluate expression: %s\n" s
  | Declaration_type result -> print_typing_result result
  | Failure s -> fprintf stderr "%s\n" s
  | Unknown_command s -> fprintf stderr "Unknown command: \"%s\"\n" s);
  end_parse lexbuf
(* Lazy to stop the compiler from complaining about the Comm c case *)
and handle_input l = lazy ( 
  let handle = function
    | Parser.Exp e ->
        let exp = desugar_expression !declared e in
        let typing_result = Checker.infer_type !env !context exp in
        if Checker.succeeded typing_result then (
          let evaluated = Eval.eval !env exp in
          Print_value.print_value evaluated)
        else print_typing_result typing_result
    | Parser.Decl d ->
        let new_declared = add_all_declaration_binders !declared d in
        let decl = desugar_declarations !declared d in
        let new_context = add_declarations_to_context !context decl in
        let new_env = Environment.add_declarations !env decl in
        print_endline (print_declarations !declared decl);
        declared := new_declared;
        env := new_env;
        context := new_context
    | Parser.Comm c -> handle_command c in
  List.iter handle l)

let rec repl lexbuf =
  try
    (* evaluating an expression will generally leave a lot of unreachable data,
     * and a pause is probably acceptable here, so do a full garbage collection
     * cycle here *)
    Gc.full_major ();

    prompt := "# ";
    parse Parser.parse_repl lexbuf;
    repl lexbuf
  with
  | End_of_file -> print_newline () 
  | Sys.Break -> print_newline (); repl lexbuf (* handle sigint *)

let () =
  if not !Sys.interactive then (
    (* Do not terminate the program on sigint: instead raise Sys.Break *)
    Sys.catch_break true;

    for i = 1 to Array.length Sys.argv - 1 do
      use_file Sys.argv.(1)
    done;

    repl stdin_lexbuf)


