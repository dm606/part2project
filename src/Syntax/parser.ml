open AbsConcrete
open LexConcrete
open ParConcrete

type expression_or_declaration =
  | Exp of exp
  | Decl of decl list

(* Creates a wrapper around lexfun which returns TOK_EOF after each
 * TOK_SEMISEMI, and raises End_of_file if lexfun returns TOK_EOF *)
let lexfun_repl lexfun =
  let return_eof = ref false in
  fun lexbuf ->
    if !return_eof then (
      return_eof := false;
      TOK_EOF)
    else
      let token = lexfun lexbuf in (
      (match token with
       | TOK_SEMISEMI _ -> return_eof := true
       | TOK_EOF -> raise End_of_file
       | _ -> ()) ;
      token)

(* Parses declarations and expressions from a lexbuf; raises End_of_file on
 * TOK_EOF *)
let parse_repl lexbuf = 
  match pReplStructure (lexfun_repl token) lexbuf with
  | ReplExpression (e, _) -> [Exp e]
  | ReplDeclarations (d, _) ->
      let rec to_list = function
        | LLDEmpty -> []
        | LLDCons (l, d) -> (Decl l) :: (to_list d) in
      to_list d

(* Parses the contents of a file *)
let parse_file lexbuf =
  let rec to_list = function
    | FileTailEnd -> []
    | FileTailEnd2 _ -> []
    | FileTailDeclaration (d, t) -> (Decl d) :: (to_list t)
    | FileTailDeclaration2 (_, d, t) -> (Decl d) :: (to_list t)
    | FileTailExpression (_, e, t) -> (Exp e) :: (to_list t) in
  match pFileStructure token lexbuf with
  | FileExpression (e, t) -> (Exp e) :: (to_list t)
  | FileTail t -> to_list t
