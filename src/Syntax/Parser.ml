open LexConcrete
open ParConcrete

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

(* Parses a single declaration or expression from a lexbuf; raises End_of_file
 * on TOK_EOF *)
let parse_repl = pReplInput (lexfun_repl token)
