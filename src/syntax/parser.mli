open AbsConcrete

type input_part =
  | Exp of exp 
  | Decl of decl list
  | Comm of command

val lexfun_repl : ('a -> ParConcrete.token) -> 'a -> ParConcrete.token
val parse_repl : Lexing.lexbuf -> input_part list
val parse_file : Lexing.lexbuf -> input_part list
