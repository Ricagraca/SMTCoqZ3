type token =
  | EOF
  | EOL
  | LPAR
  | RPAR
  | COLON
  | PROOF
  | SETLOGIC
  | MP
  | ASSERTED
  | REWRITE
  | NOT
  | TRUE
  | FALSE
  | EQUAL
  | VAR of (string)
  | QFUF

val line :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> unit
