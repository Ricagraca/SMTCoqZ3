

(* File calc.ml *)
let _ =
  try
    let lexbuf = Lexing.from_channel stdin in
    while true do
      let result = Z3Parser.line Z3Lexer.token lexbuf in
      print_newline(); flush stdout
    done
  with Z3Lexer.Eof ->
    exit 0
