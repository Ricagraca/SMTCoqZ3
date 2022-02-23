ocamllex z3Lexer.mll       # generates lexer.ml
        ocamlyacc z3Parser.mly     # generates parser.ml and parser.mli
        ocamlc -c z3Parser.mli
        ocamlc -c z3Lexer.ml
        ocamlc -c z3Parser.ml
        ocamlc -c example.ml
        ocamlc -o main z3Lexer.cmo z3Parser.cmo example.cmo
