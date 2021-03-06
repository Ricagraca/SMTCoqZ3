{
(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


  open Z3Parser
  exception Eof

  let typ_table = Hashtbl.create 53
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add typ_table kwd tok)
      [
        "proof", PROOF;
        "true", TRUE;
        "false", FALSE;
        "not", NOT;
        "proof", PROOF;
        "asserted", ASSERTED;
        "rewrite", REWRITE;
        "set-logic", SETLOGIC;
        "mp", MP;
        "QF_UF", QFUF;
      ]
}


let digit = [ '0'-'9' ]
let bit = [ '0'-'1' ]
let bitvector = '#' 'b' bit+
let alpha = [ 'a'-'z' 'A' - 'Z' ]
let blank = [' ' '\t']
let newline = ['\n' '\r']
let var = alpha (alpha|digit|'_'|'-')*
let atvar = '@' var
let bindvar = '?' var+
let int = '-'? digit+


rule token = parse
  | blank +                    { token lexbuf }
  | newline +                  { token lexbuf }

  | ":"                        { COLON }
(*  | "#" (int as i)             { SHARPINT (int_of_string i) } *)

  | "("                        { LPAR }
  | ")"                        { RPAR }

(*  | "["                        { LBRACKET }
  | "]"                        { RBRACKET } *)

  | "="                        { EQUAL }
(*  | "<"                        { LT }
  | "<="                       { LEQ }
  | ">"                        { GT }
  | ">="                       { GEQ }
  | "+"                        { PLUS }
  | "-"                        { MINUS }
  | "~"                        { OPP }
  | "*"                        { MULT }
  | "=>"                       { IMP }

  | "Formula is Satisfiable"   { SAT }

  | "Tindex_" (int as i)       { TINDEX (int_of_string i) }
  | "Int"     	      	       { TINT }
  | "Bool"		       { TBOOL }
  | (int as i)                 { try INT (int_of_string i)
	                         with _ ->
                                   BIGINT (Big_int.big_int_of_string i) }
  | bitvector as bv            { BITV bv } *)
  | var                        { let v = Lexing.lexeme lexbuf in
                                 try Hashtbl.find typ_table v with
                                   | Not_found -> VAR v }
(*  | bindvar as v               { BINDVAR v }

  | atvar 		       { ATVAR (Lexing.lexeme lexbuf) } *)

  | eof                        { raise Eof }
