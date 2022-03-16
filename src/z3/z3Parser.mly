  %{
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

open SmtBtype
open SmtAtom
open SmtForm
open VeritSyntax
open Printf  


let parse_bv s =
  let l = ref [] in
  for i = 2 to String.length s - 1 do
    match s.[i] with
    | '0' -> l := false :: !l
    | '1' -> l := true :: !l
    | _ -> assert false
  done;
  !l

    %}


  /*
définition des lexèmes
  */


  %token EOF EOL
  %token LPAR RPAR COLON
  %token PROOF SETLOGIC
  %token MP ASSERTED REWRITE
  %token NOT TRUE FALSE EQUAL 
  %token <string>VAR
  %token QFUF

  /* type de "retour" du parseur : une clause */
      %type <unit> line
	/*
      %type <Z3Syntax.atom_form_lit> term
	%start term
	*/
      %start line

	%%

      line:
    | LPAR setlogic proof RPAR EOL {}
    | LPAR setlogic proof RPAR EOF {};

      setlogic:
    | LPAR SETLOGIC logic RPAR { printf ("set-logic ");};


      logic:
    | QFUF { printf ("QF_UF "); };
      
      proof:
    | LPAR PROOF rule_list RPAR { printf ("proof "); ZProof  };

      rule_list:
    | LPAR typ term_list RPAR { ZRule $2 $3 }

      term_list:
    | term           { [$1] }
    | term_list term { $2::$1 };
	
      term:
    | rule_list      {  }
    | LPAR term RPAR {  }
    | TRUE           { printf ("true "); ZTrue }
    | FALSE          { printf ("false "); ZFalse }
    | EQUAL term term {  printf ("equal "); ZEqual $2 $3 }
    | NOT term {  printf ("not "); ZNot $2 }
    | VAR            {  };
      

      typ:
    | MP             {printf ("mp "); ZMp }
    | ASSERTED       {printf ("asserted "); ZAsserted }
    | REWRITE        {printf ("rewrite "); ZRewrite };
      


      
      
