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


VERNAC COMMAND EXTEND Vernac_zchaff
| [ "Parse_certif_zchaff" 
    ident(dimacs) ident(trace) string(fdimacs) string(fproof) ] ->
  [
    Zchaff.parse_certif dimacs trace fdimacs fproof
  ]
| [ "Zchaff_Checker" string(fdimacs) string(fproof) ] ->
  [
    Zchaff.checker fdimacs fproof
  ]
| [ "Zchaff_Theorem" ident(name) string(fdimacs) string(fproof) ] ->
  [
    Zchaff.theorem name fdimacs fproof
  ]
END

VERNAC COMMAND EXTEND Vernac_zchaff_abs
| [ "Zchaff_Theorem_Abs" ident(name) string(fdimacs) string(fproof) ] ->
  [
    Zchaff.theorem_abs name fdimacs fproof
  ]
END

VERNAC COMMAND EXTEND Vernac_verit
| [ "Parse_certif_verit"
    ident(t_i) ident(t_func) ident(t_atom) ident(t_form) ident(root) ident(used_roots) ident(trace) string(fsmt) string(fproof) ] ->
  [
    Verit.parse_certif t_i t_func t_atom t_form root used_roots trace fsmt fproof
  ]
| [ "Verit_Checker" string(fsmt) string(fproof) ] ->
  [
    Verit.checker fsmt fproof
  ]
| [ "Verit_Checker_Debug" string(fsmt) string(fproof) ] ->
  [
    Verit.checker_debug fsmt fproof
  ]
| [ "Verit_Theorem" ident(name) string(fsmt) string(fproof) ] ->
  [
    Verit.theorem name fsmt fproof
  ]
END

VERNAC COMMAND EXTEND Vernac_z3
| [ "Parse_certif_z3"
    ident(t_i) ident(t_func) ident(t_atom) ident(t_form) ident(root) ident(used_roots) ident(trace) string(fsmt) string(fproof) ] ->
  [
    Z3.parse_certif t_i t_func t_atom t_form root used_roots trace fsmt fproof
  ]
| [ "Z3_Checker" string(fsmt) string(fproof) ] ->
  [
    Z3.checker fsmt fproof
  ]
| [ "Z3_Checker_Debug" string(fsmt) string(fproof) ] ->
  [
    Z3.checker_debug fsmt fproof
  ]
| [ "Z3_Theorem" ident(name) string(fsmt) string(fproof) ] ->
  [
    Z3.theorem name fsmt fproof
  ]
END

VERNAC COMMAND EXTEND Vernac_lfsc
| [ "Parse_certif_lfsc"
    ident(t_i) ident(t_func) ident(t_atom) ident(t_form) ident(root) ident(used_roots) ident(trace) string(fsmt) string(fproof) ] ->
  [
    Lfsc.parse_certif t_i t_func t_atom t_form root used_roots trace fsmt fproof
  ]
| [ "Lfsc_Checker" string(fsmt) string(fproof) ] ->
  [
    Lfsc.checker fsmt fproof
  ]
| [ "Lfsc_Checker_Debug" string(fsmt) string(fproof) ] ->
  [
    Lfsc.checker_debug fsmt fproof
  ]
| [ "Lfsc_Theorem" ident(name) string(fsmt) string(fproof) ] ->
  [
    Lfsc.theorem name fsmt fproof
  ]
END

TACTIC EXTEND Tactic_zchaff
| [ "zchaff_bool" ] -> [ Zchaff.tactic () ]
| [ "zchaff_bool_no_check" ] -> [ Zchaff.tactic_no_check () ]
END

let lemmas_list = ref []

VERNAC COMMAND EXTEND Add_lemma
| [ "Add_lemmas" constr_list(lems) ] -> [ lemmas_list := lems @ !lemmas_list ]
| [ "Clear_lemmas" ] -> [ lemmas_list := [] ]
END


let error () = Structures.error "Tactics are not supported with native-coq"

TACTIC EXTEND Tactic_verit
| [ "verit_bool_base" constr_list(lpl) ] -> [ error () ]
| [ "verit_bool_no_check_base" constr_list(lpl) ] -> [ error () ]
END

TACTIC EXTEND Tactic_z3
| [ "z3_bool_base" constr_list(lpl) ] -> [ error () ]
| [ "z3_bool_no_check_base" constr_list(lpl) ] -> [ error () ]
END

TACTIC EXTEND Tactic_cvc4
| [ "cvc4_bool" ] -> [ error () ]
| [ "cvc4_bool_no_check" ] -> [ error () ]
END
