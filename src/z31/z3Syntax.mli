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


open SmtAtom

exception Sat

type typ = Proof | Mp | Setlogic | Asserted | Rewrite | Qf

val get_clause : int -> SmtAtom.Form.t SmtCertif.clause
val add_clause : int -> SmtAtom.Form.t SmtCertif.clause -> unit

val add_ref : int -> int -> unit
val get_ref : int -> int
val to_add : (int * SmtAtom.Form.t list) list ref

val mk_clause : SmtCertif.clause_id * typ * SmtAtom.Form.t list * SmtCertif.clause_id list -> SmtCertif.clause_id

val apply_dec_atom : (?declare:bool -> SmtAtom.hatom -> SmtAtom.hatom) ->
                     bool * Form.atom_form_lit -> bool * Form.atom_form_lit
val apply_bdec_atom :
  (?declare:bool -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t) ->
  bool * Form.atom_form_lit -> bool * Form.atom_form_lit -> bool * Form.atom_form_lit
val apply_tdec_atom :
  (?declare:bool -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t) ->
  bool * Form.atom_form_lit -> bool * Form.atom_form_lit -> bool * Form.atom_form_lit -> bool * Form.atom_form_lit

val apply_dec : ('a -> 'b) -> bool * 'a -> bool * 'b
val list_dec : (bool * 'a) list -> bool * 'a list


val get_solver : int -> bool * Form.atom_form_lit
val add_solver : int -> bool * Form.atom_form_lit -> unit

val find_opt_qvar : string -> SmtBtype.btype option 
val add_qvar : string -> SmtBtype.btype -> unit
val clear_qvar : unit -> unit

val init_index : SmtAtom.Form.t list -> (SmtAtom.Form.t -> SmtAtom.Form.t) ->
                 SmtAtom.Form.t -> int

val qf_to_add : SmtAtom.Form.t SmtCertif.clause list -> (SmtAtom.Form.t SmtCertif.clause_kind * SmtAtom.Form.t list option * SmtAtom.Form.t SmtCertif.clause) list

val ra : SmtAtom.Atom.reify_tbl
val rf : SmtAtom.Form.reify
val ra_quant : SmtAtom.Atom.reify_tbl
val rf_quant : SmtAtom.Form.reify

val hlets : (string, Form.atom_form_lit) Hashtbl.t

val clear : unit -> unit
