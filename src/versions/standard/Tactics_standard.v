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


Require Import PropToBool.
Require Import Int63 List PArray Bool ZArith.
Require Import SMTCoq.State SMTCoq.SMT_terms SMTCoq.Trace SMT_classes_instances QInst.

Declare ML Module "smtcoq_plugin".


(** Collect all the hypotheses from the context *)

Ltac get_hyps_acc acc :=
  match goal with
  | [ H : ?P |- _ ] =>
    let T := type of P in
    lazymatch T with
    | Prop =>
      lazymatch P with
      | id _ => fail
      | _ =>
        let _ := match goal with _ => change P with (id P) in H end in
        match acc with
        | Some ?t => get_hyps_acc (Some (H, t))
        | None => get_hyps_acc (Some H)
        end
      end
    | _ => fail
    end
  | _ => acc
  end.

Ltac eliminate_id :=
  repeat match goal with
  | [ H : ?P |- _ ] =>
    lazymatch P with
    | id ?Q => change P with Q in H
    | _ => fail
    end
  end.

Ltac get_hyps :=
  let Hs := get_hyps_acc (@None nat) in
  let _ := match goal with _ => eliminate_id end in
  Hs.


(* Section Test. *)
(*   Variable A : Type. *)
(*   Hypothesis H1 : forall a:A, a = a. *)
(*   Variable n : Z. *)
(*   Hypothesis H2 : n = 17%Z. *)

(*   Goal True. *)
(*   Proof. *)
(*     let Hs := get_hyps in idtac Hs. *)
(*   Abort. *)
(* End Test. *)


(** Tactics in bool *)

Tactic Notation "verit_bool_base_auto" constr(h) := verit_bool_base h; try (exact _).
Tactic Notation "verit_bool_no_check_base_auto" constr(h) := verit_bool_no_check_base h; try (exact _).

Tactic Notation "verit_bool" constr(h) :=
  let Hs := get_hyps in
  match Hs with
  | Some ?Hs => verit_bool_base_auto (Some (h, Hs))
  | None => verit_bool_base_auto (Some h)
  end;
  vauto.
Tactic Notation "verit_bool"           :=
  let Hs := get_hyps in
  verit_bool_base_auto Hs; vauto.

Tactic Notation "verit_bool_no_check" constr(h) :=
  let Hs := get_hyps in
  match Hs with
  | Some ?Hs => verit_bool_no_check_base_auto (Some (h, Hs))
  | None => verit_bool_no_check_base_auto (Some h)
  end;
  vauto.
Tactic Notation "verit_bool_no_check"           :=
  let Hs := get_hyps in
  fun Hs => verit_bool_no_check_base_auto Hs; vauto.


Tactic Notation "z3_bool_base_auto" constr(h) := z3_bool_base h; try (exact _).
Tactic Notation "z3_bool_no_check_base_auto" constr(h) := z3_bool_no_check_base h; try (exact _).
(** Tactics in Prop **)

Ltac zchaff          := prop2bool; zchaff_bool; bool2prop.
Ltac zchaff_no_check := prop2bool; zchaff_bool_no_check; bool2prop.

Tactic Notation "z3" constr(h) :=
  prop2bool;
  [ .. | prop2bool_hyps h;
         [ .. | let Hs := get_hyps in
                match Hs with
                | Some ?Hs =>
                  prop2bool_hyps Hs;
                  [ .. | z3_bool_base_auto (Some (h, Hs)) ]
                | None => z3_bool_base_auto (Some h)
                end; vauto
         ]
  ].
Tactic Notation "z3"           :=
  prop2bool;
  [ .. | let Hs := get_hyps in
         match Hs with
         | Some ?Hs =>
           prop2bool_hyps Hs;
           [ .. | z3_bool_base_auto (Some Hs) ]
         | None => z3_bool_base_auto (@None nat)
         end; vauto
  ].
Tactic Notation "verit" constr(h) :=
  prop2bool;
  [ .. | prop2bool_hyps h;
         [ .. | let Hs := get_hyps in
                match Hs with
                | Some ?Hs =>
                  prop2bool_hyps Hs;
                  [ .. | verit_bool_base_auto (Some (h, Hs)) ]
                | None => verit_bool_base_auto (Some h)
                end; vauto
         ]
  ].
Tactic Notation "verit"           :=
  prop2bool;
  [ .. | let Hs := get_hyps in
         match Hs with
         | Some ?Hs =>
           prop2bool_hyps Hs;
           [ .. | verit_bool_base_auto (Some Hs) ]
         | None => verit_bool_base_auto (@None nat)
         end; vauto
  ].
Tactic Notation "verit_no_check" constr(h) :=
  prop2bool;
  [ .. | prop2bool_hyps h;
         [ .. | let Hs := get_hyps in
                match Hs with
                | Some ?Hs =>
                  prop2bool_hyps Hs;
                  [ .. | verit_bool_no_check_base_auto (Some (h, Hs)) ]
                | None => verit_bool_no_check_base_auto (Some h)
                end; vauto
         ]
  ].
Tactic Notation "verit_no_check"           :=
  prop2bool;
  [ .. | let Hs := get_hyps in
         match Hs with
         | Some ?Hs =>
           prop2bool_hyps Hs;
           [ .. | verit_bool_no_check_base_auto (Some Hs) ]
         | None => verit_bool_no_check_base_auto (@None nat)
         end; vauto
  ].

Ltac cvc4            := prop2bool; [ .. | cvc4_bool; bool2prop ].
Ltac cvc4_no_check   := prop2bool; [ .. | cvc4_bool_no_check; bool2prop ].

Tactic Notation "smt" constr(h) := (prop2bool; [ .. | try verit h; cvc4_bool; try verit h; bool2prop ]).
Tactic Notation "smt"           := (prop2bool; [ .. | try verit  ; cvc4_bool; try verit  ; bool2prop ]).
Tactic Notation "smt_no_check" constr(h) := (prop2bool; [ .. | try verit_no_check h; cvc4_bool_no_check; try verit_no_check h; bool2prop]).
Tactic Notation "smt_no_check"           := (prop2bool; [ .. | try verit_no_check  ; cvc4_bool_no_check; try verit_no_check  ; bool2prop]).



(* 
   Local Variables:
   coq-load-path: ((rec "." "SMTCoq"))
   End: 
*)
