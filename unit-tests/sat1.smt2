(set-option :produce-proofs true)
(set-logic QF_UF)
(declare-fun a () Bool)
(assert (and a (not a)))
(check-sat)
(get-proof)
(exit)
