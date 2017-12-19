(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 32))

(assert (= (bvneg a) a))
(assert (not (= a #x00000000)))

(check-sat)
(get-model)

