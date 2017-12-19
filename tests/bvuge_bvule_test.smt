(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 8))

(assert (and (bvuge a (_ bv1 8)) (bvule a (_ bv1 8))))

(check-sat)
(get-model)

