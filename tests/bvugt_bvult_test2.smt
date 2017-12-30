(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 8))

(assert (and (bvugt a (_ bv1 8)) (bvult a (_ bv9 8))))

;(get-all-models)
(count-models)

