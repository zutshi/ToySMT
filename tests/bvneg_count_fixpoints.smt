(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 32))

(assert (= (bvneg a) a))

;(check-sat)
;(get-model)
(count-models)

