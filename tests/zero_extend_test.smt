(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 32))

(assert (= a #x1234))

(assert (= ((_ zero_extend 16) a) b))

(check-sat)
(get-model)

