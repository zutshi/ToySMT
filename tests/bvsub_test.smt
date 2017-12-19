(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun out () (_ BitVec 8))

(assert (= a #x12))
(assert (= b #x10))
(assert (= (bvsub a b) out))

(check-sat)
(get-model)

