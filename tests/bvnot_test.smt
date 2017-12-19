(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 8))
(declare-fun out () (_ BitVec 8))

(assert (= (bvnot a) out))
(assert (= out #x12))

(check-sat)
(get-model)

