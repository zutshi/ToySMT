(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))

(declare-fun i () Bool)
(declare-fun j () Bool)

(assert (= a #x34))
(assert (= b #x12))
(assert (= (ite i a b) #x12))
(assert (= (ite j b a) #x12))

(check-sat)
(get-model)

