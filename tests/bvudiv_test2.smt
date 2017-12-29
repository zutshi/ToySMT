(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))

(assert (= (bvudiv a b) #x10))
(assert (= (bvurem a b) #x03))

(check-sat)
(get-model)

