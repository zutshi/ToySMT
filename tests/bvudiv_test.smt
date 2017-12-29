(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun q () (_ BitVec 8))
(declare-fun r () (_ BitVec 8))

(assert (= a #x41))
(assert (= b #x03))
(assert (= (bvudiv a b) q))
(assert (= (bvurem a b) r))

(check-sat)
(get-model)

