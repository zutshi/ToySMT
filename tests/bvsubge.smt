; non-standard function, used in divisor
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a1 () (_ BitVec 8))
(declare-fun b1 () (_ BitVec 8))
(declare-fun out1 () (_ BitVec 8))

(assert (= a1 #x12))
(assert (= b1 #x13))

(assert (= (bvsubge a1 b1) out1))

(declare-fun a2 () (_ BitVec 8))
(declare-fun b2 () (_ BitVec 8))
(declare-fun out2 () (_ BitVec 8))

(assert (= a2 #x12))
(assert (= b2 #x11))

(assert (= (bvsubge a2 b2) out2))

(check-sat)
(get-model)

