(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(declare-fun out () (_ BitVec 4))

(assert (= a #x2))
(assert (= b #x2))
(assert (= (bvmul a b) out))

(declare-fun a2 () (_ BitVec 32))
(declare-fun b2 () (_ BitVec 32))
(declare-fun out2 () (_ BitVec 32))

(assert (= a2 #x12345678))
(assert (= b2 #x9abcdef0))
(assert (= (bvmul a2 b2) out2))

(check-sat)
(get-model)

