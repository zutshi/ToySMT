(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(declare-fun d () (_ BitVec 1))
(declare-fun e () (_ BitVec 1))

(assert (= a #x1234))

(assert (= ((_ extract 7 0) a) b))
(assert (= ((_ extract 15 8) a) c))
(assert (= ((_ extract 4 4) a) d))
(assert (= ((_ extract 0 0) a) e))

(check-sat)
(get-model)

