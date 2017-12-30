(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 2))
(declare-fun b () (_ BitVec 2))
(declare-fun c () (_ BitVec 2))
(declare-fun d () (_ BitVec 2))

(assert (distinct a b c d))

;(get-all-models)
(count-models)

