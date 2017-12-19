(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun out () Bool)

(assert out)

(check-sat)
(get-model)

