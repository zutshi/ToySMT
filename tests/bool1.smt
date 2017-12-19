(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun p () Bool)
(declare-fun q () Bool)

(declare-fun out () Bool)

(assert (= (xor p q) out))
(assert (not p))
(assert out)

(check-sat)
(get-model)

