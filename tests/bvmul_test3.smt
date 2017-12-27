; using multiplier as divider!
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun out () (_ BitVec 16))

(assert (= a #x1234))
(assert (= out #xeca4))

(assert (=
                (bvmul
                        ((_ zero_extend 16) a)
                        ((_ zero_extend 16) b)
                )
                ((_ zero_extend 16) out)))
(check-sat)
(get-model)

