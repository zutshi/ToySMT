(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun x () (_ BitVec 32))
(declare-fun out () (_ BitVec 32))

(assert (= out #x00003b19))
(assert (bvult x #x00010000))

; N.B.: ToySMT has no idea about square roots!
(assert (= (bvmul x x) out))

(check-sat)
(get-model)

