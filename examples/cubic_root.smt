(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun x () (_ BitVec 32))
(declare-fun out () (_ BitVec 32))

(assert (= out #x001c6503))
(assert (bvult x #x00010000))

; N.B.: ToySMT has no idea about cubic roots!
(assert (= (bvmul x x x) out))

(check-sat)
(get-model)

