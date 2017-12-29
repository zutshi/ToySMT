(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))

; is a=b == a+(-b) for all a,b in two's complement system?
; prove it (by absence of counterexample):
(assert (not (= (bvsub a b) (bvadd a (bvneg b)))))

(check-sat)
(get-model)

