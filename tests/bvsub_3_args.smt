(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))

; check left-associativity. must be a-b-c=0x10 or (a-b)-c=0x10

(assert (= a #x20))
(assert (= b #x05))
(assert (= (bvsub a b c) #x10))

; find a, b, c:
(check-sat)
(get-model)

