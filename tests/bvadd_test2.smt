(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))

; a=b+2
(assert (= a (bvadd b #x02)))
; b=c+4
(assert (= b (bvadd c #x04)))
; a+b+c=0x10
(assert (= (bvadd a b c) #x10))

; find a, b, c:
(check-sat)
(get-model)

