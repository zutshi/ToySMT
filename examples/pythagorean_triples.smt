(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

; https://en.wikipedia.org/wiki/Pythagorean_triple
; http://www.tsm-resources.com/alists/trip.html

(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))

(assert (bvule a #x0010))
(assert (bvule b #x0010))
(assert (bvule c #x0010))

(assert (not (= a #x0000)))
(assert (not (= b #x0000)))
(assert (not (= c #x0000)))

(assert (= 
		(bvadd 
			(bvmul a a)
			(bvmul b b)
		)
		(bvmul c c)
	)
)

;(check-sat)
;(get-model)
(get-all-models)

