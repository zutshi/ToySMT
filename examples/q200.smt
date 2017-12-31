;Q200. Find all solutions in positive integers (x, y, z) to the equations
;xy mod z = yz mod x = zx mod y = 2.

;http://www-cs-faculty.stanford.edu/~knuth/cp.html

(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))

(assert (= (bvurem (bvmul x y) z) (_ bv2 8)))
(assert (= (bvurem (bvmul y z) x) (_ bv2 8)))
(assert (= (bvurem (bvmul z x) y) (_ bv2 8)))

(assert (bvult x (_ bv16 8)))
(assert (bvult y (_ bv16 8)))
(assert (bvult z (_ bv16 8)))

(check-sat)
(get-model)
;(get-all-models)

