(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))

(declare-fun t1 () (_ BitVec 8))
(declare-fun t2 () (_ BitVec 8))

; TODO use bvshl
(assert (= t1 (bvsub (bvadd x y) (bvmul (bvand x y) #x02))))
(assert (= t2 (bvxor x y)))

(assert (not (= t1 t2)))

(check-sat)
(get-model)

