(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))

(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))

(assert (= t1 (bvsub (bvadd x y) (bvmul (bvand x y) #x02))))
(assert (= t2 (bvxor x y)))

(assert (not (= t1 t2)))

(check-sat)
(get-model)

