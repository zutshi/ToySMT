; find modulo inverse
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun m () (_ BitVec 16))

(assert (= 
		(bvudiv #x1236 #x0003) 
		(bvmul #x1236 m)))

(check-sat)
(get-model)

