; H+E+L+L+O = W+O+R+L+D = 25

(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

;(declare-const H (_ BitVec 8)) ; z3 OK, but not STP and btor
(declare-fun H () (_ BitVec 8)) ; z3, STP and btor
(declare-fun E () (_ BitVec 8))
(declare-fun L () (_ BitVec 8))
(declare-fun O () (_ BitVec 8))
(declare-fun W () (_ BitVec 8))
(declare-fun R () (_ BitVec 8))
(declare-fun D () (_ BitVec 8))

(assert (and (bvuge H (_ bv1 8)) (bvule H (_ bv9 8))))
(assert (and (bvuge E (_ bv1 8)) (bvule E (_ bv9 8))))
(assert (and (bvuge L (_ bv1 8)) (bvule L (_ bv9 8))))
(assert (and (bvuge O (_ bv1 8)) (bvule O (_ bv9 8))))
(assert (and (bvuge W (_ bv1 8)) (bvule W (_ bv9 8))))
(assert (and (bvuge R (_ bv1 8)) (bvule R (_ bv9 8))))
;(assert (and (bvuge R #b00000001) (bvule R #b00001001))) ; should also work
(assert (and (bvuge D #x01) (bvule D #x09))) ; should also work

;(assert (=(bvadd H E L L O) (_ bv25 8))) ; z3, btor OK, but not STP
;(assert (=(bvadd W O R L D) (_ bv25 8)))

(assert (=(bvadd (bvadd (bvadd (bvadd H E) L) L) O) (_ bv25 8)))
(assert (=(bvadd (bvadd (bvadd (bvadd W O) R) L) D) (_ bv25 8)))

;(assert (distinct H E L O W R D)) ; should also work
(assert (not(= H E)))
(assert (not(= H L)))
(assert (not(= H O)))
(assert (not(= H W)))
(assert (not(= H R)))
(assert (not(= H D)))

(assert (not(= E L)))
(assert (not(= E O)))
(assert (not(= E W)))
(assert (not(= E R)))
(assert (not(= E D)))

(assert (not(= L O)))
(assert (not(= L W)))
(assert (not(= L R)))
(assert (not(= L D)))

(assert (not(= O W)))
(assert (not(= O R)))
(assert (not(= O D)))

(assert (not(= W R)))
(assert (not(= W D)))

(assert (not(= R D)))

(check-sat)
(get-model)

