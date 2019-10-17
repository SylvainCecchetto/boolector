(set-option :incremental false)
(set-logic QF_BV)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))

(assert (not (= (bvashr s t) (ite (= ((_ extract 3 3) s) (_ bv0 1)) (bvlshr s t) (bvnot (bvlshr (bvnot s) t))))))


