(set-option :incremental false)
(set-logic QF_BV)
(declare-fun s () (_ BitVec 2))
(declare-fun t () (_ BitVec 2))

(assert (not (= (bvashr s t) (ite (= ((_ extract 1 1) s) (_ bv0 1)) (bvlshr s t) (bvnot (bvlshr (bvnot s) t))))))


