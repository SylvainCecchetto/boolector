(set-option :incremental false)
(set-logic QF_BV)
(declare-fun s () (_ BitVec 1))
(declare-fun t () (_ BitVec 1))

(assert (let ((_let_0 ((_ extract 0 0) s))) (let ((_let_1 ((_ extract 0 0) t))) (let ((_let_2 (= _let_0 (_ bv0 1)))) (let ((_let_3 (= _let_1 (_ bv0 1)))) (let ((_let_4 (bvneg s))) (let ((_let_5 (bvneg t))) (not (= (bvsrem s t) (ite (and _let_2 _let_3) (bvurem s t) (ite (and (= _let_0 (_ bv1 1)) _let_3) (bvneg (bvurem _let_4 t)) (ite (and _let_2 (= _let_1 (_ bv1 1))) (bvurem s _let_5) (bvneg (bvurem _let_4 _let_5))))))))))))))


