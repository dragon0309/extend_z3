(set-logic ALL)
(declare-fun x () (_ BitVec 8))

(assert
  (eqmodP1
    (PVar (ubv_to_int x))
    (PConst 0)
    (PConst 2)))

(assert
  (not
    (eqmodP1
      (PVar (ubv_to_int x))
      (PConst 1)
      (PConst 2))))

(check-sat)
