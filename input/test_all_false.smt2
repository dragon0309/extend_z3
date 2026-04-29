(set-logic ALL)
(declare-fun x () (_ BitVec 8))

(assert
  (eqP
    (PMul
      (PConst (bv2nat x))
      (PSub (PConst (bv2nat x)) (PConst 1)))
    (PConst 0)))

; all-false assignment on both eqmod atoms
(assert
  (not
    (eqmodP1
      (PConst (bv2nat x))
      (PConst 0)
      (PConst 2))))

(assert
  (not
    (eqmodP1
      (PConst (bv2nat x))
      (PConst 1)
      (PConst 2))))

(check-sat)
