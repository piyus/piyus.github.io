; https://microsoft.github.io/z3guide/docs/theories/Bitvectors

; implement add using sum(x0, y0, c0) and carry(x0, y0, c0)
; sum(x0, y0, c0) = x0 xor y0 xor c0
; carry(x0, y0, c0) = (x0 & y0) | ((x0 | y0) & c0)


(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(declare-const z (_ BitVec 4))

(declare-const x0 (_ BitVec 1))
(declare-const x1 (_ BitVec 1))
(declare-const x2 (_ BitVec 1))
(declare-const x3 (_ BitVec 1))

(declare-const y0 (_ BitVec 1))
(declare-const y1 (_ BitVec 1))
(declare-const y2 (_ BitVec 1))
(declare-const y3 (_ BitVec 1))

(declare-const z0 (_ BitVec 1))
(declare-const z1 (_ BitVec 1))
(declare-const z2 (_ BitVec 1))
(declare-const z3 (_ BitVec 1))

(declare-const c0 (_ BitVec 1))
(declare-const c1 (_ BitVec 1))
(declare-const c2 (_ BitVec 1))
(declare-const c3 (_ BitVec 1))

(assert (= x0 ((_ extract 0 0) x)))
(assert (= x1 ((_ extract 1 1) x)))
(assert (= x2 ((_ extract 2 2) x)))
(assert (= x3 ((_ extract 2 2) x)))

(assert (= y0 ((_ extract 0 0) y)))
(assert (= y1 ((_ extract 1 1) y)))
(assert (= y2 ((_ extract 2 2) y)))
(assert (= y3 ((_ extract 2 2) y)))

(define-fun sum ((xi (_ BitVec 1)) (yi (_ BitVec 1)) (ci (_ BitVec 1))) (_ BitVec 1)
        (bvxor xi yi ci))

(define-fun carry ((xi (_ BitVec 1)) (yi (_ BitVec 1)) (ci (_ BitVec 1))) (_ BitVec 1)
        (bvor (bvand xi yi) (bvand (bvor xi yi) ci)))

(assert (= c0 #b0))
(assert (= z0 (sum x0 y0 c0)))
(assert (= z1 (sum x1 y1 c1)))
(assert (= z2 (sum x2 y2 c2)))
(assert (= z3 (sum x3 y3 c3)))
(assert (= c1 (carry x0 y0 c0)))
(assert (= c2 (carry x1 y1 c1)))
(assert (= c3 (carry x2 y2 c2)))

(assert (= z (bvadd x y)))
(assert (not (= z0 ((_ extract 0 0) z))))
(assert (not (= z1 ((_ extract 1 1) z))))
(assert (not (= z2 ((_ extract 2 2) z))))
(assert (not (= z3 ((_ extract 3 3) z))))
(check-sat)
