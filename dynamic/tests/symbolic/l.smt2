;
; definitions
;

(define-fun max ((x Int) (y Int)) Int (ite (> x y) x y))

(define-sort M () (Array Int Int))

; return the max value of a map
(declare-fun maxM (M) Int)
; axiomatization
(assert (forall ((m M) (x Int) (v Int))
    (= (maxM (store m x v))
       (max v (maxM m))
    )
))

; count the number of the given value
(declare-fun count (M Int) Int)
; axiomatization
;TODO: why this is unsat?
;(assert (forall ((m M) (x Int) (v Int))
;    (= (count (store m x v) v)
;       (+ (count m v) 1)
;    )
;))
(assert (forall ((m M) (x Int) (v Int) (w Int))
    (and
        (=> (not (= (select m x) w))
            (= (count (store m x v) w)
               (+ (count m w) (ite (= v w) 1 0))
            )
        )
        (=> (= (select m x) w)
            (= (count (store m x v) w)
               (+ (count m w) (ite (= v w) 0 -1))
            )
        )
    )
))
; count cannot be negative
(assert (forall ((m M) (v Int))
    (>= (count m v) 0)
))

; count beyond the maximum value is zero
(assert (forall ((m M) (v Int))
    (=> (> v (maxM m))
        (= (count m v) 0)
    )
))

;
; theorems
;

; validity property
(define-fun isValid ((m M) (l Int)) Bool
    (forall ((e Int))
        (=> (and (<= 0 e) (<= e (maxM m)))
            (<= (count m e) l)
        )
    )
)

; original map
(declare-const m M)
(declare-const x Int)

; e: current epoch
(declare-const e Int)
(assert (>= e 0))

; l = limit >= 4
(declare-const l Int)
(assert (>= l 4))

; v = max (maxM m) (e + 4)
(declare-const v Int)
(assert (= v (max (maxM m) (+ e 4))))

; w = new value
(declare-const w Int)
(assert (= w (ite (= (count m v) l) (+ v 1) v)))

; pre-condition: m is valid
(assert (isValid m l))
; x is empty
(assert (= (select m x) -1))

; updated map: m2 = m [ x <- w ]
(declare-const m2 M)
(assert (= m2 (store m x w)))

; verify post-condition: m2 is still valid
(assert (not
    (isValid m2 l)
))

(check-sat)
