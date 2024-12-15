(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun |x4| () Real)
;;(set-logic B)
(assert (not(< (+ (* (- 4) (+ (* (* x1 x1) (* x2 x2)) (* (* x1 x1) (* 
x4 x4)) (* (* x2 x2) (* x3 x3)) (* (* x3 x3) (* x4 
x4)))) (* (+ (* x1 x1) (* x2 x2) (* x3 x3) (* x4 
x4)) (+ (* x1 x1) (* x2 x2) (* x3 x3) (* x4 x4)))) 0)))
(assert (or (and (> (+ (- x1 0.0) (- 1)) 0) (>= (- x1 x2 (* (/ 1 (- 2)) x3 x4)) 0))
            (and (<= (- x2 (- 1 (/ 3 2))) 0) (= (- x1 x2 (* (/ 1 (- 2)) x2 x4)) 0))
            (> (+ x4 (/ 4 10)) (- x3 10) )))
(assert (not (or (and (> (+ x1 (- 1)) 0) (>= (- x1 x2 (* (/ 1 (- 2)) x3 x4)) 0) (= x1 2))
            (and (<= (- x2 (- 1 (/ 3 2))) 0) (= (- x1 x2 (* (/ 1 (- 2)) x2 x4)) 0))
            (> x4 x3))))
(assert (> (- x1 x4) 10))
(check-sat)