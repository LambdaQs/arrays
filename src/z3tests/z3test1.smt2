; Declare a real variable
(declare-const a Int)
(declare-const b Int)

; Assert that a > 2
(assert (> (+ a b) 2))
(assert (> (- a b) 10))


; Ask Z3 to solve the constraints
(check-sat)

; Ask Z3 for a possible value of a
(get-model)
