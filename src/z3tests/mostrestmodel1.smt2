; Defining the length function
(declare-fun length ((Array Int Int)) Int)

; Declare the array a and its length n
(declare-const a (Array Int Int))
(declare-const n Int)
(assert (= (length a) n))

; Declareing that a is a range
(declare-const k Int)
(assert (forall ((i Int))
          (=> (and (>= i 0) (< i (length a)))
              (= (select a i) (+ k i)))))


; Declare the array b that is supposed to model the result of qMost on a
(declare-const b (Array Int Int))
(assert (= (length b) (- n 1)))

; Assert that b[i] = a[i] for all valid i
(assert (forall ((i Int))
          (=> (and (>= i 0) (< i (- n 1)))
              (= (select b i) (select a i)))))


; Declare the array c that is supposed to model the result of qRest on a
(declare-const c (Array Int Int))
(assert (= (length c) (- n 1)))

; Assert that b[i] = a[i + 1] for all valid i
(assert (forall ((i Int))
          (=> (and (>= i 0) (< i (- n 1)))
              (= (select c i) (select a (+ i 1))))))


(assert (exists ((x Int))
        (and
            (and (>= x 0) (< x (length b)))
            (= (select b x) (select c x)))))


; Ask Z3 to solve the constraints
(check-sat)

; Ask Z3 for a possible value of a
(get-model)
