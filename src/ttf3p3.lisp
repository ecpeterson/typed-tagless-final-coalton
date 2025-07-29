;;;; ttf3p3.lisp
;;;;
;;;; Section 3.3 of https://okmij.org/ftp/tagless-final/course/lecture.pdf
;;;;
;;;; 3.3: typed final embedding of integer lambda calculus

(defpackage #:typed-tagless-final/3p3
  (:use
   #:coalton
   #:coalton-prelude)
  (:local-nicknames
   (#:str  #:coalton-library/string))
  (:export
    ))

(in-package #:typed-tagless-final/3p3)

(named-readtables:in-readtable coalton:coalton)

;;; 3.3: typed final embedding of integer lambda calculus
(coalton-toplevel
  (define (constant-at x) (fn (_) x))   ; utility
  
  ;; basic final embedding of integer lambda calculus via de brujin indices.
  ;; :h is a "rest of environment" type. we'll use a Cons-list-like structure but made out of `Tuple's so that we can support nonuniform value types. (this makes explicit the total environment type at each stage of the computation.)
  (define-class (Symantics :repr)
    (int (Integer -> :repr :h Integer))
    (add (:repr :h Integer -> :repr :h Integer -> :repr :h Integer))
    (z (:repr (Tuple :a :h) :a))        ; zeroth variable
    (s (:repr :h :a -> :repr (Tuple :any :h) :a)) ; scroll to next variable when evaling inside of s
    ;; if prepending :a to env and running the body yields :b, then lam yields :a -> :b in env.
    (lam (:repr (Tuple :a :h) :b -> :repr :h (:a -> :b)))
    ;; given a function yielding :b from env + :a and given an :a, get :b
    (app (:repr :h (:a -> :b) -> :repr :h :a -> :repr :h :b)))
  
  ;; some sample terms and their types
  (declare td1 (Symantics :repr => :repr :h Integer))
  (define td1
    (add (int 1) (int 2)))              ; (+ 1 2)
  (declare td2o (Symantics :repr => :repr (Tuple Integer :h) (Integer -> Integer)))
  (define td2o
    (lam (add z (s z))))                ; (fn (x1) (+ x1 x0))
  (declare td3 (Symantics :repr => :repr :h ((Integer -> Integer) -> Integer)))
  (define td3
    (lam (add (app z (int 1)) (int 2)))) ; (fn (x0) (+ (x0 1) 2))
  
  ;; evaluation interpreter.
  ;; R is not actually a type tag, just an interpreter tag. because unR is total (even branch-less!), it can be compiled out.
  ;; (:h -> :a) lets us evaluate the environment to form a term.
  ;; we model the environment as nested `Tuple's, so that we can keep values of nonuniform type.
  (define-type (RType :h :a)
    (R (:h -> :a)))
  (define (unR (R val)) val)
  (define-instance (Symantics RType)
    (define (int x)
      (R (constant-at x))) ; constants don't depend on the environment
    (define (add e1 e2)
      (R (fn (env) (+ (unR e1 env) (unR e2 env))))) ; addition acts on immediates
    (define z
      (R (fn ((Tuple x _)) x)))    ; look up zeroth var in environment
    (define (s v)
      (R (fn ((Tuple _ h)) (unR v h)))) ; drop head of environment while evaling v
    (define (lam e)
      (R (fn (env x) (unR e (Tuple x env))))) ; absorb delayed value x into env, then eval e
    (define (app e1 e2)
      (R (fn (env) ((unR e1 env) (unR e2 env))))))
  (define (eval e)
    (unR e Nil))          ; any garbage environment value here is fine, pick a non-language term to guarantee type error on invalid access
  ;; DEMO: (eval td1)         ;; => 3
  ;; DEMO: ((eval td3) (+ 2)) ;; => 5 ; note that this mixes embedded language and host language!
  
  ;; printer interpreter. nothing too exciting beyond string munging.
  (define-type (PType :h :a)
    (P (Integer -> String))) ; the Integer "environment" this time is the innermost de brujin label
  (define (unP (P val)) val)
  (define-instance (Symantics PType)
    (define (int x)
      (P (constant-at (into x))))
    (define (add e1 e2)
      (P (fn (h)
           (fold str:concat "" (make-list "(" (unP e1 h) " + " (unP e2 h) ")")))))
    (define z
      (P (fn (h) (str:concat "x" (into (- h 1))))))
    (define (s v)
      (P (fn (h) (unP v (- h 1)))))
    (define (lam e)
      (P (fn (h)
           (let ((x (str:concat "x" (into h))))
             (fold str:concat "" (make-list "(\\" x " -> " (unP e (+ 1 h)) ")"))))))
    (define (app e1 e2)
      (P (fn (h)
           (fold str:concat "" (make-list "(" (unP e1 h) " " (unP e2 h) ")"))))))
  (define (view e)
    (unP e 0))
  ;; DEMO: (view td1)  ;; => "(1 + 2)"
  ;; DEMO: (view td2o) ;; => "(\x0 -> (x0 + x-1))" ; can print open terms just fine!
  ;; DEMO: (view td3)  ;; => "(\x0 -> ((x0 1) + 2))"
  )