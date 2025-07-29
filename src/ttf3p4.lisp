;;;; ttf3p4.lisp
;;;;
;;;; Section 3.4 of https://okmij.org/ftp/tagless-final/course/lecture.pdf
;;;;
;;;; 3.4: Tagless final embedding with higher-order abstract syntax

(defpackage #:typed-tagless-final/3p4
  (:use
   #:coalton
   #:coalton-prelude)
  (:local-nicknames
   (#:str  #:coalton-library/string))
  (:export
    ))

(in-package #:typed-tagless-final/3p4)

(named-readtables:in-readtable coalton:coalton)

;;; 3.4: Tagless final embedding with higher-order abstract syntax
(coalton-toplevel
  (define (constant-at x) (fn (_) x))   ; utility
  
  ;; same language, but use host language for variable bindings
  (define-class (Symantics :repr)
    (int (Integer -> :repr Integer))
    (add (:repr Integer -> :repr Integer -> :repr Integer))
    (lam ((:repr :a -> :repr :b) -> :repr (:a -> :b)))
    (app (:repr (:a -> :b) -> :repr :a -> :repr :b)))
  
  ;; some sample terms to show what we mean
  ;; NOTE: this is around where i started to get disappointed that coalton wasn't willing to infer these parametric types.
  ;;       these examples are simple enough to manually type, but IRL this would get annoying.
  (declare th1 (Symantics :repr => :repr Integer))
  (define th1 (add (int 1) (int 2)))
  (declare th2 (Symantics :repr => :repr (Integer -> Integer)))
  (define th2 (lam (fn (x) (add x x)))) ; fn is the coalton fn!
  (declare th3 (Symantics :repr => :repr ((Integer -> Integer) -> Integer)))
  (define th3 (lam (fn (x) (add (app x (int 1)) (int 2)))))
  
  ;; evaluation interpreter
  (define-type (RType :a)
    (R :a))
  (define (unR (R val)) val)
  (define-instance (Symantics RType)
    (define (int x)
      (R x))
    (define (add e1 e2)
      (R (+ (unR e1) (unR e2))))
    (define (lam f)
      (R (fn (x) (unR (f (R x))))))
    (define (app e1 e2)
      (R ((unR e1) (unR e2)))))
  (define (eval e) (unR e))
  ;; DEMO: (eval th1)         ;; => 3
  ;; DEMO: ((eval th2) 4)     ;; => 8
  ;; DEMO: ((eval th3) (+ 2)) ;; => 5
  
  ;; printer interpreter
  (define-type-alias VarCounter Integer)
  (define-type (PType :a)
    (P (VarCounter -> String)))
  (define (unP (P val)) val)
  (define-instance (Symantics PType)
    (define (int x)
      (P (constant-at (into x))))
    (define (add e1 e2)
      (P (fn (h)
           (fold str:concat "" (make-list "(" (unP e1 h) " + " (unP e2 h) ")")))))
    ;; note that we can print lambda terms just fine, even though their contents has been directly encoded into coalton via fn!
    ;; the only thing we've lost is the variable name, for which we substitute a de brujin index instead.
    (define (lam f)
      (P (fn (h)
           (let ((x (str:concat "x" (into h))))
             (fold str:concat "" (make-list "(\\" x " -> " (unP (f (P (constant-at x))) (+ 1 h)) ")"))))))
    (define (app e1 e2)
      (P (fn (h)
           (fold str:concat "" (make-list "(" (unP e1 h) " " (unP e2 h) ")"))))))
  (define (view e) (unP e 0))
  ;; DEMO: (view th1) ;; => "(1 + 2)"
  ;; DEMO: (view th2) ;; => "(\x0 -> x0 + x0)"
  ;; DEMO: (view th3) ;; => "(\x0 -> ((x0 1) + 2))"
  
  ;; extending by multiplication, booleans, fixed point function, all as independent language extensions.
  (define-class (MulSym :repr)
    (mul (:repr Integer -> :repr Integer -> :repr Integer)))
  
  (define-class (BoolSym :repr)
    (bool (Boolean -> :repr Boolean))
    (leq (:repr Integer -> :repr Integer -> :repr Boolean))
    ;; one trade of the final form is that we're beholden to the evaluation model of the host language.
    ;; coalton evaluates function arguments eagerly, so we have to do the trick where its branches are frozen as lambdas and released conditionally.
    ;; we don't have 0-ary lambdas, so i have them consuming dummy integers for now 🤷‍♀️
    (if_ (:repr Boolean -> :repr (Integer -> :a) -> :repr (Integer -> :a) -> :repr :a)))
  
  (define-class (FixSym :repr)
    (fix_ ((:repr (:a -> :b) -> :repr (:a -> :b)) -> :repr (:a -> :b))))
  
  ;; some demo terms using these extensions.
  ;; 2-ary power function
  (declare tpow ((Symantics :repr) (MulSym :repr) (BoolSym :repr) (FixSym :repr) =>
                 :repr (Integer -> Integer -> Integer)))
  (define tpow
    (lam (fn (x)
           (fix_ (fn (self)
                   (lam (fn (n)
                          (if_ (leq n (int 0))
                               (lam (fn (_) (int 1)))
                               (lam (fn (_) (mul x (app self (add n (int -1))))))))))))))

  ;; 1-ary seventh power function
  (declare tpow7 ((Symantics :repr) (MulSym :repr) (BoolSym :repr) (FixSym :repr) =>
                  :repr (Integer -> Integer)))
  (define tpow7
    (lam (fn (x) (app (app tpow x) (int 7)))))
  ;; 2^7 as a closed but unevaluated term
  (declare tpow72 ((Symantics :repr) (MulSym :repr) (BoolSym :repr) (FixSym :repr) =>
                   :repr Integer))
  (define tpow72
    (app tpow7 (int 2)))
  ;; factorial function
  (declare fact ((Symantics :repr) (MulSym :repr) (BoolSym :repr) (FixSym :repr) =>
                 :repr (Integer -> Integer)))
  (define fact
    (fix_ (fn (self) (lam (fn (n) 
                            (if_ (leq n (int 0))
                                 (lam (fn (_) (int 1)))
                                 (lam (fn (_) (mul n (app self (add n (int -1))))))))))))
   
  ;; extending the evaluation interpreter over the language extensions
  (define-instance (MulSym RType)
    (define (mul e1 e2)
      (R (* (unR e1) (unR e2)))))
   
  (define-instance (BoolSym RType)
    (define (bool val)
      (R val))
    (define (leq e1 e2)
      (R (<= (unR e1) (unR e2))))
    (define (if_ bt et ef)
      (R (if (unR bt) ((unR et) 0) ((unR ef) 0)))))
  
  (define-instance (FixSym RType)
    (define (fix_ f)
      (R (fix (fn (self) (unR (f (R self))))))))
  
  ;; extending the printing interpreter over the language extensions
  (define-instance (MulSym PType)
    (define (mul e1 e2)
      (P (fn (h)
           (fold str:concat "" (make-list "(* " (unP e1 h) " " (unP e2 h) ")"))))))
  
  (define-instance (BoolSym PType)
    (define (bool val)
      (P (fn (h) (match val
                   ((True) "(bool True)")
                   ((False) "(bool False)")))))
    (define (leq e1 e2)
      (P (fn (h)
           (fold str:concat "" (make-list "(leq " (unP e1 h) " " (unP e2 h) ")")))))
    (define (if_ bt et ef)
      (P (fn (h)
           (fold str:concat "" (make-list "(if " (unP bt h) " " (unP et h) " " (unP ef h) ")"))))))
  
  (define-instance (FixSym PType)
    (define (fix_ f)
      (P (fn (h)
           (let ((self (str:concat "self" (into h))))
             (fold str:concat "" (make-list "(fix " self " . " (unP (f (P (const self))) (+ 1 h)) ")")))))))
  
  ;; DEMO: (view tpow72) ;; => "((\\x0 -> (((\\x1 -> (fix self2 . (\\x3 -> (if (leq x3 0) (\\x4 -> 1) (\\x4 -> (* x1 (self2 (x3 + -1)))))))) x0) 7)) 2)"
  ;; in particular this makes clear we haven't evaluated anything in assembling the term, we can see the whole pre-evaluation structure.
  ;; DEMO: (eval tpow72) ;; => 128 ; 😎
  ;; DEMO: (eval (app fact (int 15))) ;; => 1307674368000
  )