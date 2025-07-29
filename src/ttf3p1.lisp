;;;; ttf3p1.lisp
;;;;
;;;; Section 3.1 of https://okmij.org/ftp/tagless-final/course/lecture.pdf
;;;;
;;;; 3.1: un/typed lambda calculus in initial form

(defpackage #:typed-tagless-final/3p1
  (:use
   #:coalton
   #:coalton-prelude)
  (:local-nicknames
   (#:str  #:coalton-library/string))
  (:export
    ))

(in-package #:typed-tagless-final/3p1)

(named-readtables:in-readtable coalton:coalton)

;;; 3.1: un/typed lambda calculus in initial form
(coalton-toplevel
  ;; de brujin indices for arguments
  (define-type Variable
    VarZero
    (VarSucc Variable))
  ;; AST for (untyped) lambda calculus
  (define-type DataTag
    (VarTag Variable)
    (BoolTag Boolean)
    (LambdaTag DataTag)
    (ApplyTag DataTag DataTag))
  ;; term evaluation can give two things back, so obligated to build a union type with tags
  (define-type UniverseTag
    (UBool Boolean)
    (UApp (UniverseTag -> UniverseTag)))
  
  ;; lookup successor-encoded indices inside of a list
  (define (lookp x env)
    (match (Tuple x env)
      ((Tuple (VarSucc z) (Cons _ y))
       (lookp z y))
      ;; nonexhaustive compiler warning
      ((Tuple (VarZero) (Cons y _))
       y)))
  
  ;; evaluation rules
  (define (eval env term)
    (match term
      ((VarTag var)
       (lookp var env))
      ((BoolTag bool)
       (UBool bool))
      ((LambdaTag ell)
       (UApp (fn (x) (eval (Cons x env) ell))))
      ((ApplyTag f x)
       ;; nonexhaustive compiler warning --- can't tell if eval'ing f will give something to which x can be applied
       (match (eval env f)
         ((UApp f-resolved)
          (f-resolved (eval env x)))))))
  
  ;; toy term
  (define ti1
    (ApplyTag (LambdaTag (VarTag VarZero)) (BoolTag True)))
  ;; DEMO: (eval Nil ti1)
  
  ;; example ill-typed terms from the perspective of eval but the initial encoding permits them anyway
  (define ti2a
    (ApplyTag (BoolTag True) (BoolTag False))) ; can't apply bool to bool
  (define ti2o
    (ApplyTag (LambdaTag (VarTag (VarSucc VarZero))) (BoolTag True))) ; oob variable
  
  ;; could build some (declare type-check (DataTag -> Result ErrMsg DataTag))
  ;; but eval has no way of knowing whether type-check has been done, so needs tags
  )