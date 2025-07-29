;;;; ttf2p4.lisp
;;;;
;;;; Section 2.4 of https://okmij.org/ftp/tagless-final/course/lecture.pdf
;;;;
;;;; 2.4: structural transformations

(defpackage #:typed-tagless-final/2p4
  (:use
   #:coalton
   #:coalton-prelude
   #:typed-tagless-final/2p1-3)
  (:local-nicknames
   (#:str  #:coalton-library/string)
   (#:list #:coalton-library/list))
  (:export
    ))

(in-package #:typed-tagless-final/2p4)

(named-readtables:in-readtable coalton:coalton)

;;; 2.4: structural transformations
(coalton-toplevel
  ;; let's put our arithmetic trees into a normal form, starting by pushing negation down to the leaves.
  ;; here's an initial version.  while this is a common way to write ethis, it isn't the only way (which will limit our complaints about it below).
  (define (push-neg-tag x)
    (match x
      ((LitTag _)                  ; if we're at a leaf, nothing to do
       x)
      ((NegTag (LitTag _)) ; if we're at a negative at a leaf, that's also good, that's what we want
       x)
      ((NegTag (NegTag y))              ; cancel out negative pairs
       (push-neg-tag y))
      ((NegTag (AddTag y z))        ; push negatives down through sums
       (AddTag (push-neg-tag (NegTag y))
               (push-neg-tag (NegTag z))))
      ((AddTag y z)             ; push our tree walk down through sums
       (AddTag (push-neg-tag y) (push-neg-tag z)))))
  ;; it is not super obvious that this is structurally complete, and the clause ordering matters.

  ;; in the final presentation, we are more obviously constrained to a pure structural tree walk, with no hope of matching on elaborate terms like (neg (neg e)).
  ;; instead, we carry along any context we need in a side value.  the side value here will be an outer multiplication by ±1.
  (define-type PushNegCtx
    Positive
    Negative)
  
  ;; the final version is then expressed as another interpreter.
  ;; the interpreter type straightforwardly describes a mechanism for converting transformation context into (arbitrary) final terms; more sneakily, it also provides an opportunity to convert final terms into transformation context.
  (define-instance (Exp-Sym :repr => Exp-Sym (PushNegCtx -> :repr))
    (define (lit n ctx) ; disgorge negation in the context onto a literal
      (match ctx
        ((Positive)
         (lit n))
        ((Negative)
         (neg (lit n)))))
    (define (neg e ctx) ; ingest negation in the tree into the context
      (match ctx
        ((Positive) 
         (e Negative))
        ((Negative)
         (e Positive))))
    (define (add e1 e2 Ctx) ; rewrite ±1 * (x + y) as (± 1 * x) + (± 1 * y)
      (add (e1 Ctx) (e2 Ctx))))
  (define (push-neg x) ; as usual, rig the interpreter by binding the type --- and providing initial context!
    (x Positive))
  
  ;; pleasingly, we can still extend the final approach over language extensions:
  (define-instance (Mul-Sym :repr => Mul-Sym (PushNegCtx -> :repr))
    (define (mul e1 e2 ctx)
      (match ctx
        ((Positive)
         (mul (e1 Positive) (e2 Positive)))
        ((Negative)
         (mul (e1 Positive) (e2 Negative))))))
  
  ;; let's consider another common normalization transformation: right-associating iterated addition.
  ;; here's the initial version:
  (define (flata-tag x)
    (match x
      ((LitTag _)
       x)
      ((NegTag _)
       x)
      ((AddTag (AddTag e1 e2) e3) ; again, we lean on early matching of complex structures
       (flata-tag (AddTag e1 (AddTag e2 e3))))
      ((AddTag e1 e2)
       (AddTag e1 (flata-tag e2)))))
  
  ;; compound transformation with our two normalizing passes so far
  (define (norm-tag x)
    (flata-tag (push-neg-tag x)))
  
  ;; toy initial term which illustrates the transformation
  (define ti3
    (AddTag typed-tagless-final/2p1-3::ti1
            (NegTag (NegTag typed-tagless-final/2p1-3::ti1))))
  ;; DEMO: (view-tag (norm-tag ti3))
  
  ;; here's the final version of the right-association transformation.
  ;; this time, the context value carries along a possible parent expression of which we're a subexpression.
  (define-type (FlatCtx :e)
    (LCA :e) ; "Left Child Add", (LCA e3) represents going down the hole in (Add [] e3)
    NonLCA)  ; an unadorned hole [] for all other situations 
  
  (define-instance (Exp-Sym :repr => Exp-Sym (FlatCtx :repr -> :repr))
    (define (lit n ctx)         ; plug the literal into whichever hole
      (match ctx
        ((NonLCA)
         (lit n))
        ((LCA e)
         (add (lit n) e))))
    (define (neg e ctx)
      (match ctx
        ((NonLCA)            ; convert e to a value and apply negation
         (neg (e NonLCA)))
        ((LCA e3) ; neg interrupts reassocation, so expand the (Add [] e3) hole and switch to NonLCA
         (add (neg (e NonLCA)) e3))))
    ;; rotate context onto right branch, absorb *this* addition into context as "e1 is the left branch of adding with e2"
    (define (add e1 e2 ctx)
      (e1 (LCA (e2 ctx)))))
  ;; rigging the interpreter requires a DECLARE, since the initial context is the 0-ary NonLCA but we need to bind the FlatCtx type parameter
  (declare flata ((Exp-Sym :repr) => (FlatCtx :repr -> :repr) -> :repr))
  (define (flata x) (x NonLCA))

  ;; compound normalization transformation in the final view
  (define (norm x) (flata (push-neg x)))
  
  ;; toy final term.  typechecker gets spooked (by unifying tf1 with tf1?) unless we're explicit
  (declare tf3 (Exp-Sym :repr => :repr))
  (define tf3
    (add typed-tagless-final/2p1-3::tf1
         (neg (neg typed-tagless-final/2p1-3::tf1))))
  ;; DEMO: (print (view (norm tf3)))
  
  ;; TODO: write a distributive transform for Mul-Sym
  )