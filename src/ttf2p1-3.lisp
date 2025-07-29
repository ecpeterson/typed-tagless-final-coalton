;;;; ttf2p1-3.lisp
;;;;
;;;; Sections 2.1-3 of https://okmij.org/ftp/tagless-final/course/lecture.pdf
;;;;
;;;; 2.1: interpreting a toy language with literals, negation, addition
;;;; 2.2: extending the language with multiplication
;;;; 2.3: successive interpretation
;;;;
;;;; We have to put these in the same file because 2.3 defines a typeclass
;;;; instance which refers only to typeclasses from 2.1.

(defpackage #:typed-tagless-final/2p1-3
  (:use
   #:coalton
   #:coalton-prelude)
  (:local-nicknames
   (#:str  #:coalton-library/string)
   (#:list #:coalton-library/list))
  (:export
    #:LitTag
    #:NegTag
    #:AddTag

    #:Exp-Sym
    #:lit
    #:neg
    #:add

    #:eval
    #:view

    #:Mul-Sym
    #:mul
    ))

(in-package #:typed-tagless-final/2p1-3)

(named-readtables:in-readtable coalton:coalton)

;;; 2.1: interpreting a toy language with literals, negation, addition
(coalton-toplevel
;;; initial form
  ;; term datatype
  (define-type Expr
    (LitTag Integer)
    (NegTag Expr)
    (AddTag Expr Expr))
  
  ;; toy term, embedded in the host language via the data type Expr
  (define ti1 (AddTag (LitTag 8) (NegTag (AddTag (LitTag 1) (LitTag 2)))))
  
  ;; evaluation interpreter
  (declare eval-tag (Expr -> Integer))
  (define (eval-tag expr)
    (match expr
      ((LitTag x)
       x)
      ((NegTag x)
       (- 0 (eval-tag x)))
      ((AddTag x y)
       (+ (eval-tag x) (eval-tag y)))))
  
  ;; printing interpreter
  (declare view-tag (Expr -> String))
  (define (view-tag expr)
    (match expr
      ((LitTag x)
       (into x))
      ((NegTag x)
       (fold str:concat "" (make-list "(-" (view-tag x) ")")))
      ((AddTag x y)
       (fold str:concat "" (make-list "(" (view-tag x) "+" (view-tag y) ")")))))
  
;;; final form
  ;; term typeclass
  (define-class (Exp-Sym :repr)
    (lit (Integer -> :repr))
    (neg (:repr -> :repr))
    (add (:repr -> :repr -> :repr)))
  
  ;; toy term, embedded in the host language as a delayed native expression awaiting semantics
  ;; NOTE: coalton is uncomfortable defining parametric terms unless you explicitly provide it a parametric type.  (haskell, otoh, will gladly infer the parametric type for you.)  this accounts for _most_ of the `declare's found throughout.
  (declare tf1 (Exp-Sym :repr => :repr))
  (define tf1 (add (lit 8) (neg (add (lit 1) (lit 2)))))
  
  ;; interpreters are written by specializing the typeclass parameter to some value type.
  ;; the typeclass instance carries the interpretation semantics.

  ;; evaluation interpreter
  (define-instance (Exp-Sym Integer)
    (define (lit x) x)
    (define (neg x) (- 0 x))
    (define (add x y) (+ x y)))
  ;; the only job of eval is to bind the parameter type
  (declare eval (Integer -> Integer))
  (define (eval x) x)
  
  ;; printing interpreter
  (define-instance (Exp-Sym String)
    (define (lit x)
      (into x))
    (define (neg x)
      (fold str:concat "" (make-list "(-" x ")")))
    (define (add x y)
      (fold str:concat "" (make-list "(" x "+" y ")"))))
  ;; the only job of view is to bind the parameter type
  (declare view (String -> String))
  (define (view x) x))

;;; 2.2: extending the language with multiplication
(coalton-toplevel
  ;; in the initial form of the language, the data type Expr is "closed".
  ;; to extend language we have to either rewrite the type or build some new type which includes it along some tag.
  ;; in the final form, we get around this by simultaneous inhabitation of typeclasses.
  (define-class (Mul-Sym :repr)
    (mul (:repr -> :repr -> :repr)))
  
  ;; some toy terms which mix the old Exp-Sym typeclass with the new Mul-Sym typeclass.
  ;; neither "inherits" from the other; they just coexist.
  (declare tfm1 ((Mul-Sym :repr) (Exp-Sym :repr) => :repr))
  (define tfm1 (add (lit 7) (neg (mul (lit 1) (lit 2)))))
  (declare tfm2 ((Mul-Sym :repr) (Exp-Sym :repr) => :repr))
  (define tfm2 (mul (lit 7) tf1))
  
  ;; evaluation semantics for mul
  (define-instance (Mul-Sym Integer)
    (define (mul x y) (* x y)))
  
  ;; printing semantics for mul
  (define-instance (Mul-Sym String)
    (define (mul x y)
      (fold str:concat "" (make-list "(" x "*" y ")")))))

;;; 2.3: successive interpretation
(coalton-toplevel
  ;; a (psychological?) advantage of the initial presentation is that it is clearer what it means to copy + store + recall data.
  ;; to explore this, consider the following serialization format:
  (define-type Tree
    (Leaf String)
    (Node String (List Tree)))
  (define-instance (Into Tree String)
    (define (into x)
      (match x
        ((Leaf y)
         (fold str:concat "" (make-list "(Leaf " y ")")))
        ((Node y z)
         (let ((body (fold str:concat "" (list:intersperse " " (map into z)))))
           (fold str:concat "" (make-list "(Node \"" y "\" " body ")")))))))
  
  ;; serializing interpreter
  (define-instance (Exp-Sym Tree)
    (define (lit x)
      (Node "Lit" (make-list (Leaf (into x)))))
    (define (neg x)
      (Node "Neg" (make-list x)))
    (define (add x y)
      (Node "Add" (make-list x y))))
  (declare to-tree (Tree -> Tree))
  (define (to-tree x) x)
  
  ;; serialized form of toy tf1 term from before
  (define tf1_tree (to-tree tf1))
  
  ;; deserializing is inherently partial.
  ;; we explore this in a limited context by parsing out the string-serialized integer literals, string node names, and accompanying node widths, allowing for each kind of failure.
  (define-type-alias ErrMsg String)
  (declare safe-read (String -> Result ErrMsg Integer))
  (define (safe-read x)
    (match (str:parse-int x)
      ((None) (err (str:concat "Invalid tree: " x))) ; flag the offending string
      ((Some y) (ok y))))  
  ;; the paper indicates that this has to be written in an open style (i.e., explicitly naming `self' and then feeding it through `fix') to account for language extensions, which then have to explicitly interrupt the `fix' process; see below.
  ;; this feels to me like a weak point of the whole argument, but perhaps there's some satisfying conceptual explanation why the input laxness of the deserialization problem forces this on us.
  (define (from-tree-ext self x)
    (match x
      ((Node "Lit" (Cons (Leaf y) (Nil)))
       (map lit (safe-read y)))
      ((Node "Neg" (Cons y (Nil)))
       (map neg (self y)))
      ((Node "Add" (Cons y (Cons z (Nil))))
       (liftA2 add (self y) (self z)))
      (_
       (err (str:concat "Invalid tree: " (into x)))))) ; flag the offending string
  (declare from-tree ((Exp-Sym :repr) => (Tree -> (Result ErrMsg :repr))))
  (define from-tree
    (fix from-tree-ext))
  
  ;; if we load something from disk and naively try to apply a couple of different interpreters to it --- say, printing the AST and then printing the evaluation result --- we will fail on a type error, having attempted to multiply constrain the typeclass parameter type.
  #+#:this-will-fail
  (match (from-tree tf1_tree)
    ((Err x)
     (print (str:concat "Error: " x)))
    ((Ok x)
     (print (view x))
     (print (eval x)))) ;; <-- type error, x got specialized along String, can't respecialize
  
  ;; to get around this, we introduce an interpreter which clones the final tree as it goes, so that we can interpret one output through specialization & leave the other output unspecialized for unconstrained future use.
  ;; NOTE: coalton requires define-instance to reference at least some symbol from the present package, so `duplicate' can't be deferred the same way the paper is structured
  (define-instance ((Exp-Sym :r1) (Exp-Sym :r2) => Exp-Sym (Tuple :r1 :r2))
    (define (lit x)
      (Tuple (lit x) (lit x)))
    (define (neg (Tuple x1 x2))
      (Tuple (neg x1) (neg x2)))
    (define (add (Tuple e11 e12) (Tuple e21 e22))
      (Tuple (add e11 e21) (add e12 e22))))
  (declare duplicate ((Exp-Sym :r1) (Exp-Sym :r2) => (Tuple :r1 :r2) -> (Tuple :r1 :r2)))
  (define (duplicate x) x)
  
  ;; helper which does something to a final tree (and prints the result) but preserves an unmolested final tree as output
  (define (without-specializing ev x)
    (match (duplicate x)
      ((Tuple x1 x2)
       (print (ev x1))
       x2)))
  
  ;; demo multi-pass interpreter
  (define (multipass x)
    (pipe x
          (without-specializing view)      ; print "internal" AST
          (without-specializing eval)      ; print evaluation result
          (fn (xx) (print (to-tree xx))))) ; print serialized result
  
  ;; TODO: does this have a nicer expression in terms of Result?
  (define (check-consume f x)
    (match x
      ((Err y)
       (print (str:concat "Error: " y)))
      ((Ok y)
       (f y))))

  ;; DEMO: deserialize **once**, multiply interpret
  ;; (check-consume multipass (from-tree tf1_tree))
  
  ;; we can extend the map into the serialization format by providing more typeclass instances
  (define-instance (Mul-Sym Tree)
    (define (mul e1 e2)
      (Node "Mul" (make-list e1 e2))))
  (define-instance ((Mul-Sym :r1) (Mul-Sym :r2) => Mul-Sym (Tuple :r1 :r2))
    (define (mul (Tuple e11 e12) (Tuple e21 e22))
      (Tuple (mul e11 e21) (mul e12 e22))))
  
  ;; extending the deserialization map is more invasive. with forethought (viz., writing from-tree-ext as an open recursion) it is possible, but it makes explicit some hierarchy of extensions via the subcall.
  (define (from-tree-ext-mul self x)
    (match x
      ((Node "Mul" (Cons x (Cons y (Nil))))
       (liftA2 mul (self x) (self y)))
      (_
       (from-tree-ext self x))))
  (declare from-tree-mul ((Exp-Sym :repr) (Mul-Sym :repr) => (Tree -> (Result ErrMsg :repr))))
  (define from-tree-mul
    (fix from-tree-ext-mul))
  ;; DEMO: (check-consume multipass (from-tree-mul tf1_tree))
  ;; DEMO: (check-consume multipass (from-tree-mul (to-tree tfm1)))
  )
