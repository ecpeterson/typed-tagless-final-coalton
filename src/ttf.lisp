;;;; ttf.lisp
;;;;
;;;; working through https://okmij.org/ftp/tagless-final/course/lecture.pdf in coalton

(in-package #:typed-tagless-final)

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
    (AddTag ti1 (NegTag (NegTag ti1))))
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
    (add tf1 (neg (neg tf1))))
  ;; DEMO: (print (view (norm tf3)))
  
  ;; TODO: write a distributive transform for Mul-Sym
  )

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

;;; 3.2: typed initial embedding via GADTs, which IIUC coalton doesn't have

;;; 3.3: typed final embedding of integer lambda calculus
(coalton-toplevel
  (define (constant-at x) (fn (_) x))   ; utility
  
  ;; basic final embedding of integer lambda calculus via de brujin indices.
  ;; :h is a "rest of environment" type. we'll use a Cons-list-like structure but made out of `Tuple's so that we can support nonuniform value types. (this makes explicit the total environment type at each stage of the computation.)
  (define-class (SymanticsDB :repr)
    (int (Integer -> :repr :h Integer))
    (add (:repr :h Integer -> :repr :h Integer -> :repr :h Integer))
    (z (:repr (Tuple :a :h) :a))        ; zeroth variable
    (s (:repr :h :a -> :repr (Tuple :any :h) :a)) ; scroll to next variable when evaling inside of s
    ;; if prepending :a to env and running the body yields :b, then lam yields :a -> :b in env.
    (lam (:repr (Tuple :a :h) :b -> :repr :h (:a -> :b)))
    ;; given a function yielding :b from env + :a and given an :a, get :b
    (app (:repr :h (:a -> :b) -> :repr :h :a -> :repr :h :b)))
  
  ;; some sample terms and their types
  (declare td1 (SymanticsDB :repr => :repr :h Integer))
  (define td1
    (add (int 1) (int 2)))              ; (+ 1 2)
  (declare td2o (SymanticsDB :repr => :repr (Tuple Integer :h) (Integer -> Integer)))
  (define td2o
    (lam (add z (s z))))                ; (fn (x1) (+ x1 x0))
  (declare td3 (SymanticsDB :repr => :repr :h ((Integer -> Integer) -> Integer)))
  (define td3
    (lam (add (app z (int 1)) (int 2)))) ; (fn (x0) (+ (x0 1) 2))
  
  ;; evaluation interpreter.
  ;; R is not actually a type tag, just an interpreter tag. because unR is total (even branch-less!), it can be compiled out.
  ;; (:h -> :a) lets us evaluate the environment to form a term.
  ;; we model the environment as nested `Tuple's, so that we can keep values of nonuniform type.
  (define-type (RTypeDB :h :a)
    (RDB (:h -> :a)))
  (define (unRDB (RDB val)) val)
  (define-instance (SymanticsDB RTypeDB)
    (define (int x)
      (RDB (constant-at x))) ; constants don't depend on the environment
    (define (add e1 e2)
      (RDB (fn (env) (+ (unRDB e1 env) (unRDB e2 env))))) ; addition acts on immediates
    (define z
      (RDB (fn ((Tuple x _)) x)))    ; look up zeroth var in environment
    (define (s v)
      (RDB (fn ((Tuple _ h)) (unRDB v h)))) ; drop head of environment while evaling v
    (define (lam e)
      (RDB (fn (env x) (unRDB e (Tuple x env))))) ; absorb delayed value x into env, then eval e
    (define (app e1 e2)
      (RDB (fn (env) ((unRDB e1 env) (unRDB e2 env))))))
  (define (eval e)
    (unRDB e Nil))          ; any garbage environment value here is fine, pick a non-language term to guarantee type error on invalid access
  ;; DEMO: (eval td1)         ;; => 3
  ;; DEMO: ((eval td3) (+ 2)) ;; => 5 ; note that this mixes embedded language and host language!
  
  ;; printer interpreter. nothing too exciting beyond string munging.
  (define-type (PTypeDB :h :a)
    (PDB (Integer -> String))) ; the Integer "environment" this time is the innermost de brujin label
  (define (unPDB (PDB val)) val)
  (define-instance (SymanticsDB PTypeDB)
    (define (int x)
      (PDB (constant-at (into x))))
    (define (add e1 e2)
      (PDB (fn (h)
           (fold str:concat "" (make-list "(" (unPDB e1 h) " + " (unPDB e2 h) ")")))))
    (define z
      (PDB (fn (h) (str:concat "x" (into (- h 1))))))
    (define (s v)
      (PDB (fn (h) (unPDB v (- h 1)))))
    (define (lam e)
      (PDB (fn (h)
           (let ((x (str:concat "x" (into h))))
             (fold str:concat "" (make-list "(\\" x " -> " (unPDB e (+ 1 h)) ")"))))))
    (define (app e1 e2)
      (PDB (fn (h)
           (fold str:concat "" (make-list "(" (unPDB e1 h) " " (unPDB e2 h) ")"))))))
  (define (view e)
    (unPDB e 0))
  ;; DEMO: (view td1)  ;; => "(1 + 2)"
  ;; DEMO: (view td2o) ;; => "(\x0 -> (x0 + x-1))" ; can print open terms just fine!
  ;; DEMO: (view td3)  ;; => "(\x0 -> ((x0 1) + 2))"
  )

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

;;; 3.5: explores relationship between 3.4 and the GADT embedding, which again we have to skip

;;; 4: "real fun" -- there are a lot of little projects here, and comparatively little code. i'll probably stop here.
