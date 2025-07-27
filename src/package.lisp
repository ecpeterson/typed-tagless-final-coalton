;;;; package.lisp
;;;;
;;;; defpackage for typed-tagless-final playground

(defpackage #:typed-tagless-final
  (:use
   #:coalton
   #:coalton-prelude)
  (:local-nicknames 
   (#:str  #:coalton-library/string)
   (#:list #:coalton-library/list)
   ;(#:vec  #:coalton-library/vector)
   ;(#:math #:coalton-library/math)
   )
  )
