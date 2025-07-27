;;;; typed-tagless-final.asd
;;;;
;;;; 

(asdf:defsystem #:typed-tagless-final
  :description "Reproduces examples from https://okmij.org/ftp/tagless-final/course/lecture.pdf"
  :author "Eric Peterson <peterson.eric.c@gmail.com>"
  :version (:read-file-form "VERSION.txt")
  :license "MIT (See LICENSE.md)"
  :pathname "src/"
  :depends-on (#:coalton)
  :serial t
  :components ((:file "package")
               (:file "ttf")))
