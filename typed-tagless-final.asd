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
               (:file "ttf2p1-3")
               (:file "ttf2p4")
               (:file "ttf3p1")
               ;; 3.2: typed initial embedding via GADTs, which IIUC coalton doesn't have
               (:file "ttf3p3")
               (:file "ttf3p4")
               ;; 3.5: explores relationship between 3.4 and the GADT embedding, which again we have to skip
               ;; 4: "real fun" -- there are a lot of little projects here, and comparatively little code. i'll probably stop here.
               ;;    ... but the one about evaluation order looks neat!
               ))
