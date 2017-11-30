;;;; package.lisp

(uiop:define-package #:derive
    (:use #:cl :optima :named-readtables)
  (:import-from :alexandria :with-gensyms))
