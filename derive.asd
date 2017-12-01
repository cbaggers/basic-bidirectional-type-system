;;;; derive.asd

(asdf:defsystem #:derive
  :description "Describe derive here"
  :author "Your Name <your.name@example.com>"
  :license "Specify license here"
  :depends-on (:fn
			   #:optima
			   #:fare-quasiquote-extras
			   :fiveam)
  :serial t
  :components ((:file "package")
			   (:file "readtables")
               (:file "derive")))
