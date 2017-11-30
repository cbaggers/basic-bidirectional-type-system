(in-package #:derive)

;;---------------------------------------------

(defmacro fails (x)
  `(assert (handler-case (progn ,x nil)
			 (error () t))
		   ()
		   "~a didnt fail" ',x))

;;---------------------------------------------
