;; types
;; integer
;; (function (arg-type) expr-type)

;; expressions
;; x
;; 1
;; (funcall fn arg)
;; (lambda (x) y)


(define-check-system my-system ())

(define-fact my-system ()
  ())

(define-rule let my-system
  :check (lambda (context expression)
		   ..)
  :infer #'let-infer)
