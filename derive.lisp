(in-package #:derive)
(in-readtable :derive.readtable)

;;---------------------------------------------

(defclass context ()
  ((bindings :initarg :bindings :initform nil :reader bindings)))

;;---------------------------------------------

(defun make-context (&optional bindings)
  (make-instance 'context :bindings bindings))

(defun add-binding (name type context)
  (make-context (cons (cons name type)
                      (bindings context))))

(defun lookup (name context)
  (or (cdr (find name (bindings context) :key #'car))
      (error "Var ~a is not in scope" name)))

;;---------------------------------------------

;; infer & check could return 2 vals new expression and type

(defun infer (context expression)
  (match expression
    (t 'boolean)
    (nil 'boolean)
    ((type symbol) (lookup expression context))
    ((type integer) 'integer)
    (`(funcall ,expr0 ,expr1)
      ;; t-app
      (let ((type0 (infer context expr0)))
        (match type0
          (`(function (,a) ,b)
            (check context expr1 a)
            b)
          (otherwise (error "expression ~a was meant to be a function"
                            expr0)))))
    (`(rec ,name ,type ,body-expr)
      (let ((body-context (add-binding name type context)))
        (check body-context body-expr type)
        type))
    (`(if ,test ,then ,else)
      (check context test 'boolean)
      (let ((let-type (infer context then)))
        (check context else let-type)
        let-type))
    (`(the ,type ,expression)
      (check context expression type)
      type)
    (`(let1 (,name ,expr) ,body)
      (let* ((τ (infer context expr))
             (body-context (add-binding name τ context)))
        (infer body-context body)))
    (otherwise (error "Could not infer a type for: ~a" expression))))


(defun check (context expression type)
  (match expression
    (`(lambda (,l-arg) ,l-expr)
      ;; t-fn
      (match type
        (`(function (,a) ,b)
          (let ((body-context (add-binding l-arg a context)))
            (check body-context l-expr b)))
        (otherwise
         (error "Lambda must have a function type: ~a ~a"
                expression type))))
    (`(if ,test ,then ,else)
      (check context test 'boolean)
      (check context then type)
      (check context else type)
      type)
    (`(let1 (,name ,expr) ,body)
      (let* ((τ (infer context expr))
             (body-context (add-binding name τ context)))
        (check body-context body type)))
    (otherwise
     ;; t-sub
     (let ((inferred (infer context expression)))
       ;; if equal was a subtypep equivalent this would allow subtyping!
       ;; subtypep with return a function name that will convert from original
       ;; type to subtype. Normally #'identity, but could be something else.
       ;;        ↓↓
       (assert (equal inferred type))))))

;;---------------------------------------------
