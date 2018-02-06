(in-package #:derive)
(in-readtable :derive.readtable)

;;---------------------------------------------

(defvar *uvar-id* -1)

(defclass context ()
  ((bindings :initarg :bindings :initform nil :reader bindings)))

;;---------------------------------------------

(defun make-context (&optional bindings)
  (make-instance 'context :bindings bindings))

(defun make-uvar ()
  `(uvar ,(incf *uvar-id*) nil))

(defun add-binding (name type context)
  (make-context (cons (cons name type)
                      (bindings context))))

(defun lookup (name context)
  (or (cdr (find name (bindings context) :key #'car))
      (error "Var ~a is not in scope" name)))

;;---------------------------------------------

(defun zonk (type)
  (match type
    (`(function (,a) ,b) `(function (,(zonk a)) ,(zonk b)))
    (`(uvar ,_ ,utype) (or utype type))
    (otherwise type)))

(defun unify (type-a type-b)
  ;; only used for side-effects
  (let ((zonk-a (zonk type-a))
        (zonk-b (zonk type-b)))
    (unless (or (equal zonk-a zonk-b)
                (and (eq zonk-a 'integer) (eq zonk-b 'integer))
                (and (eq zonk-a 'boolean) (eq zonk-b 'boolean)))
      (match (list zonk-a zonk-b)
        (`((function (,a0) ,b0)
           (function (,a1) ,b1))
          (unify a0 a1)
          (unify b0 b1))
        (`((uvar ,_ ,_) ,type2) (setf (third zonk-a) type2))
        (`(,type1 (uvar ,_ ,_)) (setf (third zonk-b) type1))
        (otherwise (error "Can't unify ~a and ~a" zonk-a zonk-b))))))

;; infer & check could return 2 vals new expression and type

(defun infer (context expression)
  (match expression
    (t 'boolean)
    (nil 'boolean)
    ((type symbol) (lookup expression context))
    ((type integer) 'integer)
    (`(funcall ,expr0 ,expr1)
      ;; t-app
      (let* ((arg-type (make-uvar))
             (ret-type (make-uvar)))
        (check context expr0 `(function (,arg-type) ,ret-type))
        (check context expr1 arg-type)
        (zonk ret-type)))
    (`(lambda (,a) ,b)
      (let* ((arg-type (make-uvar))
             (ret-type (infer (add-binding a arg-type context) b)))
        `(function (,(zonk arg-type)) ,(zonk ret-type))))
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
  (let ((expr-type (infer context expression)))
    (unify expr-type type)
    nil))

;;---------------------------------------------

(defvar test0 (infer (make-context) '(lambda (x) x)))
(defvar test1 (infer (make-context) '(funcall (lambda (x) x) 1)))

;; add depth to uvars then when generalizing only forall things >= our depth
;; also ask olle about occurs, somethign about acessing vars and then instantiating fresh uvars for outermost foralls
