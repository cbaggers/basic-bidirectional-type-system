(in-package #:derive)
(in-readtable :derive.readtable)

;;---------------------------------------------

;; uvar = unification variable
;; tvar = (polymorphic) type variable. Always bound by a forall

;;---------------------------------------------

(defvar *uvar-id* -1)
(defvar *tvar-id* -1)

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

(defun make-uvar ()
  `(uvar ,(incf *uvar-id*) nil))

(defun make-forall (name type)
  `(forall ,name ,type))

(defun make-tvar (name)
  `(tvar ,name))

(defun fresh-tvar-name ()
  (format-symbol :derive "TVAR~a" (incf *tvar-id*)))

(defun fresh-tvar-names (count)
  (loop :for i :below count :collect (fresh-tvar-name)))

;;---------------------------------------------

(defun foralls (names type)
  (if names
      (make-forall (first names) (foralls (rest names) type))
      type))

(defun unification-vars (type)
  (match type
    ;;
    (`(function (,arg) ,res)
      (remove-duplicates
       (union (unification-vars arg)
              (unification-vars res))
       :test #'equal))
    ;;
    (`(uvar ,name ,_)
      (list name))
    ;; tvar, integer, boolean
    (otherwise nil)))

(defun subst-uvars (type hash-table)
  (match type
    ('integer type)
    ('boolean type)
    (`(function (,arg) ,res)
      `(function (,(subst-uvars arg hash-table))
                 ,(subst-uvars res hash-table)))
    (`(uvar ,name ,_)
      (or (gethash name hash-table)
          type))
    (`(tvar ,_) type)
    (`(forall ,name ,fa-type)
      (make-forall name (subst-uvars fa-type hash-table)))
    (otherwise (error "subst-uvars did not recognise ~a" type))))

(defun generalize (type)
  (let* ((z-type (zonk type))
         (uvars (unification-vars z-type))
         (names (fresh-tvar-names (length uvars)))
         (tvars (mapcar #'make-tvar names))
         (paired (mapcar #'cons uvars tvars))
         (table (alist-hash-table paired)))
    (foralls names (subst-uvars z-type table))))

(defun check-occurs (name type)
  (assert (not (find name (unification-vars type))) ()
          "Occurs check failed~%name: ~a~%type: ~a"
          name type))

;;---------------------------------------------

(defun zonk (type)
  (match type
    (`(function (,a) ,b) `(function (,(zonk a)) ,(zonk b)))
    (`(uvar ,_ ,utype) (or utype type))
    (`(tvar ,_) type)
    (`(forall ,name ,itype) (make-forall name (zonk itype)))
    (otherwise type)))

(defun unify (type-a type-b)
  ;; only used for side-effects
  (let ((zonk-a (zonk type-a))
        (zonk-b (zonk type-b)))
    (unless (or (equal zonk-a zonk-b)
                (and (eq zonk-a 'integer) (eq zonk-b 'integer))
                (and (eq zonk-a 'boolean) (eq zonk-b 'boolean)))
      (match (list zonk-a zonk-b)
        ;;
        (`((function (,a0) ,b0)
           (function (,a1) ,b1))
          (unify a0 a1)
          (unify b0 b1))
        ;;
        (`((forall ,_ ,type1)
           (forall ,_ ,type2))
          (unify type1 type2))
        ;;
        (`((uvar ,name ,type)
           ,type2)
          (check-occurs name type2)
          (setf (third zonk-a) type2))
        ;;
        (`(,type1
           (uvar ,name ,type))
          (check-occurs name type1)
          (setf (third zonk-b) type1))
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
(defvar test2 (generalize (infer (make-context) '(lambda (a) a))))
;; TODO:
;;
;; add depth to uvars then when generalizing only forall things >= our depth.
;; When you unify with another type you will need to fix up it's types to be
;; at least our depth too.
