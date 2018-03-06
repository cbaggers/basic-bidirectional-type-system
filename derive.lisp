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

(defclass typed () ())

;; type Expr =
;;   | Var of Ident // x
;;   | Lit of int // n
;;   | Lam of Ident * Expr // \x. e
;;   | App of Expr * Expr // e e'

;; type TypedExpr =
;;   | Var of Ident * Type // x
;;   | Lit of int // n
;;   | Lam of Ident * Type * TypedExpr // \x. e
;;   | App of TypedExpr * TypedExpr // e e'

(defclass var-form (typed)
  ((ident :initarg :ident)
   (type :initarg :type)))

(defclass literal-form (typed)
  ((val :initarg :val)
   (type :initarg :type)))

(defclass lambda-form (typed)
  ((ident :initarg :ident)
   (type :initarg :type)
   (typed-expr :initarg :typed-expr)))

(defclass app-form (typed)
  ((typed-expr-a :initarg :typed-expr-a)
   (typed-expr-b :initarg :typed-expr-b)))

(defclass rec-form (typed)
  ((name :initarg :name)
   (type :initarg :type)
   (typed-expr :initarg :typed-expr)))

(defclass the-form (typed)
  ((type :initarg :type)
   (typed-expr :initarg :typed-expr)))

(defclass if-form (typed)
  ((typed-expr-test :initarg :typed-expr-test)
   (typed-expr-then :initarg :typed-expr-then)
   (typed-expr-else :initarg :typed-expr-else)))

(defclass let-form (typed)
  ((var-name :initarg :var-name)
   (var-type :initarg :var-type)
   (var-typed-expr :initarg :var-type)
   (body-typed-expr :initarg :body-typed-expr)))

(defclass type-lam ()
  ((ident :initarg :ident)
   (typed-expr :initarg :typed-expr)))

(defclass type-app ()
  ((typed-expr :initarg :typed-expr)
   (type :initarg :type)))

(defun make-type-lam (ident typed-expr)
  (make-instance 'type-lam
                 :ident ident
                 :typed-expr typed-expr))

(defun make-type-app (typed-expr type)
  (make-instance 'type-app
                 :typed-expr typed-expr
                 :type type))

(defun make-let (var-name var-type var-typed-expr body-typed-expr)
  (make-instance 'let-form
                 :var-name var-name
                 :var-type var-type
                 :var-type var-typed-expr
                 :body-typed-expr body-typed-expr))

(defun make-if (test then else)
  (make-instance 'if-form
                 :typed-expr-test test
                 :typed-expr-then then
                 :typed-expr-else else))

(defun make-var (ident type)
  (make-instance 'var-form :ident ident :type type))

(defun make-literal (val type)
  (make-instance 'literal-form :val val :type type))

(defun make-lambda (ident type typed-expr)
  (make-instance 'lambda-form :ident ident :type type :typed-expr typed-expr))

(defun make-app (typed-expr-a typed-expr-b)
  (make-instance 'app-form
                 :typed-expr-a typed-expr-a
                 :typed-expr-b typed-expr-b))

(defun make-rec (name type typed-expr)
  (make-instance 'rec-form
                 :name name
                 :type type
                 :typed-expr typed-expr))

(defun make-the (type typed-expr)
  (make-instance 'the-form
                 :type type
                 :typed-expr typed-expr))


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
    (`(uvar ,_ ,_)
      (list type))
    ;;
    (`(forall ,_ ,fa-type)
      (unification-vars fa-type))
    ;; tvar, integer, boolean
    (otherwise nil)))

(defun type-subst (name sub-type type)
  (match type
    ('integer type)
    ('boolean type)
    (`(function (,orig-arg) ,orig-body)
      (let ((arg (type-subst name sub-type orig-arg))
            (body (type-subst name sub-type orig-body)))
        `(function (,arg) ,body)))
    (`(uvar ,@_) type)
    (`(tvar ,tname)
      (if (equal name tname)
          sub-type
          type))
    (`(forall ,fa-name ,fa-type)
      (if (equal fa-name name)
          type
          (let ((new-type (type-subst name sub-type fa-type)))
            `(forall ,fa-name ,new-type))))))

(defun instantiate (expr type)
  (match type
    (`(forall ,fa-name ,fa-type)
      (let ((v (make-uvar)))
        (destructuring-bind (new-expr new-type)
            (instantiate expr (type-subst fa-name v fa-type))
          (cons (make-type-app new-expr v)
                new-type))))
    (otherwise (cons expr type))))

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

(defun typelams (names typed-expr)
  (if names
      (make-type-lam (first names) (typelams (rest names) typed-expr))
      typed-expr))

(defun generalize (typed-expr type)
  (let* ((z-type (zonk type))
         (uvars (unification-vars z-type))
         (names (fresh-tvar-names (length uvars))))
    (loop :for uvar :in uvars
       :for name :in names :do
       (match uvar
         (`(uvar ,_ ,_)
           (setf (third uvar) (make-tvar name)))
         (otherwise (error "generalize bug"))))
    (cons (zonk-expr (typelams names typed-expr))
          (zonk (foralls names type)))))

(defun check-occurs (name-id-pair type)
  "Checks if a type variable (name) occurs in a type.
   Used to avoid making infinite types (remember that recusion case
   we hit)"
  (assert (not (find `(uvar ,@name-id-pair)
                     (unification-vars type)
                     :test #'equal))
          ()
          "Occurs check failed~%name-id-pair: ~a~%type: ~a"
          name-id-pair type))

;;---------------------------------------------

(defun zonk (type)
  (match type
    (`(function (,a) ,b) `(function (,(zonk a)) ,(zonk b)))
    (`(uvar ,_ ,utype) (or utype type))
    (`(tvar ,_) type)
    (`(forall ,name ,itype) (make-forall name (zonk itype)))
    (otherwise type)))

(defun zonk-expr (expr)
  (ematch expr
    ;;
    ((class var-form ident type)
     (make-var ident (zonk type)))
    ;;
    ((class literal-form val type)
     (make-var val (zonk type)))
    ;;
    ((class lambda-form ident type typed-expr)
     (make-lambda ident (zonk type) (zonk-expr typed-expr)))
    ;;
    ((class app-form typed-expr-a typed-expr-b)
     (make-app (zonk-expr typed-expr-a) (zonk-expr typed-expr-b)))
    ;;
    ((class type-lam ident typed-expr)
     (make-type-lam ident (zonk-expr typed-expr)))
    ;;
    ((class type-app typed-expr type)
     (make-type-app (zonk-expr typed-expr) (zonk type)))))

(defun type-of-typed-expr (typed-expr context)
  (ematch typed-expr
    ;; technically we could just used the type from the var-form.
    ;; its a bit unusual to do this the way we have, but meh.
    ((class var-form ident)
     (lookup ident context))
    ((class literal-form type)
     type)
    ((class lambda-form ident type typed-expr)
     (let ((type-of-body
            (type-of-typed-expr typed-expr (add-binding ident type context))))
       `(function (,type) ,type-of-body)))
    ((class app-form typed-expr-a)
     (match (type-of-typed-expr typed-expr-a context)
       (`(function (,_) ,body-type)
         body-type)
       (otherwise (error "type-of-typed-expr: applying a non-function"))))
    ((class type-lam ident typed-expr)
     (make-forall ident (type-of-typed-expr typed-expr context)))
    ((class type-app typed-expr type)
     (match (type-of-typed-expr typed-expr context)
       (`(forall ,name ,fa-type)
         (type-subst name type fa-type))
       (otherwise (error "type-of-typed-expr: type-applying a non-forall"))))
    ((class let-form var-name var-type body-typed-expr)
     (type-of-typed-expr body-typed-expr
                         (add-binding var-name var-type context)))))

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
        (`((uvar ,name ,id)
           ,type2)
          (check-occurs (list name id) type2)
          (setf (third zonk-a) type2))
        ;;
        (`(,type1
           (uvar ,name ,id))
          (check-occurs (list name id) type1)
          (setf (third zonk-b) type1))
        (otherwise (error "Can't unify ~a and ~a" zonk-a zonk-b))))))

;; infer & check could return 2 vals new expression and type

(defun infer (context expression)
  (match expression
    ;;
    ;; literals
    (t (cons (make-literal t 'boolean) 'boolean))
    (nil (cons (make-literal nil 'boolean) 'boolean))
    ((type integer)
     (cons (make-literal expression 'integer) 'integer))
    ;;
    ;; variables
    ((type symbol)
     (let ((type (lookup expression context)))
       (if type
           (instantiate (make-var expression type) type)
           (error "Not in scope: ~a" expression))))
    ;;
    ;; application (t-app)
    (`(funcall ,expr0 ,expr1)
      (let* ((arg-type (make-uvar))
             (ret-type (make-uvar))
             (texpr0 (check context expr0 `(function (,arg-type) ,ret-type)))
             (texpr1 (check context expr1 arg-type)))
        (cons (make-app texpr0 texpr1)
              (zonk ret-type))))
    ;;
    ;; lambda
    (`(lambda (,a) ,b)
      (let* ((arg-type (make-uvar)))
        (destructuring-bind (typed-expr . ret-type)
            (infer (add-binding a arg-type context) b)
          (cons (make-lambda a (zonk arg-type) typed-expr)
                `(function (,(zonk arg-type)) ,(zonk ret-type))))))
    ;;
    ;; recursion
    (`(rec ,name ,type ,body-expr)
      (let* ((body-context (add-binding name type context))
             (typed-body (check body-context body-expr type)))
        (cons (make-rec name type typed-body)
              (zonk type))))
    ;;
    ;; Conditionals
    (`(if ,test ,then ,else)
      (let ((typed-test-expr (check context test 'boolean)))
        (destructuring-bind (typed-then-expr . then-type)
            (infer context then)
          (let ((typed-else-expr (check context else then-type)))
            (cons (make-if typed-test-expr
                           typed-then-expr
                           typed-else-expr)
                  (zonk then-type))))))
    ;;
    ;; type annotation
    (`(the ,type ,expression)
      (let ((typed-expr (check context expression type)))
        (cons typed-expr
              (zonk type))))
    ;;
    ;; let
    (`(let1 (,name ,expr) ,body)
      (destructuring-bind (typed-arg-expr . arg-type)
          (infer context expr)
        (let* ((body-context (add-binding name arg-type context)))
          (destructuring-bind (typed-body-expr . body-type)
              (infer body-context body)
            (cons (make-let name
                            arg-type
                            typed-arg-expr
                            typed-body-expr)
                  body-type)))))
    ;;
    (otherwise (error "Could not infer a type for: ~a" expression))))

(defun infer2 (expression)
  (destructuring-bind (expr . type)
      (infer (make-context) expression)
    (cons (zonk-expr expr)
          (zonk type))))


(defun check (context expression type)
  (destructuring-bind (typed-expr . inferred-type) (infer context expression)
    (unify inferred-type type)
    typed-expr))

;;---------------------------------------------

(defparameter test0 (infer (make-context) '(lambda (x) x)))
(defparameter test1 (infer (make-context) '(funcall (lambda (x) x) 1)))
(defparameter test2
  (destructuring-bind (typed-expr . type)

      (infer (make-context) '(lambda (a)
                              (lambda (b)
                                (funcall (funcall a b)
                                         b))))

    (let ((tmp (generalize typed-expr type)))
      (list (car tmp)
            (cdr tmp)))))
;; TODO:
;;
;; add depth to uvars then when generalizing only forall things >= our depth.
;; When you unify with another type you will need to fix up it's types to be
;; at least our depth too.
