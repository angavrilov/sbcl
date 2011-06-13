;;;; This file implements the constraint propagation phase of the
;;;; compiler, which uses global flow analysis to obtain dynamic type
;;;; information.

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

;;; TODO:
;;;
;;; -- documentation
;;;
;;; -- MV-BIND, :ASSIGNMENT
;;;
;;; Note: The functions in this file that accept constraint sets are
;;; actually receiving the constraint sets associated with nodes,
;;; blocks, and lambda-vars.  It might be make CP easier to understand
;;; and work on if these functions traded in nodes, blocks, and
;;; lambda-vars directly.

;;; Problems:
;;;
;;; -- Constraint propagation badly interacts with bottom-up type
;;; inference. Consider
;;;
;;; (defun foo (n &aux (i 42))
;;;   (declare (optimize speed))
;;;   (declare (fixnum n)
;;;            #+nil (type (integer 0) i))
;;;   (tagbody
;;;      (setq i 0)
;;;    :loop
;;;      (when (>= i n) (go :exit))
;;;      (setq i (1+ i))
;;;      (go :loop)
;;;    :exit))
;;;
;;; In this case CP cannot even infer that I is of class INTEGER.
;;;
;;; -- In the above example if we place the check after SETQ, CP will
;;; fail to infer (< I FIXNUM): it does not understand that this
;;; constraint follows from (TYPEP I (INTEGER 0 0)).

(in-package "SB!C")

;;; *CONSTRAINT-UNIVERSE* gets bound in IR1-PHASES to a fresh,
;;; zero-length, non-zero-total-size vector-with-fill-pointer.
(declaim (type (and vector (not simple-vector)) *constraint-universe*))
(defvar *constraint-universe*)

(deftype constraint-y () '(or ctype lvar lambda-var constant))

(defstruct (constraint
            (:include sset-element)
            (:constructor make-constraint (number kind x y not-p))
            (:copier nil))
  ;; the kind of constraint we have:
  ;;
  ;; TYPEP
  ;;     X is a LAMBDA-VAR and Y is a CTYPE. The value of X is
  ;;     constrained to be of type Y.
  ;;
  ;; > or <
  ;;     X is a lambda-var and Y is a CTYPE. The relation holds
  ;;     between X and some object of type Y.
  ;;
  ;; EQL
  ;;     X is a LAMBDA-VAR and Y is a LVAR, a LAMBDA-VAR or a CONSTANT.
  ;;     The relation is asserted to hold.
  (kind nil :type (member typep < > eql))
  ;; The operands to the relation.
  (x nil :type lambda-var)
  (y nil :type constraint-y)
  ;; If true, negates the sense of the constraint, so the relation
  ;; does *not* hold.
  (not-p nil :type boolean))

;;; Historically, CMUCL and SBCL have used a sparse set implementation
;;; for which most operations are O(n) (see sset.lisp), but at the
;;; cost of at least a full word of pointer for each constraint set
;;; element.  Using bit-vectors instead of pointer structures saves a
;;; lot of space and thus GC time (particularly on 64-bit machines),
;;; and saves time on copy, union, intersection, and difference
;;; operations; but makes iteration slower.  Circa September 2008,
;;; switching to bit-vectors gave a modest (5-10%) improvement in real
;;; compile time for most Lisp systems, and as much as 20-30% for some
;;; particularly CP-dependent systems.

;;; It's bad to leave commented code in files, but if some clever
;;; person comes along and makes SSETs better than bit-vectors as sets
;;; for constraint propagation, or if bit-vectors on some XC host
;;; really lose compared to SSETs, here's the conset API as a wrapper
;;; around SSETs:
(progn
  (deftype conset () 'sset)
  (declaim (ftype (sfunction (conset) boolean) conset-empty))
  (declaim (ftype (sfunction (conset) conset) copy-conset))
  (declaim (ftype (sfunction (constraint conset) boolean) conset-member))
  (declaim (ftype (sfunction (constraint conset) boolean) conset-adjoin))
  (declaim (ftype (sfunction (conset conset) boolean) conset=))
  (declaim (ftype (sfunction (conset conset) (values)) conset-union))
  (declaim (ftype (sfunction (conset conset) (values)) conset-intersection))
  (declaim (ftype (sfunction (conset conset) (values)) conset-difference))
  (declaim (inline make-conset conset-empty copy-conset
                   conset-member conset-adjoin conset=
                   conset-union conset-intersection conset-difference))
  (defun make-conset () (make-sset))
  (defmacro do-conset-elements ((constraint conset &optional result) &body body)
    `(do-sset-elements (,constraint ,conset ,result) ,@body))
  (defmacro do-conset-intersection
      ((constraint conset1 conset2 &optional result) &body body)
    `(do-sset-intersection (,constraint ,conset1 ,conset2 ,result)
       ,@body))
  (defun conset-empty (conset) (sset-empty conset))
  (defun copy-conset (conset) (copy-sset conset))
  (defun conset-member (constraint conset) (sset-member constraint conset))
  (defun conset-adjoin (constraint conset) (sset-adjoin constraint conset))
  (defun conset= (conset1 conset2) (sset= conset1 conset2))
  ;; Note: CP doesn't ever care whether union, intersection, and
  ;; difference change the first set.  (This is an important degree of
  ;; freedom, since some ways of implementing sets lose a great deal
  ;; when these operations are required to track changes.)
  (defun conset-union (conset1 conset2)
    (sset-union conset1 conset2) (values))
  (defun conset-intersection (conset1 conset2)
    (sset-intersection conset1 conset2) (values))
  (defun conset-difference (conset1 conset2)
    (sset-difference conset1 conset2) (values)))

#+nil
(locally
    ;; This is performance critical for the compiler, and benefits
    ;; from the following declarations.  Probably you'll want to
    ;; disable these declarations when debugging consets.
    (declare #-sb-xc-host (optimize (speed 3) (safety 0) (space 0)))
  (declaim (inline %constraint-number))
  (defun %constraint-number (constraint)
    (sset-element-number constraint))
  (defstruct (conset
              (:constructor make-conset ())
              (:copier %copy-conset))
    (vector (make-array
             ;; FIXME: make POWER-OF-TWO-CEILING available earlier?
             (ash 1 (integer-length (1- (length *constraint-universe*))))
             :element-type 'bit :initial-element 0)
            :type simple-bit-vector)
    ;; Bit-vectors win over lightweight hashes for copy, union,
    ;; intersection, difference, but lose for iteration if you iterate
    ;; over the whole vector.  Tracking extrema helps a bit.
    (min 0 :type fixnum)
    (max 0 :type fixnum))

  (defmacro do-conset-elements ((constraint conset &optional result) &body body)
    (with-unique-names (vector index start end
                               #-sb-xc-host ignore
                               #-sb-xc-host constraint-universe-end)
      (let* ((constraint-universe #+sb-xc-host '*constraint-universe*
                                  #-sb-xc-host (sb!xc:gensym "UNIVERSE"))
             (with-array-data
                #+sb-xc-host '(progn)
                #-sb-xc-host `(with-array-data
                                  ((,constraint-universe *constraint-universe*)
                                   (,ignore 0) (,constraint-universe-end nil)
                                   :check-fill-pointer t)
                                (declare (ignore ,ignore))
                                (aver (<= ,end ,constraint-universe-end)))))
        `(let* ((,vector (conset-vector ,conset))
               (,start (conset-min ,conset))
               (,end (min (conset-max ,conset) (length ,vector))))
          (,@with-array-data
            (do ((,index ,start (1+ ,index))) ((>= ,index ,end) ,result)
              (when (plusp (sbit ,vector ,index))
                (let ((,constraint (elt ,constraint-universe ,index)))
                  ,@body))))))))

  ;; Oddly, iterating just between the maximum of the two sets' minima
  ;; and the minimum of the sets' maxima slowed down CP.
  (defmacro do-conset-intersection
      ((constraint conset1 conset2 &optional result) &body body)
    `(do-conset-elements (,constraint ,conset1 ,result)
       (when (conset-member ,constraint ,conset2)
         ,@body)))

  (defun conset-empty (conset)
    (or (= (conset-min conset) (conset-max conset))
        ;; TODO: I bet FIND on bit-vectors can be optimized, if it
        ;; isn't.
        (not (find 1 (conset-vector conset)
                   :start (conset-min conset)
                   ;; By inspection, supplying :END here breaks the
                   ;; build with a "full call to
                   ;; DATA-VECTOR-REF-WITH-OFFSET" in the
                   ;; cross-compiler.  If that should change, add
                   ;; :end (conset-max conset)
                   ))))

  (defun copy-conset (conset)
    (let ((ret (%copy-conset conset)))
      (setf (conset-vector ret) (copy-seq (conset-vector conset)))
      ret))

  (defun %conset-grow (conset new-size)
    (declare (type index new-size))
    (setf (conset-vector conset)
          (replace (the simple-bit-vector
                     (make-array
                      (ash 1 (integer-length (1- new-size)))
                      :element-type 'bit
                      :initial-element 0))
                   (the simple-bit-vector
                     (conset-vector conset)))))

  (declaim (inline conset-grow))
  (defun conset-grow (conset new-size)
    (declare (type index new-size))
    (when (< (length (conset-vector conset)) new-size)
      (%conset-grow conset new-size))
    (values))

  (defun conset-member (constraint conset)
    (let ((number (%constraint-number constraint))
          (vector (conset-vector conset)))
      (when (< number (length vector))
        (plusp (sbit vector number)))))

  (defun conset-adjoin (constraint conset)
    (prog1
      (not (conset-member constraint conset))
      (let ((number (%constraint-number constraint)))
        (conset-grow conset (1+ number))
        (setf (sbit (conset-vector conset) number) 1)
        (setf (conset-min conset) (min number (conset-min conset)))
        (when (>= number (conset-max conset))
          (setf (conset-max conset) (1+ number))))))

  (defun conset= (conset1 conset2)
    (let* ((vector1 (conset-vector conset1))
           (vector2 (conset-vector conset2))
           (length1 (length vector1))
           (length2 (length vector2)))
      (if (= length1 length2)
          ;; When the lengths are the same, we can rely on EQUAL being
          ;; nicely optimized on bit-vectors.
          (equal vector1 vector2)
          (multiple-value-bind (shorter longer)
              (if (< length1 length2)
                  (values vector1 vector2)
                  (values vector2 vector1))
            ;; FIXME: make MISMATCH fast on bit-vectors.
            (dotimes (index (length shorter))
              (when (/= (sbit vector1 index) (sbit vector2 index))
                (return-from conset= nil)))
            (if (find 1 longer :start (length shorter))
                nil
                t)))))

  (macrolet
      ((defconsetop (name bit-op)
           `(defun ,name (conset-1 conset-2)
              (declare (optimize (speed 3) (safety 0)))
              (let* ((size-1 (length (conset-vector conset-1)))
                     (size-2 (length (conset-vector conset-2)))
                     (new-size (max size-1 size-2)))
                (conset-grow conset-1 new-size)
                (conset-grow conset-2 new-size))
              (let ((vector1 (conset-vector conset-1))
                    (vector2 (conset-vector conset-2)))
                (declare (simple-bit-vector vector1 vector2))
                (setf (conset-vector conset-1) (,bit-op vector1 vector2 t))
                ;; Update the extrema.
                ,(ecase name
                   ((conset-union)
                    `(setf (conset-min conset-1)
                           (min (conset-min conset-1)
                                (conset-min conset-2))
                           (conset-max conset-1)
                           (max (conset-max conset-1)
                                (conset-max conset-2))))
                   ((conset-intersection)
                    `(let ((start (max (conset-min conset-1)
                                       (conset-min conset-2)))
                           (end (min (conset-max conset-1)
                                     (conset-max conset-2))))
                       (setf (conset-min conset-1)
                             (if (> start end)
                                 0
                                 (or (position 1 (conset-vector conset-1)
                                               :start start :end end)
                                     0))
                             (conset-max conset-1)
                             (if (> start end)
                                 0
                                 (let ((position
                                        (position
                                         1 (conset-vector conset-1)
                                         :start start :end end :from-end t)))
                                   (if position
                                       (1+ position)
                                       0))))))
                   ((conset-difference)
                    `(setf (conset-min conset-1)
                           (or (position 1 (conset-vector conset-1)
                                         :start (conset-min conset-1)
                                         :end (conset-max conset-1))
                               0)
                           (conset-max conset-1)
                           (let ((position
                                  (position
                                   1 (conset-vector conset-1)
                                   :start (conset-min conset-1)
                                   :end (conset-max conset-1)
                                   :from-end t)))
                             (if position
                                 (1+ position)
                                 0))))))
              (values))))
    (defconsetop conset-union bit-ior)
    (defconsetop conset-intersection bit-and)
    (defconsetop conset-difference bit-andc2)))

;; Specialised constraint set representation for blocks
;;
;; LAMBDA-VARs and CBLOCKs both have sets of constraints; however,
;; the design constraints are very different.
;;
;; LAMBDA-VARs need to be able to FIND-CONSTRAINT, and to make a
;; CBLOCK's constraint set forget everything about that LAMBDA-VAR.
;;
;; CBLOCKs are much more interesting. They need to:
;;  - Track LAMBDA-VARs that are known to be EQL
;;  - For each lambda var: EQL lvars (to map LVARs to LAMBDA-VARs)
;;  - Grab the set of constraints relevant to a given variable
;;    * sometimes, only those that are safe to propagate to EQL variables
;;      i.e. all but EQL lvars and constants
;;  - Forget everything about a given variable
;;  - take the intersection/union of CBLOCK consets, and other usual stuff
(locally (declare (optimize speed (safety 0)))
(deftype maybe (x)
  `(or null ,x))

(defstruct (block-conset
             (:constructor %make-block-conset)
             (:copier nil))
  ;; lambda-var set
  (vars (make-sset)       :type sset)
  ;; lambda-var -> var-info
  ;; NIL if dump block-conset
  (data (make-hash-table) :type (maybe hash-table)))

(defvar *heavy-consets* nil)

(declaim (inline make-block-conset))
(defun make-block-conset (&key vars data)
  (%make-block-conset :vars (or vars (make-sset))
                      :data (or data
                                (and *heavy-consets*
                                     (make-hash-table)))))

(defmacro do-block-conset-vars ((var info conset &optional result) &body body)
  (let ((_conset (gensym "BCONSET"))
        (_data   (gensym "DATA")))
    `(let* ((,_conset ,conset)
            (,_data  (block-conset-data ,_conset)))
       (do-sset-elements (,var (block-conset-vars ,_conset) ,result)
         (let ((,info (gethash ,var ,_data))
               (,var  ,var))
           (declare (type var-info ,info)
                    (type lambda-var ,var))
           ,@body)))))

(defstruct (eqv-class
             (:copier nil))
  (conset (make-sset) :type (maybe sset)) ; only nil when dead
  (class  (make-sset) :type (maybe sset)) ;  same
  ;; next pointer, to avoid backpatching
  (pointer nil        :type (maybe eqv-class))
  ;; used as a random mutable cell
  (info    nil))

(defun copy-eqv-class (class)
  (declare (type eqv-class class))
  (make-eqv-class :conset  (copy-sset (eqv-class-conset class))
                  :class   (copy-sset (eqv-class-class  class))
                  :pointer nil
                  :info    nil))

(declaim (inline eqv-class=))
(defun eqv-class= (class1 class2)
  (declare (type eqv-class class1 class2)
           (optimize speed (safety 0)))
  (and (sset= (eqv-class-conset class1) (eqv-class-conset class2))
       (sset= (eqv-class-class  class1) (eqv-class-class  class2))))

(declaim (inline eqv-class-union))
(defun eqv-class-union (eqv1 eqv2)
  (declare (type eqv-class eqv1 eqv2)
           (optimize speed (safety 0)))
  (sset-union (eqv-class-class  eqv1) (eqv-class-class  eqv2))
  (sset-union (eqv-class-conset eqv1) (eqv-class-conset eqv2))
  eqv1)

(defstruct (var-info
             (:constructor %make-var-info)
             (:copier nil))
  (self (missing-arg)     :type lambda-var :read-only t)
  ;; private consets
  (eql-lvars   nil        :type (maybe sset))
  (private     nil        :type (maybe sset))
  (%eqv-class  (make-eqv-class) :type eqv-class)
  ;; temporary ssets
  ;; eql-sset is
  ;;  nil usually
  ;;  a shared sset of eqv vars after stashed canonicalisation
  ;;   nil if alone in eqv class, t if non-singleton eqv after set intersection
  (eql-sset    nil        :type (or (maybe sset) (member nil t)))
  (constraints nil        :type (maybe sset)))

(defun make-var-info (&key self eql-lvars private %eqv-class eql-sset constraints)
  (declare (optimize speed (safety 0)))
  (assert self)
  (%make-var-info :self self
                  :eql-lvars eql-lvars
                  :private private
                  :%eqv-class (or %eqv-class
                                  (let ((class (make-eqv-class)))
                                    (sset-adjoin self (eqv-class-class class))
                                    class))
                  :eql-sset eql-sset
                  :constraints constraints))

(declaim (inline copy-sset-designator sset-designator-empty sset-designator-clear
                 sset-designator= sset-designator-intersection sset-designator-union))
(defun copy-sset-designator (sset)
  (declare (type (maybe sset) sset)
           (optimize speed (safety 0)))
  (and sset
       (copy-sset sset)))

(defun sset-designator-empty (sset)
  (declare (type (maybe sset) sset)
           (optimize speed (safety 0)))
  (or (null sset)
      (sset-empty sset)))

(defun sset-designator-clear (sset)
  (declare (type (maybe sset) sset)
           (optimize speed (safety 0)))
  (or (null sset)
      (sset-difference sset sset))
  sset)

(defun sset-designator= (x y)
  (declare (type (maybe sset) x y)
           (optimize speed (safety 0)))
  (let ((empty-x (sset-designator-empty x))
        (empty-y (sset-designator-empty y)))
    (cond ((and empty-x empty-y))
          ((and (not empty-x) (not empty-y))
           (sset= x y)))))

(defun sset-designator-intersection (x y)
  (declare (type (maybe sset) x y)
           (optimize speed (safety 0)))
  (let ((empty-x (sset-designator-empty x))
        (empty-y (sset-designator-empty y)))
    (cond (empty-x)
          (empty-y
           (sset-difference x x))
          (t
           (sset-intersection x y)))
    x))

(defun sset-designator-union (x y)
  (declare (type (maybe sset) x y)
           (optimize speed (safety 0)))
  (cond ((sset-designator-empty y)
         x)
        (x
         (sset-union x y)
         x)
        (t
         (copy-sset y))))

(declaim (ftype (sfunction (var-info) eqv-class) var-info-eqv-class))
(defun var-info-eqv-class (info)
  (declare (type var-info info)
           (optimize speed (safety 0)))
  (labels ((walk (class prev)
             (declare (type eqv-class class)
                      (type (maybe eqv-class) prev))
             (let ((next (eqv-class-pointer class)))
               (cond (next
                      (when prev
                        (setf (eqv-class-pointer prev) next
                              (eqv-class-conset  prev) nil
                              (eqv-class-class   prev) nil))
                      (walk next class))
                     (t class)))))
    (let* ((class (var-info-%eqv-class info))
           (root (walk class nil)))
      (unless (eq class root)
        (setf (var-info-%eqv-class info) root))
      root)))

(defun canonicalize-block-conset (bconset &optional stash-shared-ssets-p)
  (declare (type block-conset bconset)
           (optimize speed (safety 0)))
  (let ((data (block-conset-data bconset)))
    (do-sset-elements (var (block-conset-vars bconset) bconset)
      (let* ((info      (gethash var data))
             (eqv-class (var-info-eqv-class info)))
        (declare (type var-info info))
        (unless (eqv-class-info eqv-class)
          (setf (eqv-class-info eqv-class) var))
        (when stash-shared-ssets-p
          (setf (var-info-eql-sset    info) (eqv-class-class  eqv-class)
                (var-info-constraints info) (eqv-class-conset eqv-class)))))))

(defun clear-canonicalization-temporaries (bconset)
  (declare (type block-conset bconset)
           (optimize speed (safety 0)))
  (do-block-conset-vars (var info bconset bconset)
    (declare (ignore var))
    (let ((class (var-info-eqv-class info)))
      (setf (eqv-class-info      class) nil
            (var-info-constraints info) nil
            (var-info-eql-sset    info) nil))))

(declaim (inline copy-canonical-var-info))
(defun copy-canonical-var-info (info new-data)
  (declare (type var-info info)
           (type hash-table new-data)
           (optimize speed (safety 0)))
  (let* ((class (var-info-eqv-class info))
         (new-class (if (eql (var-info-self info) (eqv-class-info class))
                        (copy-eqv-class class)
                        (var-info-eqv-class (gethash (eqv-class-info class) new-data)))))
    (make-var-info
     :self      (var-info-self info)
     :eql-lvars (copy-sset-designator (var-info-eql-lvars info))
     :private   (copy-sset-designator (var-info-private info))
     :%eqv-class new-class)))

(defun copy-block-conset (bconset)
  (declare (type block-conset bconset)
           (optimize speed (safety 0)))
  (unless (block-conset-data bconset)
    (return-from copy-block-conset
      (%make-block-conset :vars (copy-sset (block-conset-vars bconset))
                          :data nil)))
  (canonicalize-block-conset bconset)
  (let* ((copy (make-block-conset :vars (copy-sset (block-conset-vars bconset))))
         (new-data (block-conset-data copy)))
    (do-block-conset-vars (var info bconset bconset)
      (setf (gethash var new-data) (copy-canonical-var-info info new-data)))
    (clear-canonicalization-temporaries bconset)
    copy))

(defun block-conset= (x y)
  (declare (type block-conset x y)
           (optimize speed (safety 0)))
  (and (sset= (block-conset-vars x) (block-conset-vars y))
       (or (null (block-conset-data x))
           (let ((x-data (block-conset-data x))
                 (y-data (block-conset-data y)))
             (canonicalize-block-conset x)
             (canonicalize-block-conset y)
             (prog1
                 (do-sset-elements (var (block-conset-vars x) t)
                   (let* ((x-info  (gethash var x-data))
                          (y-info  (gethash var y-data))
                          (x-class (var-info-eqv-class x-info))
                          (y-class (var-info-eqv-class y-info))
                          (x-root  (eql var (eqv-class-info x-class)))
                          (y-root  (eql var (eqv-class-info y-class))))
                     (declare (type var-info x-info y-info))
                     (unless (and (sset-designator= (var-info-eql-lvars x-info)
                                                    (var-info-eql-lvars y-info))
                                  (sset-designator= (var-info-private x-info)
                                                    (var-info-private y-info))
                                  (eql x-root y-root)
                                  (cond (x-root
                                         (eqv-class= x-class y-class))
                                        (t
                                         (eql (eqv-class-info x-class)
                                              (eqv-class-info y-class)))))
                       (return nil))))
               (clear-canonicalization-temporaries x)
               (clear-canonicalization-temporaries y))))))

;; x, y already canonicalised
(declaim (inline %block-conset-eql-intersection))
(defun %block-conset-eql-intersection (x y)
  (declare (type block-conset x y)
           (optimize speed (safety 0)))
  (let ((x-data (block-conset-data x))
        (y-data (block-conset-data y)))
    (do-block-conset-vars (var x-info x x)
      (when (var-info-constraints x-info)
        (let* ((y-info      (gethash var y-data))
               (constraints (let ((con (copy-sset (var-info-constraints
                                                   x-info))))
                              (sset-intersection con
                                                 (var-info-constraints y-info))
                              con))
               (eqv-class   (make-eqv-class :conset constraints))
               (class       (eqv-class-class eqv-class))
               (shared      nil))
          (setf (var-info-%eqv-class x-info) eqv-class)
          (do-sset-intersection (var2 (var-info-eql-sset x-info)
                                      (var-info-eql-sset y-info))
            (sset-adjoin var2 class)
            (let ((info (gethash var2 x-data)))
              (setf (var-info-constraints info) nil)
              (unless (eq var var2)
                (setf shared t)
                (setf (var-info-%eqv-class info) eqv-class
                      (var-info-eql-sset   info) t))))
          (setf (var-info-eql-sset x-info) shared))))))

(defun block-conset-intersection (x y)
  (declare (type block-conset x y)
           (optimize speed (safety 0)))
  ;; easy stuff
  (sset-intersection (block-conset-vars x)
                     (block-conset-vars y))
  (unless (block-conset-data x)
    (return-from block-conset-intersection x))
  (canonicalize-block-conset x t)
  (canonicalize-block-conset y t)
  ;; compute eql set intersection
  (%block-conset-eql-intersection x y)
  ;; var-wise intersections
  (let ((y-data    (block-conset-data y))
        (to-delete '()))
    (do-block-conset-vars (var x-info x)
      (let ((y-info (gethash var y-data)))
        (declare (type var-info y-info))
        (sset-designator-intersection (var-info-eql-lvars x-info)
                                      (var-info-eql-lvars y-info))
        (sset-designator-intersection (var-info-private x-info)
                                      (var-info-private y-info))
        (when (and (not (var-info-eql-sset x-info))
                   (sset-designator-empty (var-info-eql-lvars x-info))
                   (sset-designator-empty (var-info-private x-info))
                   (sset-designator-empty (eqv-class-conset (var-info-eqv-class x-info))))
          (push var to-delete))))
    (clear-canonicalization-temporaries x)
    (clear-canonicalization-temporaries y)
    (let ((vars (block-conset-vars x)))
      (dolist (var to-delete)
        (sset-delete var vars))))
  x)

(declaim (inline block-conset-empty))
(defun block-conset-empty (x)
  (declare (type block-conset x)
           (optimize speed (safety 0)))
  (sset-empty (block-conset-vars x)))

(defun ensure-block-conset-info (bconset var)
  (declare (type block-conset bconset)
           (type lambda-var var)
           (optimize speed (safety 0)))
  (let ((deltap (sset-adjoin var (block-conset-vars bconset)))
        (hash   (block-conset-data bconset)))
    (if (not deltap)
        (the var-info (gethash var hash))
        (let ((info (gethash var hash)))
          (cond (info
                 (sset-designator-clear (var-info-private info))
                 (sset-designator-clear (var-info-eql-lvars info))
                 (let ((eqv-class (make-eqv-class)))
                   (sset-adjoin var (eqv-class-class eqv-class))
                   (setf (var-info-%eqv-class info) eqv-class))
                 info)
                (t
                 (setf (gethash var hash) (make-var-info :self var))))))))

(defmacro do-eql-vars ((name (var bconset) &optional result) &body body)
  `(let ((.var. ,var))
     (do-sset-intersection (.con. (lambda-var-constraints .var.)
                                  (block-conset-vars ,bconset) ,result)
       (declare (type constraint .con.))
       (let ((,name (and (eql 'eql (constraint-kind .con.))
                         (not (constraint-not-p .con.))
                         (let ((x (constraint-x .con.))
                               (y (constraint-y .con.)))
                           (cond ((eql .var. x)
                                  y)
                                 ((eql .var. y)
                                  x))))))
         (when (and ,name
                    (lambda-var-p ,name))
           (let ((,name ,name))
             ,@body))))))

(defun inherit-constraints (vars source constraints)
  (declare (type list vars)
           (type lambda-var source)
           (type sset constraints))
  (collect ((to-merge))
    (do-sset-intersection (con (lambda-var-constraints source) constraints)
      (let ((y (constraint-y con)))
        (unless (or (lvar-p y)
                    (and (not (constraint-not-p con))
                         (or (constant-p y)
                             (lambda-var-p y))))
          (to-merge con))))
    (dolist (con (to-merge))
      (let* ((y (constraint-y con))
             (kind  (constraint-kind con))
             (not-p (constraint-not-p con))
             (x     (constraint-x con))
             (other (if (eq source x) y x)))
        (dolist (var vars)
          (conset-adjoin (find-or-create-constraint kind var other not-p)
                         constraints))))))

(defun eql-var-list (var conset)
  (declare (type lambda-var var)
           (type block-conset conset))
  (collect ((vars))
    (do-eql-vars (other (var conset) (vars))
      (vars other))))

(defun block-conset-assert-eql (bconset var1 var2)
  (declare (type block-conset bconset)
           (type lambda-var var1 var2)
           (optimize speed (safety 0)))
  (when (eql var1 var2)
    (return-from block-conset-assert-eql nil))
  (unless (block-conset-data bconset)
    (let ((sset     (block-conset-vars bconset))
          (eql-var1 (cons var2 (eql-var-list var1 bconset)))
          (eql-var2 (cons var1 (eql-var-list var2 bconset))))
      (inherit-constraints eql-var1 var2 sset)
      (dolist (x eql-var1)
        (dolist (y eql-var2)
          (sset-adjoin (find-or-create-constraint 'eql x y nil)
                       sset)))))
  (let* ((info1 (ensure-block-conset-info bconset var1))
         (info2 (ensure-block-conset-info bconset var2))
         (eqv1  (var-info-eqv-class info1))
         (eqv2  (var-info-eqv-class info2)))
    (when (eql eqv1 eqv2)
      (return-from block-conset-assert-eql nil))
    (setf eqv1 (eqv-class-union eqv1 eqv2)
          (var-info-%eqv-class info1) eqv1
          (var-info-%eqv-class info2) eqv1
          (eqv-class-pointer    eqv2) eqv1
          (eqv-class-class      eqv2) nil
          (eqv-class-conset     eqv2) nil)
    t))

(defun block-conset-union (x y)
  (declare (type block-conset x y)
           (optimize speed (safety 0)))
  (unless (block-conset-data x)
    (sset-union (block-conset-vars x) (block-conset-vars y))
    (return-from block-conset-union x))
  (canonicalize-block-conset y)
  (do-block-conset-vars (var y-info y)
    (let* ((class          (var-info-eqv-class y-info))
           (representative (eqv-class-info class))
           (x-info         (ensure-block-conset-info x var)))
      (declare (type lambda-var representative)
               (type var-info x-info))
      (if (eql var representative)
          (eqv-class-union (var-info-eqv-class x-info) class)
          (block-conset-assert-eql x var representative))
      (setf (var-info-eql-lvars x-info)
            (sset-designator-union (var-info-eql-lvars x-info)
                                   (var-info-eql-lvars y-info))
            (var-info-private x-info)
            (sset-designator-union (var-info-private x-info)
                                   (var-info-private y-info)))))
  (clear-canonicalization-temporaries y)
  x)

(defun block-conset-var-lvar-eql-p (bconset var lvar)
  (declare (type block-conset bconset)
           (type lambda-var var)
           (type lvar lvar)
           (optimize speed (safety 0)))
  (if (not (block-conset-data bconset))
      (let ((con  (find-constraint 'eql var lvar nil)))
        (and con
             (sset-member con (block-conset-vars bconset))))
      (and (sset-member var (block-conset-vars bconset))
           (let* ((info (gethash var (block-conset-data bconset)))
                  (con  (find-constraint 'eql var lvar nil)))
             (declare (type var-info info))
             (and con
                  (sset-member con (var-info-eql-lvars info)))))))

(defun block-conset-forget-var (bconset var)
  (declare (type block-conset bconset)
           (type lambda-var var)
           (optimize speed (safety 0)))
  (unless (block-conset-data bconset)
    (sset-difference (block-conset-vars bconset) (lambda-var-constraints var))
    (return-from block-conset-forget-var bconset))
  (when (sset-delete var (block-conset-vars bconset))
    (let ((info (gethash var (block-conset-data bconset))))
      (flet ((clear (sset)
               (declare (type (maybe sset) sset))
               (when sset
                 (sset-difference sset sset))))
        (clear (var-info-eql-lvars info))
        (clear (var-info-private   info))
        (let ((class (var-info-eqv-class info)))
          (sset-delete var (eqv-class-class class)))
        (setf (var-info-%eqv-class info)
              (let ((class (make-eqv-class)))
                (sset-adjoin var (eqv-class-class class))
                class))))
    t))

(defvar *dummy-var*)

(declaim (inline %call-with-var-block-conset-constraints))
(defun %call-with-var-block-conset-constraints (var bconset function)
  (declare (type lambda-var var)
           (type block-conset bconset)
           (optimize speed (safety 0)))
  (let ((function (if (functionp function)
                      function
                      (fdefinition function))))
    (unless (block-conset-data bconset)
      (do-sset-intersection (con (lambda-var-constraints var) (block-conset-vars bconset))
        (funcall function con))
      (return-from %call-with-var-block-conset-constraints))
    (unless (sset-member var (block-conset-vars bconset))
      (return-from %call-with-var-block-conset-constraints nil))
    (let* ((info     (gethash var (block-conset-data bconset)))
           (class    (var-info-eqv-class info)))
      (do-sset-elements (con (eqv-class-conset class))
        (funcall function con))
      (do-sset-elements (var2 (eqv-class-class class))
        (unless (eql var var2)
          (funcall function var2)))
      (when (var-info-private info)
        (do-sset-elements (con (var-info-private info))
          (funcall function con))))))

(defmacro do-var-block-conset-constraints ((constraint var bconset &optional result) &body body)
  `(block nil
     (%call-with-var-block-conset-constraints ,var ,bconset
                                              (lambda (,constraint)
                                                ,@body))
     ,result))

;; return T if deltap
(defun block-adjoin-constraint (bconset kind x y not-p)
  (declare (type block-conset bconset)
           (type lambda-var x)
           (type constraint-y y)
           (optimize speed (safety 0)))
  (unless (block-conset-data bconset)
    (let ((sset (block-conset-vars bconset)))
      (return-from block-adjoin-constraint
        (and (sset-adjoin (find-or-create-constraint kind x y not-p)
                          sset)
             (dolist (var (eql-var-list x bconset) t)
               (sset-adjoin (find-or-create-constraint kind var y not-p)
                            sset))))     ))
  (let* ((info (ensure-block-conset-info bconset x))
         (class (var-info-eqv-class info)))
    (cond ((and (eql kind 'eql)
                (not not-p))
           (cond ((constant-p y)
                  (sset-adjoin (find-or-create-constraint kind x y not-p)
                               (or (var-info-private info)
                                   (setf (var-info-private info) (make-sset)))))
                 ((lvar-p y)
                  (sset-adjoin (find-or-create-constraint kind x y not-p)
                               (or (var-info-eql-lvars info)
                                   (setf (var-info-eql-lvars info) (make-sset)))))
                 ((lambda-var-p y)
                  (block-conset-assert-eql bconset x y))))
          (t
           (sset-adjoin (find-or-create-constraint kind *dummy-var* y not-p)
                        (eqv-class-conset class))))))
)

(defun find-constraint (kind x y not-p)
  (declare (type lambda-var x) (type constraint-y y) (type boolean not-p))
  (etypecase y
    (ctype
       (let ((index (lambda-var-ctype-constraints x)))
         (when index
           (dolist (con (gethash (sb!kernel::type-class-info y) index) nil)
             (when (and (eq (constraint-kind con) kind)
                        (eq (constraint-not-p con) not-p)
                        (type= (constraint-y con) y))
               (return-from find-constraint con)))
           nil)))
    ((or lvar constant)
       (let ((index (lambda-var-eq-constraints x)))
         (when index
           (dolist (con (gethash y index) nil)
             (when (and (eq (constraint-kind con) kind)
                        (eq (constraint-not-p con) not-p)
                        (eq (constraint-y con) y))
               (return con))))))
    (lambda-var
       (let ((index (lambda-var-eq-constraints x)))
         (when index
           (dolist (con (gethash y index) nil)
             (when (and (eq (constraint-kind con) kind)
                        (eq (constraint-not-p con) not-p)
                        (let ((cx (constraint-x con)))
                          (eq (if (eq cx x)
                                  (constraint-y con)
                                  cx)
                              y)))
               (return con))))))))

(defun register-constraint (x con y)
  (declare (type lambda-var x)
           (type constraint con)
           (type constraint-y y))
  (unless *heavy-consets*
    (conset-adjoin con (lambda-var-constraints x)))
  (etypecase y
    (ctype
       (let ((index (or (lambda-var-ctype-constraints x)
                        (setf (lambda-var-ctype-constraints x)
                              (make-hash-table)))))
         (push con (gethash (sb!kernel::type-class-info y) index))))
    ((or lvar constant lambda-var)
       (let ((index (or (lambda-var-eq-constraints x)
                        (setf (lambda-var-eq-constraints x)
                              (make-hash-table)))))
         (push con (gethash y index)))))
  nil)

;;; Return a constraint for the specified arguments. We only create a
;;; new constraint if there isn't already an equivalent old one,
;;; guaranteeing that all equivalent constraints are EQ. This
;;; shouldn't be called on LAMBDA-VARs with no CONSTRAINTS set.
(defun find-or-create-constraint (kind x y not-p)
  (declare (type lambda-var x) (type constraint-y y) (type boolean not-p))
  (or (find-constraint kind x y not-p)
      (let ((new (make-constraint (length *constraint-universe*)
                                  kind x y not-p)))
        (vector-push-extend new *constraint-universe*
                            (1+ (length *constraint-universe*)))
        (register-constraint x new y)
        (when (lambda-var-p y)
          (register-constraint y new x))
        new)))

;;; If REF is to a LAMBDA-VAR with CONSTRAINTs (i.e. we can do flow
;;; analysis on it), then return the LAMBDA-VAR, otherwise NIL.
#!-sb-fluid (declaim (inline ok-ref-lambda-var))
(defun ok-ref-lambda-var (ref)
  (declare (type ref ref))
  (let ((leaf (ref-leaf ref)))
    (when (and (lambda-var-p leaf)
               (lambda-var-constraints leaf))
      leaf)))

;;; See if LVAR's single USE is a REF to a LAMBDA-VAR and they are EQL
;;; according to CONSTRAINTS. Return LAMBDA-VAR if so.
(defun ok-lvar-lambda-var (lvar constraints)
  (declare (type lvar lvar)
           (type block-conset constraints))
  (let ((use (lvar-uses lvar)))
    (cond ((ref-p use)
           (let ((lambda-var (ok-ref-lambda-var use)))
             (when (and lambda-var
                        (block-conset-var-lvar-eql-p constraints lambda-var lvar))
               lambda-var)))
          ((cast-p use)
           (ok-lvar-lambda-var (cast-value use) constraints)))))

#+nil
(defmacro do-eql-vars ((symbol (var constraints) &optional result) &body body)
  (once-only ((var var))
    `(let ((,symbol ,var))
       (flet ((body-fun ()
                ,@body))
         (body-fun)
         (do-conset-elements (con (block-conset-sset ,constraints) ,result)
           (let ((other (and (eq (constraint-kind con) 'eql)
                             (eq (constraint-not-p con) nil)
                             (cond ((eq ,var (constraint-x con))
                                    (constraint-y con))
                                   ((eq ,var (constraint-y con))
                                    (constraint-x con))
                                   (t
                                    nil)))))
             (when other
               (setq ,symbol other)
               (when (lambda-var-p ,symbol)
                 (body-fun)))))))))

;;;; Searching constraints

;;; Add the indicated test constraint to BLOCK. We don't add the
;;; constraint if the block has multiple predecessors, since it only
;;; holds on this particular path.
(defun add-test-constraint (fun x y not-p target)
  (declare (type block-conset target))
  (block-adjoin-constraint target fun x y not-p)
  (values))

;;; Add complementary constraints to the consequent and alternative
;;; blocks of IF. We do nothing if X is NIL.
(defun add-complement-constraints (fun x y not-p
                                   consequent-constraints
                                   alternative-constraints)
  (declare (type block-conset consequent-constraints
                              alternative-constraints))
  (when x
    (add-test-constraint fun x y not-p       consequent-constraints)
    (add-test-constraint fun x y (not not-p) alternative-constraints))
  (values))

;;; Add test constraints to the consequent and alternative blocks of
;;; the test represented by USE.
(defun add-test-constraints (use if constraints)
  (declare (type node use) (type cif if) (type block-conset constraints))
  ;; Note: Even if we do (IF test exp exp) => (PROGN test exp)
  ;; optimization, the *MAX-OPTIMIZE-ITERATIONS* cutoff means that we
  ;; can't guarantee that the optimization will be done, so we still
  ;; need to avoid barfing on this case.
  (unless (eq (if-consequent if) (if-alternative if))
    (let ((consequent-constraints  (copy-block-conset constraints))
          (alternative-constraints (copy-block-conset constraints)))
      (macrolet ((add (fun x y not-p)
                   `(add-complement-constraints ,fun ,x ,y ,not-p
                                                consequent-constraints
                                                alternative-constraints)))
        (typecase use
          (ref
           (add 'typep (ok-lvar-lambda-var (ref-lvar use) constraints)
                (specifier-type 'null) t))
          (combination
           (unless (eq (combination-kind use)
                       :error)
             (let ((name (lvar-fun-name
                          (basic-combination-fun use)))
                   (args (basic-combination-args use)))
               (case name
                 ((%typep %instance-typep)
                  (let ((type (second args)))
                    (when (constant-lvar-p type)
                      (let ((val (lvar-value type)))
                        (add 'typep
                             (ok-lvar-lambda-var (first args) constraints)
                             (if (ctype-p val)
                                 val
                                 (let ((*compiler-error-context* use))
                                   (specifier-type val)))
                             nil)))))
                 ((eq eql)
                  (let* ((arg1 (first args))
                         (var1 (ok-lvar-lambda-var arg1 constraints))
                         (arg2 (second args))
                         (var2 (ok-lvar-lambda-var arg2 constraints)))
                    ;; The code below assumes that the constant is the
                    ;; second argument in case of variable to constant
                    ;; comparision which is sometimes true (see source
                    ;; transformations for EQ, EQL and CHAR=). Fixing
                    ;; that would result in more constant substitutions
                    ;; which is not a universally good thing, thus the
                    ;; unnatural asymmetry of the tests.
                    (cond ((not var1)
                           (when var2
                             (add-test-constraint 'typep var2 (lvar-type arg1)
                                                  nil
                                                  consequent-constraints)))
                          (var2
                           (add 'eql var1 var2 nil))
                          ((constant-lvar-p arg2)
                           (add 'eql var1
                                (let ((use (principal-lvar-use arg2)))
                                  (if (ref-p use)
                                      (ref-leaf use)
                                      (find-constant (lvar-value arg2))))
                                nil))
                          (t
                           (add-test-constraint 'typep var1 (lvar-type arg2)
                                                nil
                                                consequent-constraints)))))
                 ((< >)
                  (let* ((arg1 (first args))
                         (var1 (ok-lvar-lambda-var arg1 constraints))
                         (arg2 (second args))
                         (var2 (ok-lvar-lambda-var arg2 constraints)))
                    (when var1
                      (add name var1 (lvar-type arg2) nil))
                    (when var2
                      (add (if (eq name '<) '> '<) var2 (lvar-type arg1) nil))))
                 (t
                  (let ((ptype (gethash name *backend-predicate-types*)))
                    (when ptype
                      (add 'typep (ok-lvar-lambda-var (first args) constraints)
                           ptype nil))))))))))
      (values consequent-constraints alternative-constraints))))

;;;; Applying constraints

;;; Return true if X is an integer NUMERIC-TYPE.
(defun integer-type-p (x)
  (declare (type ctype x))
  (and (numeric-type-p x)
       (eq (numeric-type-class x) 'integer)
       (eq (numeric-type-complexp x) :real)))

;;; Given that an inequality holds on values of type X and Y, return a
;;; new type for X. If GREATER is true, then X was greater than Y,
;;; otherwise less. If OR-EQUAL is true, then the inequality was
;;; inclusive, i.e. >=.
;;;
;;; If GREATER (or not), then we max (or min) in Y's lower (or upper)
;;; bound into X and return that result. If not OR-EQUAL, we can go
;;; one greater (less) than Y's bound.
(defun constrain-integer-type (x y greater or-equal)
  (declare (type numeric-type x y))
  (flet ((exclude (x)
           (cond ((not x) nil)
                 (or-equal x)
                 (greater (1+ x))
                 (t (1- x))))
         (bound (x)
           (if greater (numeric-type-low x) (numeric-type-high x))))
    (let* ((x-bound (bound x))
           (y-bound (exclude (bound y)))
           (new-bound (cond ((not x-bound) y-bound)
                            ((not y-bound) x-bound)
                            (greater (max x-bound y-bound))
                            (t (min x-bound y-bound)))))
      (if greater
          (modified-numeric-type x :low new-bound)
          (modified-numeric-type x :high new-bound)))))

;;; Return true if X is a float NUMERIC-TYPE.
(defun float-type-p (x)
  (declare (type ctype x))
  (and (numeric-type-p x)
       (eq (numeric-type-class x) 'float)
       (eq (numeric-type-complexp x) :real)))

;;; Exactly the same as CONSTRAIN-INTEGER-TYPE, but for float numbers.
(defun constrain-float-type (x y greater or-equal)
  (declare (type numeric-type x y))
  (declare (ignorable x y greater or-equal)) ; for CROSS-FLOAT-INFINITY-KLUDGE

  (aver (eql (numeric-type-class x) 'float))
  (aver (eql (numeric-type-class y) 'float))
  #+sb-xc-host                    ; (See CROSS-FLOAT-INFINITY-KLUDGE.)
  x
  #-sb-xc-host                    ; (See CROSS-FLOAT-INFINITY-KLUDGE.)
  (labels ((exclude (x)
             (cond ((not x) nil)
                   (or-equal x)
                   (t
                    (if (consp x)
                        x
                        (list x)))))
           (bound (x)
             (if greater (numeric-type-low x) (numeric-type-high x)))
           (tighter-p (x ref)
             (cond ((null x) nil)
                   ((null ref) t)
                   ((and or-equal
                         (= (type-bound-number x) (type-bound-number ref)))
                    ;; X is tighter if REF is not an open bound and X is
                    (and (not (consp ref)) (consp x)))
                   (greater
                    (< (type-bound-number ref) (type-bound-number x)))
                   (t
                    (> (type-bound-number ref) (type-bound-number x))))))
    (let* ((x-bound (bound x))
           (y-bound (exclude (bound y)))
           (new-bound (cond ((not x-bound)
                             y-bound)
                            ((not y-bound)
                             x-bound)
                            ((tighter-p y-bound x-bound)
                             y-bound)
                            (t
                             x-bound))))
      (if greater
          (modified-numeric-type x :low new-bound)
          (modified-numeric-type x :high new-bound)))))

;;; Return true if LEAF is "visible" from NODE.
(defun leaf-visible-from-node-p (leaf node)
  (cond
   ((lambda-var-p leaf)
    ;; A LAMBDA-VAR is visible iif it is homed in a CLAMBDA that is an
    ;; ancestor for NODE.
    (let ((leaf-lambda (lambda-var-home leaf)))
      (loop for lambda = (node-home-lambda node)
            then (lambda-parent lambda)
            while lambda
            when (eq lambda leaf-lambda)
            return t)))
   ;; FIXME: Check on FUNCTIONALs (CLAMBDAs and OPTIONAL-DISPATCHes),
   ;; not just LAMBDA-VARs.
   (t
    ;; Assume everything else is globally visible.
    t)))

;;; Given the set of CONSTRAINTS for a variable and the current set of
;;; restrictions from flow analysis IN, set the type for REF
;;; accordingly.
(defun constrain-ref-type (ref var in)
  (declare (type ref ref) (type lambda-var var)
           (type block-conset in))
  ;; KLUDGE: The NOT-SET and NOT-FPZ here are so that we don't need to
  ;; cons up endless union types when propagating large number of EQL
  ;; constraints -- eg. from large CASE forms -- instead we just
  ;; directly accumulate one XSET, and a set of fp zeroes, which we at
  ;; the end turn into a MEMBER-TYPE.
  ;;
  ;; Since massive symbol cases are an especially atrocious pattern
  ;; and the (NOT (MEMBER ...ton of symbols...)) will never turn into
  ;; a more useful type, don't propagate their negation except for NIL
  ;; unless SPEED > COMPILATION-SPEED.
  (let ((res (single-value-type (node-derived-type ref)))
        (constrain-symbols (policy ref (> speed compilation-speed)))
        (not-set (alloc-xset))
        (not-fpz nil)
        (not-res *empty-type*)
        (leaf (ref-leaf ref)))
    (flet ((note-not (x)
             (if (fp-zero-p x)
                 (push x not-fpz)
                 (when (or constrain-symbols (null x) (not (symbolp x)))
                   (add-to-xset x not-set)))))
      ;; KLUDGE: the implementations of DO-CONSET-INTERSECTION will
      ;; probably run faster when the smaller set comes first, so
      ;; don't change the order here.
      (do-var-block-conset-constraints (con var in)
        (multiple-value-bind (kind other not-p)
            (etypecase con
              (constraint
                 (let ((x (constraint-x con))
                       (y (constraint-y con)))
                   (values (constraint-kind con)
                           (if (or (eq x leaf) (eq x *dummy-var*))
                               y x)
                           (constraint-not-p con))))
              (lambda-var
                 (values 'eql con nil)))
          (case kind
            (typep
               (if not-p
                   (if (member-type-p other)
                       (mapc-member-type-members #'note-not other)
                       (setq not-res (type-union not-res other)))
                   (setq res (type-approx-intersection2 res other))))
            (eql
               (unless (lvar-p other)
                 (let ((other-type (leaf-type other)))
                   (if not-p
                       (when (and (constant-p other)
                                  (member-type-p other-type))
                         (note-not (constant-value other)))
                       (let ((leaf-type (leaf-type leaf)))
                         (cond
                           ((or (constant-p other)
                                (and (leaf-refs other) ; protect from
                                        ; deleted vars
                                     (csubtypep other-type leaf-type)
                                     (not (type= other-type leaf-type))
                                     ;; Don't change to a LEAF not visible here.
                                     (leaf-visible-from-node-p other ref)))
                            (change-ref-leaf ref other)
                            (when (constant-p other) (return)))
                           (t
                            (setq res (type-approx-intersection2
                                       res other-type)))))))))
            ((< >)
               (cond
                 ((and (integer-type-p res) (integer-type-p other))
                  (let ((greater (eq kind '>)))
                    (let ((greater (if not-p (not greater) greater)))
                      (setq res
                            (constrain-integer-type res other greater not-p)))))
                 ((and (float-type-p res) (float-type-p other))
                  (let ((greater (eq kind '>)))
                    (let ((greater (if not-p (not greater) greater)))
                      (setq res
                            (constrain-float-type res other greater not-p)))))))))))
    (cond ((and (if-p (node-dest ref))
                (or (xset-member-p nil not-set)
                    (csubtypep (specifier-type 'null) not-res)))
           (setf (node-derived-type ref) *wild-type*)
           (change-ref-leaf ref (find-constant t)))
          (t
           (setf not-res
                 (type-union not-res (make-member-type :xset not-set :fp-zeroes not-fpz)))
           (derive-node-type ref
                             (make-single-value-type
                              (or (type-difference res not-res)
                                  res)))
           (maybe-terminate-block ref nil))))
  (values))

;;;; Flow analysis

(defun maybe-add-eql-var-lvar-constraint (ref gen)
  (declare (type block-conset gen))
  (let ((lvar (ref-lvar ref))
        (leaf (ref-leaf ref)))
    (when (and (lambda-var-p leaf) lvar)
      (block-adjoin-constraint gen 'eql leaf lvar nil))))

;;; Copy all CONSTRAINTS involving FROM-VAR - except the (EQL VAR
;;; LVAR) ones - to all of the variables in the VARS list.
#+nil
(defun inherit-constraints (vars from-var constraints target)
  (declare (type block-conset constraints target))
  (do-conset-elements (con (block-conset-sset constraints))
    ;; Constant substitution is controversial.
    (unless (constant-p (constraint-y con))
      (dolist (var vars)
        (let ((eq-x (eq from-var (constraint-x con)))
              (eq-y (eq from-var (constraint-y con))))
          (when (or (and eq-x (not (lvar-p (constraint-y con))))
                    eq-y)
            (block-adjoin-constraint target
                                     (constraint-kind con)
                                     (if eq-x var (constraint-x con))
                                     (if eq-y var (constraint-y con))
                                     (constraint-not-p con))))))))

;; Add an (EQL LAMBDA-VAR LAMBDA-VAR) constraint on VAR1 and VAR2 and
;; inherit each other's constraints.
(defun add-eql-var-var-constraint (var1 var2 constraints
                                   &optional (target constraints))
  (declare (type block-conset constraints target))
  (block-adjoin-constraint target 'eql var1 var2 nil))

;; Add an (EQL LAMBDA-VAR LAMBDA-VAR) constraint on VAR and LVAR's
;; LAMBDA-VAR if possible.
(defun maybe-add-eql-var-var-constraint (var lvar constraints
                                         &optional (target constraints))
  (declare (type lambda-var var) (type lvar lvar)
           (type block-conset constraints target))
  (let ((lambda-var (ok-lvar-lambda-var lvar constraints)))
    (when lambda-var
      (add-eql-var-var-constraint var lambda-var constraints target))))

;;; Local propagation
;;; -- [TODO: For any LAMBDA-VAR ref with a type check, add that
;;;    constraint.]
;;; -- For any LAMBDA-VAR set, delete all constraints on that var; add
;;;    a type constraint based on the new value type.
(declaim (ftype (function (cblock block-conset boolean)
                          block-conset)
                constraint-propagate-in-block))
(defun constraint-propagate-in-block (block gen preprocess-refs-p)
  (declare (type block-conset gen))
  (do-nodes (node lvar block)
    (typecase node
      (bind
       (let ((fun (bind-lambda node)))
         (when (eq (functional-kind fun) :let)
           (loop with call = (lvar-dest (node-lvar (first (lambda-refs fun))))
                 for var in (lambda-vars fun)
                 and val in (combination-args call)
                 when (and val (lambda-var-constraints var))
                 do (let ((type (lvar-type val)))
                      (unless (eq type *universal-type*)
                        (block-adjoin-constraint gen 'typep var type nil)))
                    (maybe-add-eql-var-var-constraint var val gen)))))
      (ref
       (when (ok-ref-lambda-var node)
         (maybe-add-eql-var-lvar-constraint node gen)
         (when preprocess-refs-p
           (let ((var (ref-leaf node)))
             (constrain-ref-type node var gen)))))
      (cast
       (let ((lvar (cast-value node)))
         (let ((var (ok-lvar-lambda-var lvar gen)))
           (when var
             (let ((atype (single-value-type (cast-derived-type node)))) ;FIXME
               (unless (eq atype *universal-type*)
                 (block-adjoin-constraint gen 'typep var atype nil)))))))
      (cset
       (binding* ((var (set-var node))
                  (nil (lambda-var-p var) :exit-if-null)
                  (nil (lambda-var-constraints var) :exit-if-null))
         (block-conset-forget-var gen var)
         (let ((type (single-value-type (node-derived-type node))))
           (unless (eq type *universal-type*)
             (block-adjoin-constraint gen 'typep var type nil)))
         (maybe-add-eql-var-var-constraint var (set-value node) gen)))))
  gen)

(defun constraint-propagate-if (block gen)
  (declare (type block-conset gen))
  (let ((node (block-last block)))
    (when (if-p node)
      (let ((use (lvar-uses (if-test node))))
        (when (node-p use)
          (add-test-constraints use node gen))))))

;;; Starting from IN compute OUT and (consequent/alternative
;;; constraints if the block ends with and IF). Return the list of
;;; successors that may need to be recomputed.
(defun find-block-type-constraints (block final-pass-p)
  (declare (type cblock block))
  (let ((gen (constraint-propagate-in-block
              block
              (if final-pass-p
                  (block-in block)
                  (copy-block-conset (block-in block)))
              final-pass-p)))
    (setf (block-gen block) gen)
    (multiple-value-bind (consequent-constraints alternative-constraints)
        (constraint-propagate-if block gen)
      (if consequent-constraints
          (let* ((node (block-last block))
                 (old-consequent-constraints (if-consequent-constraints node))
                 (old-alternative-constraints (if-alternative-constraints node))
                 (succ ()))
            ;; Add the consequent and alternative constraints to GEN.
            (setf (if-consequent-constraints  node) consequent-constraints
                  (if-alternative-constraints node) alternative-constraints)
            ;; Has the consequent been changed?
            (unless (and old-consequent-constraints
                         (block-conset= (if-consequent-constraints node)
                                        old-consequent-constraints))
              (push (if-consequent node) succ))
            ;; Has the alternative been changed?
            (unless (and old-alternative-constraints
                         (block-conset= (if-alternative-constraints node)
                                        old-alternative-constraints))
              (push (if-alternative node) succ))
            succ)
          ;; There is no IF.
          (unless (and (block-out block)
                       (block-conset= gen (block-out block)))
            (setf (block-out block) gen)
            (block-succ block))))))

;;; Deliver the results of constraint propagation to REFs in BLOCK.
;;; During this pass, we also do local constraint propagation by
;;; adding in constraints as we see them during the pass through the
;;; block.
(defun use-result-constraints (block)
  (declare (type cblock block))
  (constraint-propagate-in-block block (block-in block) t))

;;; Give an empty constraints set to any var that doesn't have one and
;;; isn't a set closure var. Since a var that we previously rejected
;;; looks identical to one that is new, so we optimistically keep
;;; hoping that vars stop being closed over or lose their sets.
(defun init-var-constraints (component)
  (declare (type component component))
  (dolist (fun (component-lambdas component))
    (flet ((frob (x)
             (dolist (var (lambda-vars x))
               (unless (lambda-var-constraints var)
                 (when (or (null (lambda-var-sets var))
                           (not (closure-var-p var)))
                   (setf (lambda-var-constraints var) (make-conset)))))))
      (frob fun)
      (dolist (let (lambda-lets fun))
        (frob let)))))

;;; Return the constraints that flow from PRED to SUCC. This is
;;; BLOCK-OUT unless PRED ends with an IF and test constraints were
;;; added.
(defun block-out-for-successor (pred succ)
  (declare (type cblock pred succ))
  (let ((last (block-last pred)))
    (or (when (if-p last)
          (cond ((eq succ (if-consequent last))
                 (if-consequent-constraints last))
                ((eq succ (if-alternative last))
                 (if-alternative-constraints last))))
        (block-out pred))))

(defun compute-block-in (block)
  (let ((in nil))
    (dolist (pred (block-pred block))
      ;; If OUT has not been calculated, assume it to be the universal
      ;; set.
      (let ((out (block-out-for-successor pred block)))
        (when out
          (if in
              (block-conset-intersection in out)
              (setq in (copy-block-conset out))))))
    (or in (make-block-conset))))

(defun update-block-in (block)
  (let ((in (compute-block-in block)))
    (cond ((and (block-in block) (block-conset= in (block-in block)))
           nil)
          (t
           (setf (block-in block) in)))))

;;; Return two lists: one of blocks that precede all loops and
;;; therefore require only one constraint propagation pass and the
;;; rest. This implementation does not find all such blocks.
;;;
;;; A more complete implementation would be:
;;;
;;;     (do-blocks (block component)
;;;       (if (every #'(lambda (pred)
;;;                      (or (member pred leading-blocks)
;;;                          (eq pred head)))
;;;                  (block-pred block))
;;;           (push block leading-blocks)
;;;           (push block rest-of-blocks)))
;;;
;;; Trailing blocks that succeed all loops could be found and handled
;;; similarly. In practice though, these more complex solutions are
;;; slightly worse performancewise.
(defun leading-component-blocks (component)
  (declare (type component component))
  (flet ((loopy-p (block)
           (let ((n (block-number block)))
             (dolist (pred (block-pred block))
               (unless (< n (block-number pred))
                 (return t))))))
    (let ((leading-blocks ())
          (rest-of-blocks ())
          (seen-loop-p ()))
      (do-blocks (block component)
        (when (and (not seen-loop-p) (loopy-p block))
          (setq seen-loop-p t))
        (if seen-loop-p
            (push block rest-of-blocks)
            (push block leading-blocks)))
      (values (nreverse leading-blocks) (nreverse rest-of-blocks)))))

;;; Append OBJ to the end of LIST as if by NCONC but only if it is not
;;; a member already.
(defun nconc-new (obj list)
  (do ((x list (cdr x))
       (prev nil x))
      ((endp x) (if prev
                    (progn
                      (setf (cdr prev) (list obj))
                      list)
                    (list obj)))
    (when (eql (car x) obj)
      (return-from nconc-new list))))

(defun find-and-propagate-constraints (component)
  (let ((blocks-to-process ()))
    (flet ((enqueue (blocks)
             (dolist (block blocks)
               (setq blocks-to-process (nconc-new block blocks-to-process)))))
      (multiple-value-bind (leading-blocks rest-of-blocks)
          (leading-component-blocks component)
        ;; Update every block once to account for changes in the
        ;; IR1. The constraints of the lead blocks cannot be changed
        ;; after the first pass so we might as well use them and skip
        ;; USE-RESULT-CONSTRAINTS later.
        (dolist (block leading-blocks)
          (setf (block-in block) (compute-block-in block))
          (find-block-type-constraints block t))
        (setq blocks-to-process (copy-list rest-of-blocks))
        ;; The rest of the blocks.
        (dolist (block rest-of-blocks)
          (aver (eq block (pop blocks-to-process)))
          (setf (block-in block) (compute-block-in block))
          (enqueue (find-block-type-constraints block nil)))
        ;; Propagate constraints
        (loop for block = (pop blocks-to-process)
              while block do
              (unless (eq block (component-tail component))
                (when (update-block-in block)
                  (enqueue (find-block-type-constraints block nil)))))
        rest-of-blocks))))

(defun constraint-propagate (component)
  (declare (type component component))
  (init-var-constraints component)

  (unless (block-out (component-head component))
    (setf (block-out (component-head component)) (make-block-conset)))

  (dolist (block (find-and-propagate-constraints component))
    (unless (block-delete-p block)
      (use-result-constraints block)))

  (values))
