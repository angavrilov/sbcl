;;;; This file implements a sparse set abstraction, represented as a
;;;; custom lightweight hash-table. We don't use bit-vectors to
;;;; represent sets in flow analysis, since the universe may be quite
;;;; large but the average number of elements is small. We also don't
;;;; use sorted lists like in the original CMUCL code, since it had
;;;; bad worst-case performance (on some real-life programs the
;;;; hash-based sset gives a 20% compilation speedup). A custom
;;;; hash-table is used since the standard one is too heavy (locking,
;;;; memory use) for this use.

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information. (This file no)

(in-package "SB!C")

;;; Each structure that may be placed in a SSET must include the
;;; SSET-ELEMENT structure. We allow an initial value of NIL to mean
;;; that no ordering has been assigned yet (although an ordering must
;;; be assigned before doing set operations.)
(def!struct (sset-element (:constructor nil)
                         (:copier nil))
  (number nil :type (or index null))
  (hash   most-positive-fixnum :type (and unsigned-byte fixnum)))

#||
(defstruct (sset (:copier nil))
  ;; Vector containing the set values. 0 is used for empty (since
  ;; initializing a vector with 0 is cheaper than with NIL), +DELETED+
  ;; is used to mark buckets that used to contain an element, but no
  ;; longer do.
  (vector #() :type simple-vector)
  ;; How many buckets currently contain or used to contain an element.
  (free 0 :type index)
  ;; How many elements are currently members of the set.
  (count 0 :type index))
(defprinter (sset) vector)

;;; Iterate over the elements in SSET, binding VAR to each element in
;;; turn.
(defmacro do-sset-elements ((var sset &optional result) &body body)
  `(loop for ,var across (sset-vector ,sset)
         do (unless (member ,var '(0 +deleted+))
              ,@body)
         finally (return ,result)))

;;; Primary hash.
(declaim (inline sset-hash1))
(defun sset-hash1 (element)
  #+sb-xc-host
  (let ((result (sset-element-number element)))
    ;; This is performance critical, and it's not certain that the host
    ;; compiler does modular arithmetic optimization. Instad use
    ;; something that most CL implementations will do efficiently.
    (the fixnum (logxor (the fixnum result)
                        (the fixnum (ash result -9))
                        (the fixnum (ash result -5)))))
  #-sb-xc-host
  (let ((result (sset-element-number element)))
    (declare (type sb!vm:word result))
    ;; We only use the low-order bits.
    (macrolet ((set-result (form)
                 `(setf result (ldb (byte #.sb!vm:n-word-bits 0) ,form))))
      (set-result (+ result (ash result -19)))
      (set-result (logxor result (ash result -13)))
      (set-result (+ result (ash result -9)))
      (set-result (logxor result (ash result -5)))
      (set-result (+ result (ash result -2)))
      (logand sb!xc:most-positive-fixnum result))))

;;; Secondary hash (for double hash probing). Needs to return an odd
;;; number.
(declaim (inline sset-hash2))
(defun sset-hash2 (element)
  (let ((number (sset-element-number element)))
    (declare (fixnum number))
    (logior 1 number)))

;;; Double the size of the hash vector of SET.
(defun sset-grow (set)
  (let* ((vector (sset-vector set))
         (new-vector (make-array (if (zerop (length vector))
                                     2
                                     (* (length vector) 2))
                                 :initial-element 0)))
    (setf (sset-vector set) new-vector
          (sset-free set) (length new-vector)
          (sset-count set) 0)
    (loop for element across vector
          do (unless (member element '(0 +deleted+))
               (sset-adjoin element set)))))

;;; Rehash the sset when the proportion of free cells in the set is
;;; lower than this.
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant +sset-rehash-threshold+ 1/4))

;;; Destructively add ELEMENT to SET. If ELEMENT was not in the set,
;;; then we return true, otherwise we return false.
(declaim (ftype (sfunction (sset-element sset) boolean) sset-adjoin))
(defun sset-adjoin (element set)
  (declare (optimize (speed 2)))
  (when (<= (sset-free set)
            (max 1 (truncate (length (sset-vector set))
                             #.(round (/ +sset-rehash-threshold+)))))
    (sset-grow set))
  (loop with vector = (sset-vector set)
        with mask of-type fixnum = (1- (length vector))
        with secondary-hash = (sset-hash2 element)
        for hash of-type index = (logand mask (sset-hash1 element)) then
          (logand mask (+ hash secondary-hash))
        for current = (aref vector hash)
        for deleted-index = nil
        do (cond ((eql current 0)
                  (incf (sset-count set))
                  (cond (deleted-index
                         (setf (aref vector deleted-index) element))
                        (t
                         (decf (sset-free set))
                         (setf (aref vector hash) element)))
                  (return t))
                 ((and (eql current '+deleted+)
                       (not deleted-index))
                  (setf deleted-index hash))
                 ((eq current element)
                  (return nil)))))

;;; Destructively remove ELEMENT from SET. If element was in the set,
;;; then return true, otherwise return false.
(declaim (ftype (sfunction (sset-element sset) boolean) sset-delete))
(defun sset-delete (element set)
  (when (zerop (length (sset-vector set)))
    (return-from sset-delete nil))
  (loop with vector = (sset-vector set)
        with mask fixnum = (1- (length vector))
        with secondary-hash = (sset-hash2 element)
        for hash of-type index = (logand mask (sset-hash1 element)) then
          (logand mask (+ hash secondary-hash))
        for current = (aref vector hash)
        do (cond ((eql current 0)
                  (return nil))
                 ((eq current element)
                  (decf (sset-count set))
                  (setf (aref vector hash) '+deleted+)
                  (return t)))))

;;; Return true if ELEMENT is in SET, false otherwise.
(declaim (ftype (sfunction (sset-element sset) boolean) sset-member))
(defun sset-member (element set)
  (when (zerop (length (sset-vector set)))
    (return-from sset-member nil))
  (loop with vector = (sset-vector set)
        with mask fixnum = (1- (length vector))
        with secondary-hash = (sset-hash2 element)
        for hash of-type index = (logand mask (sset-hash1 element)) then
          (logand mask (+ hash secondary-hash))
        for current = (aref vector hash)
        do (cond ((eql current 0)
                  (return nil))
                 ((eq current element)
                  (return t)))))

(declaim (ftype (sfunction (sset sset) boolean) sset=))
(defun sset= (set1 set2)
  (unless (eql (sset-count set1)
               (sset-count set2))
    (return-from sset= nil))
  (do-sset-elements (element set1)
    (unless (sset-member element set2)
      (return-from sset= nil)))
  t)

;;; Return true if SET contains no elements, false otherwise.
(declaim (ftype (sfunction (sset) boolean) sset-empty))
(defun sset-empty (set)
  (zerop (sset-count set)))

;;; Return a new copy of SET.
(declaim (ftype (sfunction (sset) sset) copy-sset))
(defun copy-sset (set)
  (make-sset :vector (let* ((vector (sset-vector set))
                            (new-vector (make-array (length vector))))
                       (declare (type simple-vector vector new-vector)
                                (optimize speed (safety 0)))
                       ;; There's no REPLACE deftransform for simple-vectors.
                       (dotimes (i (length vector))
                         (setf (aref new-vector i)
                               (aref vector i)))
                       new-vector)
             :count (sset-count set)
             :free (sset-free set)))

;;; Perform the appropriate set operation on SET1 and SET2 by
;;; destructively modifying SET1. We return true if SET1 was modified,
;;; false otherwise.
(declaim (ftype (sfunction (sset sset) boolean) sset-union sset-intersection
                sset-difference))
(defun sset-union (set1 set2)
  (loop with modified = nil
        for element across (sset-vector set2)
        do (unless (member element '(0 +deleted+))
             (when (sset-adjoin element set1)
               (setf modified t)))
        finally (return modified)))
(defun sset-intersection (set1 set2)
  (loop with modified = nil
        for element across (sset-vector set1)
        for index of-type index from 0
        do (unless (member element '(0 +deleted+))
             (unless (sset-member element set2)
               (decf (sset-count set1))
               (setf (aref (sset-vector set1) index) '+deleted+
                     modified t)))
        finally (return modified)))
(defun sset-difference (set1 set2)
  (loop with modified = nil
        for element across (sset-vector set1)
        for index of-type index from 0
        do (unless (member element '(0 +deleted+))
             (when (sset-member element set2)
               (decf (sset-count set1))
               (setf (aref (sset-vector set1) index) '+deleted+
                     modified t)))
        finally (return modified)))

;;; Destructively modify SET1 to include its union with the difference
;;; of SET2 and SET3. We return true if SET1 was modified, false
;;; otherwise.
(declaim (ftype (sfunction (sset sset sset) boolean) sset-union-of-difference))
(defun sset-union-of-difference (set1 set2 set3)
  (loop with modified = nil
        for element across (sset-vector set2)
        do (unless (member element '(0 +deleted+))
             (unless (sset-member element set3)
               (when (sset-adjoin element set1)
                 (setf modified t))))
        finally (return modified)))
||#

(defparameter *sset-random-state* (make-random-state))

(declaim (inline ensure-sset-hash))
(defun ensure-sset-hash (element)
  (declare (type sset-element element))
  (let ((hash (sset-element-hash element)))
    (if (= most-positive-fixnum hash)
        (setf (sset-element-hash element)
              (random most-positive-fixnum (load-time-value *sset-random-state*)))
        hash)))

(defstruct (sset
             (:copier %copy-sset))
  (table #() :type simple-vector)
  (length  0 :type index)
  (count   0 :type index)
  (rehash-count 0 :type index))

(declaim (inline sset-empty)
         (ftype (sfunction (sset) boolean) sset-empty))
(defun sset-empty (sset)
  (declare (type sset sset))
  (zerop (sset-count sset)))

(declaim (inline %sset-init))
(defun %sset-init (sset)
  (declare (type sset sset))
  (setf (sset-table  sset) (make-array 11 :initial-element nil)
        (sset-length sset) 8
        (sset-rehash-count sset) (truncate 8 2)))

(declaim (inline interpolate))
(defun interpolate (hash length)
  (declare (type index hash length))
  (macrolet
      ((frob ()
         (let* ((fx-len   (integer-length most-positive-fixnum))
                (fx-len/2 (truncate fx-len 2)))
           `(if (< length ,(ash 1 fx-len/2))
                (ash (* (ash hash ,(- fx-len/2)) length)
                     ,(- fx-len/2 fx-len))
                (the index (ash (* hash length) ,(- fx-len)))))))
    (frob)))

(defun sset-grow (sset)
  (declare (type sset sset)
           (optimize speed))
  (let ((old-table  (sset-table sset))
        (new-length (truncate (* 3 (sset-length sset)) 2)))
    (declare (type index new-length))
    (tagbody
     retry
       (let* ((new-table  (make-array (+ new-length 3) :initial-element nil))
              (size       (length new-table))
              (alloc      0))
         (declare (type index alloc))
         (map nil (lambda (x)
                    (when x
                      (let* ((hash (sset-element-hash x))
                             (pos  (max (interpolate hash new-length)
                                        alloc)))
                        (when (>= pos size)
                          (setf new-length (ceiling (* 3 new-length) 2))
                          (go retry))
                        (setf (aref new-table pos) x
                              alloc                (1+ pos)))))
              old-table)
         (setf (sset-table  sset) new-table
               (sset-length sset) new-length
               (sset-rehash-count sset) (truncate new-length 2))
         (return-from sset-grow alloc)))))

(declaim (ftype (sfunction (sset-element sset) boolean) sset-member))
(defun sset-member (element sset)
  (declare (type sset-element element)
           (type sset sset)
           (optimize speed))
  (let ((hash  (sset-element-hash element))
        (count (sset-count sset)))
    (when (or (= hash most-positive-fixnum)
              (zerop count))
      (return-from sset-member nil))
    (let ((table  (sset-table  sset))
          (length (sset-length sset)))
      (loop for i from (interpolate hash length) below (length table)
            for x = (aref table i)
            do (when (eq x element)
                 (return t))
               (when (or (null x)
                         (> (sset-element-hash x) hash))
                 (return nil))))))

(declaim (ftype (sfunction (sset-element sset) boolean) sset-adjoin))
(defun sset-adjoin (element sset)
  (declare (type sset-element element)
           (type sset sset)
           (optimize speed))
  (cond ((sset-empty sset)
         (%sset-init sset))
        ((>= (sset-count sset) (sset-rehash-count sset))
         (sset-grow sset)))
  (tagbody
   retry
     (let* ((hash   (ensure-sset-hash element))
            (table  (sset-table sset))
            (length (sset-length sset))
            (size   (length table)))
       (loop for i from (interpolate hash length) below size
             for x = (aref table i)
             do (when (eq x element)
                  (return-from sset-adjoin nil))
                (when (null x)
                  (setf (aref table i) element)
                  (incf (sset-count sset))
                  (return-from sset-adjoin t))
                (when (or (> (sset-element-hash x) hash)
                          (and (= (sset-element-hash x) hash)
                               (> (sset-element-number x) (sset-element-number element))))
                  (let ((empty
                         (loop for j from (1+ i) below size
                               for x = (aref table j)
                               do (when (null x)
                                    (return j))
                               finally (go rehash))))
                    (loop for j from (1- empty) downto i
                          do (setf (aref table (1+ j)) (aref table j)))
                    (setf (aref table i) element)
                    (incf (sset-count sset))
                    (return-from sset-adjoin t)))))
     rehash
     (sset-grow sset)
     (go retry)))

(declaim (ftype (sfunction (sset-element sset) boolean) sset-delete))
(defun sset-delete (element sset)
  (declare (type sset-element element)
           (type sset sset)
           (optimize speed))
  (when (or (sset-empty sset)
            (= most-positive-fixnum (sset-element-hash element)))
    (return-from sset-delete nil))
  (let* ((hash   (sset-element-hash element))
         (table  (sset-table sset))
         (length (sset-length sset))
         (size   (length table)))
    (loop for i from (interpolate hash length) below size
          for x = (aref table i)
          do (when (eq x element)
               (decf (sset-count sset))
               (let ((last (loop for j from (1+ i) below size
                                 for x = (aref table j)
                                 do
                              (when (null x)
                                (return j))
                              (let ((loc (interpolate (sset-element-hash x) length)))
                                (if (< loc j)
                                    (setf (aref table (1- j)) x)
                                    (return j)))
                                 finally (return size))))
                 (setf (aref table (1- last)) nil))
               (return t))
             (when (or (null x)
                       (> (sset-element-hash x) hash))
               (return nil)))))

(declaim (inline %call-with-sset-elements))
(defun %call-with-sset-elements (sset function)
  (declare (type sset sset)
           (optimize speed))
  (let ((function (if (functionp function)
                      function
                      (fdefinition function))))
    (map nil (lambda (x)
               (when x
                 (funcall function x)))
         (sset-table sset))))

(defmacro do-sset-elements ((var sset &optional result) &body body)
  `(block nil
     (%call-with-sset-elements ,sset (lambda (,var) ,@body))
     ,result))

(defmacro with-sset-iterator ((sset iterator) &body body)
  (let ((_sset  (gensym "SSET"))
        (_length (gensym "LENGTH"))
        (_table (gensym "TABLE"))
        (_index (gensym "INDEX"))
        (_max   (gensym "MAX")))
    `(let* ((,_sset ,sset)
            (,_length (sset-length ,_sset))
            (,_table (sset-table ,_sset))
            (,_index 0)
            (,_max   (length ,_table)))
       (declare (type sset ,_sset)
                (type index ,_index ,_max))
       (flet ((,iterator (&optional hint)
                (when hint
                  (setf ,_index
                        (max ,_index
                             (interpolate (sset-element-hash hint) ,_length))))
                (loop for i from ,_index below ,_max
                      for x = (aref ,_table i)
                      when x
                        do (setf ,_index (1+ i))
                           (return x)
                      finally (progn
                                (setf ,_index ,_max)
                                (return nil)))))
         ,@body))))

(defmacro with-sset-builder ((sset builder) &body body)
  (let ((_sset  (gensym "SSET"))
        (_table (gensym "TABLE"))
        (_length (gensym "LENGTH"))
        (_size  (gensym "SIZE"))
        (_index (gensym "INDEX"))
        (_max   (gensym "MAX"))
        (_grow  (gensym "GROW")))
    `(let* ((,_sset   ,sset)
            (,_table  (sset-table ,_sset))
            (,_length (sset-length ,_sset))
            (,_size   (length ,_table))
            (,_index  0)
            (,_max    (sset-rehash-count ,_sset)))
       (declare (type sset ,_sset)
                (type simple-vector ,_table)
                (type index ,_length ,_size ,_index ,_max))
       (labels ((,_grow ()
                  (setf ,_index  (sset-grow ,_sset)
                        ,_table  (sset-table ,_sset)
                        ,_length (sset-length ,_sset)
                        ,_size   (length ,_table)
                        ,_max    (sset-rehash-count ,_sset)))
                (,builder (element)
                  (declare (type sset-element element))
                  (loop while (or (>= ,_index ,_size)
                                  (>= (sset-count ,_sset) ,_max))
                        do (,_grow))
                  (let ((loc (max ,_index (interpolate (sset-element-hash element) ,_length))))
                    (setf (aref ,_table loc) element
                          ,_index            (1+ loc))
                    (incf (sset-count ,_sset)))))
         ,@body))))

(declaim (ftype (sfunction (sset sset) boolean) sset=))
(defun sset= (sset1 sset2)
  (declare (type sset sset1 sset2)
           (optimize speed))
  (with-sset-iterator (sset1 sset1)
    (with-sset-iterator (sset2 sset2)
      (loop for x = (sset1)
            for y = (sset2)
            do (unless (eq x y)
                 (return nil))
               (when (null x)
                 (return t))))))

(declaim (ftype (sfunction (sset) sset) copy-sset))
(defun copy-sset (sset)
  (declare (type sset sset)
           (optimize speed))
  (let ((copy (%copy-sset sset)))
    (setf (sset-table copy) (copy-seq (sset-table sset)))
    copy))

(declaim (ftype (sfunction (sset sset) boolean) sset-union sset-intersection
                sset-difference))
(defun sset-union (dst src)
  (declare (type sset dst src)
           (optimize speed))
  (let ((deltap nil))
    (do-sset-elements (x src deltap)
      (setf deltap (if (sset-adjoin x dst)
                       t
                       deltap)))))

(defun sset-clean-deletions (sset)
  (declare (type sset sset)
           (optimize speed))
  (setf (sset-count sset) 0)
  (with-sset-builder (sset add)
    (let ((table (sset-table sset)))
      (loop for i below (length table)
            for x = (aref table i)
            do (when x
                 (setf (aref table i) nil)
                 (add x)))))
  sset)

(defun sset-intersection (dst src)
  (declare (type sset dst src)
           (optimize speed))
  (when (eq dst src)
    (return-from sset-intersection nil))
  (let ((table  (sset-table dst))
        (deltap nil))
    (loop for i below (length table)
          for x  = (aref table i)
          do (when (and x
                        (not (sset-member x src)))
               (setf deltap         t
                     (aref table i) nil)))
    (when deltap
      (sset-clean-deletions dst))
    deltap))

(defun sset-difference (dst src)
  (declare (type sset dst src)
           (optimize speed))
  (when (sset-empty dst)
    (return-from sset-difference nil))
  (when (eq dst src)
    (fill (sset-table dst) nil)
    (setf (sset-count dst) 0)
    (return-from sset-difference t))
  (let ((table  (sset-table dst))
        (deltap nil))
    (loop for i below (length table)
          for x  = (aref table i)
          do (when (and x
                        (sset-member x src))
               (setf deltap         t
                     (aref table i) nil)))
    (sset-clean-deletions dst)
    deltap))

(declaim (ftype (sfunction (sset sset sset) boolean) sset-union-of-difference))
(defun sset-union-of-difference (dst src1 src2)
  (declare (type sset dst src1 src2)
           (optimize speed))
  (let ((deltap nil))
    (flet ((add (x)
             (setf deltap (if (sset-adjoin x dst)
                              t deltap))))
      (declare (inline add))
      (do-sset-elements (x src1 deltap)
        (unless (sset-member x src2)
          (add x))))
    deltap))

(declaim (inline sset-element<))
(defun sset-element< (x y)
  (declare (type sset-element x y))
  (let ((hx (sset-element-hash x))
        (hy (sset-element-hash y)))
    (or (< hx hy)
        (and (= hx hy)
             (< (sset-element-number x) (sset-element-number y))))))

(declaim (inline %call-with-sset-intersection))
(defun %call-with-sset-intersection (sset1 sset2 function)
  (declare (type sset sset1 sset2)
           (optimize speed))
  (let ((function (if (functionp function)
                      function
                      (fdefinition function))))
    (with-sset-iterator (sset1 src1)
      (with-sset-iterator (sset2 src2)
        (let ((x1 (src1))
              (x2 (src2)))
          (loop while (and x1 x2)
                do
             (cond ((eq x1 x2)
                    (funcall function x1)
                    (setf x1 (src1)
                          x2 (src2)))
                   ((sset-element< x1 x2)
                    (setf x1 (src1 x2)))
                   (t
                    (setf x2 (src2 x1))))))))))

(defmacro do-sset-intersection ((var sset1 sset2 &optional result) &body body)
  `(block nil
     (%call-with-sset-intersection ,sset1 ,sset2 (lambda (,var) ,@body))
     ,result))

(declaim (notinline sset-empty))
