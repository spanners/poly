(setq poly "/path/to/this/file/polynomial.lisp")
(setq tests "/path/to/tests/file/tests.lisp")
(defun rl () (load poly))
(defun tst () (load tests))

;;; ---------------------------------------------------------------------------
;;; Polynomial operators.
(defun p+ (p1 p2) (clean (clean (append p1 p2))))
(defun p- (p1 p2) (p+ p1 (negate p2)))
(defun p* (p1 p2) (clean (pmult (clean p1) (clean p2))))
(defun p= (p1 p2) (pequal (clean p1) (clean p2)))

;;; ---------------------------------------------------------------------------
;;; Functions for cleaning input before/after manipulation.
;; A 4-pass algorithm:
;; Pass 1: Remove terms with zero as coefficient, (rem-zero)
;; Pass 2: For each term, remove variables raised to power 0, (simp-vars)
;; Pass 3: For each term, combine like variables into one variable, (simp-vars)
;; Pass 4: Combine like terms in whole polynomial into one term. (simp-terms)
(defun clean (p) (simp-terms 
		   (simp-vars ;; performs both Pass 3 and Pass 2
		     (rem-zero p)))) 

;; Pass 4.
;; Simplifies the terms in a polynomial by summing collected like terms.
(defun simp-terms (p)
  (simplifier p combine-terms vars= (lambda (x) (vars x))))

;; Generic simplifier function used by simp-terms and simp-vars.
;; Takes a list you want to simplify, 
;; a combiner to perform the summing step to combine the like terms/vars 
;; into one,
;; an test of equality, either t= or vars= for collecting like terms/vars,
;; and a selector to get inside the term/variable to compare for likeness.
(defun simplifier (L combiner test selector)
  (cond ((null L) '())
	(t (let ((simplified ;; save it in "simplified"
		   (combiner ;; combine like terms/vars into one
			       (collectlike ;; collect like terms/vars
				 (car L)    ;; those that are like 1st term/var
				 L 	    ;; in the whole poly/var list
				 test       ;; using t=/vars= to compare
				 selector)))) ;; selecting vars/power
		(cons simplified ;; build a list of simplified terms/vars
		      (simplifier
			(removelike simplified 
				(cdr L) test selector)
				  combiner test selector))))))

;; Combines like terms into one term by summing coefficients
(defun combine-terms (lterms)
  (mk-term (accumulate + 0 (map coef lterms)) (vars (pcar lterms))))

;; Produces a list of terms/variables that are like x in list L
(defun collectlike (x L test selector)
  (cond ((null L) '())
	((test (selector x) (selector (car L)))
	 (cons (car L) (collectlike x (cdr L) test selector)))
	(t (collectlike x (cdr L) test selector))))

;; Pass 3 and Pass 2 in one function.
;; Simplifies the variables in a polynomial by summing collected like 
;; variables. Removes variables raised to power 0.
(defun simp-vars (p)
  (cond ((null p) '())
	((constantp (pcar p)) (cons (pcar p) (simp-vars (pcdr p)))) 
	(t (cons (mk-term (coef (pcar p))
			  (removelike 0 ;; Pass 2

				  (simplifier (vars (pcar p)) ;; Pass 3
					      combine-vars 
					      equal 
					      (lambda (v) (vcar v)))

				  equal ;; test for variable letters
				  (lambda (v) ;; selector for removelike
				    (cond ((not (listp v)) v) 
						    (t (power v))))))
		 (simp-vars (pcdr p))))))

;; Combines like variables into one variable by summing powers
(defun combine-vars (lvars)
  (mk-var (letter (vcar lvars)) (accumulate + 0 (map power lvars))))

;; Performs step 1.
;; Removes terms with zero as coefficient from a polynomial.
(defun rem-zero (p)
  (removelike 0 p = (lambda (x) (cond ((not (listp x)) x) (t (coef x))))))

;; Produces a list of terms/variables that are not like x in list L
(defun removelike (x L test selector)
  (cond ((null L) '())
	((test (selector x) (selector (car L))) (removelike x (cdr L) test selector))
	(t (cons (car L) (removelike x (cdr L) test selector)))))

;;; ---------------------------------------------------------------------------
;;; Functions for p-, p* and p=

;; Negates the coefficients in a polynomial by multiplying each by -1.
(defun negate (p) (map (lambda (x) (mk-term (* -1 (coef x)) (vars x))) p))

;; Algorithm:
;; For each term in p1, for each term in p2 multiply terms using t*.
;; Then accumulate each cartesian pair into one polynomial with append.
(defun pmult (p1 p2)
  (accumulate append '() (mmap t* p1 p2)))

;; Make a term by multiplying coefficients and just appending variable lists.
;; We'll leave the job of summing variables to (simp-vars) in the (clean) step.
(defun t* (t1 t2)
 (mk-term (* (coef t1) (coef t2))
	  (cond ((and (constantp t1) (constantp t2)) no-vars) 
	        ((constantp t1) (vars t2))
		((constantp t2) (vars t1))
		(t (append (vars t1) (vars t2))))))

;; Algorithm:
;; For each term in p1, for each term in p2, test equality of terms using t=.
;; Since we do not sort polynomials, we can not simply check each position in 
;; p1 and p2 to see if they have matching terms.
;; If (p= p1 p2) the nested map gives us ((#t ()) (() #t)), if (length p1) is 
;; 2, and (= (length p1) (length p2)). This means t= returned #t for p1's
;; first term and a term in p2, and t= returned true for p1's second term and a
;; term in p2. We reduce this to a list of nils (if (p= p1 p2)) with 2 maps.
(defun pequal (p1 p2) (and (= (length p1) (length p2)) 
			   (all (map any (mmap t= p1 p2)))))

;; Asks if coefficients and variables of t1 and t2 are equal using vars=.
(defun t= (t1 t2)
  (cond ((and (constantp t1) (constantp t2)) (= (coef t1) (coef t2)))
	(t (and (= (coef t1) (coef t2))
		(vars= (vars t1) (vars t2))))))

;; Asks if variables of vs1 and vs2 are equal using same method as pequal.
;; Uses v= to actually compare individual variables.
(defun vars= (vs1 vs2) (cond ((and (null vs1) (null vs2)) t)
			     ((and (equal no-vars vs1) (equal no-vars vs2)) t)
			     (t (and (= (length vs1) (length vs2))
				     (all (map any (mmap v= vs1 vs2)))))))

;; Asks if v1 and v2 are equal
(defun v= (v1 v2) (and (equal (letter v1) (letter v2))
		       (= (power v1) (power v2))))

;;; ---------------------------------------------------------------------------
;;; Utility functions

;; About the representation:
;; A polynomial is a list of terms. Polynomials may (equal empty).
;; A term is a list of two elements. Terms may not (equal empty).
;; First element is an atom - a coefficient, accessed with (coef term). 
;; Coefficients may be 0.
;; Second element is a list of variables, accessed with (vars term). 
;; List of variables may (equal no-vars) - a constant.
(defun mk-term (coeff variabs) (cons coeff (cons variabs '())))

;; A non-empty variable is a list of two elements.
;; First element is a variable - can be any object.
;; Second element is an atom - a power the letter is raised to.
;; A variable may be raised to the power 0.
(defun mk-var (ltr pow) (mk-term ltr pow))

;; Asks if term is a constant
;; A term is a constant if it has an integer coefficient, and no variables
(defun constantp (term)
  (cond ((null term) nil)
	((null (coef term)) nil)
	(t (and (integerp (coef term)) 
		(equal (vars term) no-vars)))))

;; Asks if all the values in L are true (not nil)
(defun all (L)
  (cond ((null L) t)
	(else (and (not (equal nil (car L))) (all (cdr L))))))

;; Asks if any of the values in L are true (not nil)
(defun any (L)
  (cond ((null L) nil)
	(else (or (not (equal nil (car L))) (any (cdr L))))))

;; Nested map abbreviation
(defun mmap (f l1 l2) (map (lambda (x) (map (lambda (y) (f x y)) l2)) l1))

;; Aliases to (hopefully) make code clearer
(setq pcar car) (setq pcdr cdr) (setq coef car) (setq vars cadr) 
(setq vcar car) (setq vcdr cdr) (setq letter car) (setq power cadr) 
(setq empty '()) (setq no-vars '(())) ;; (equal (vars term) no-vars) - constant
