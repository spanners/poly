(setq this-file "/home/simon/git/poly/poly.lisp")
(setq tests "/home/simon/git/poly/tests.lisp")
(defun rl () (load this-file))
(defun tst () (load tests))

;;; ---------------------------------------------------------------------------
;;; Polynomial operators.
(defun p+ (p1 p2) (clean (append p1 p2)))
(defun p- (p1 p2) (p+ p1 (negate p2)))
(defun p* (p1 p2) (clean (pmult (clean p1) (clean p2))))
(defun p= (p1 p2) (null (p- p1 p2)))

;;; ---------------------------------------------------------------------------
;;; Functions for cleaning input before/after manipulation.
;; A 2-pass algorithm:
;; Pass 1: For each term, combine like variables into one variable, (simp-vars)
;; Pass 2: Combine like terms in whole polynomial into one term. (simp-terms)
(defun clean (p) (simp-terms (simp-vars p)))

;; Pass 2.
;; Simplifies the terms in a polynomial by summing collected like terms.
(defun simp-terms (p)
  (let ((poly 
  (simplifier p combine-terms vars= (lambda (x) (vars x)))))
    (cond ((equal no-vars poly) empty)
	  (t poly))))

;; Generic simplifier function used by simp-terms and simp-vars.
;; Takes a list you want to simplify, 
;; a combiner to perform the summing step to combine the like terms/vars 
;; into one,
;; a test of equality, either t= or vars= for collecting like terms/vars,
;; and a selector to get inside the term/variable to compare for likeness.
(defun simplifier (p combiner test selector)
  (cond ((null p) empty)
	(t (let ((simplified ;; save it in "simplified"
		   (combiner ;; combine like terms/vars into one
			       (collectlike ;; collect like terms/vars
				 (pcar p)    ;; those that are like 1st term/var
				 p 	    ;; in the whole poly/var list
				 test       ;; using t=/vars= to compare
				 selector)))) ;; selecting vars/power
	     (cond ((null simplified) empty)
		   (t (cons simplified ;; build a list of simplified terms/vars
		      (simplifier
			(removelike simplified 
				(pcdr p) test selector)
				  combiner test selector))))))))

;; Combines like terms into one term by summing coefficients
(defun combine-terms (lterms)
  (let ((combined-coef (accumulate + 0 (map coef lterms))))
    (cond ((zerop combined-coef) empty)
	  (t (mk-term combined-coef (vars (pcar lterms)))))))

;; Produces a list of terms/variables that are like x in list p
(defun collectlike (x p test selector)
  (cond ((null p) empty)
	((null x) empty)
	((test (selector x) (selector (pcar p)))
	 (cons (pcar p) (collectlike x (pcdr p) test selector)))
	(t (collectlike x (pcdr p) test selector))))

;; Pass 1.
;; Simplifies the variables in a polynomial by summing collected like 
;; variables.
(defun simp-vars (p)
  (cond ((null p) empty)
	((constantp (pcar p)) (cons (pcar p) (simp-vars (pcdr p)))) 
	(t (cons (mk-term (coef (pcar p))
			  (simplifier (vars (pcar p))
				      combine-vars 
				      equal 
				      (lambda (v) (vcar v))))
			  (simp-vars (pcdr p))))))

;; Combines like variables into one variable by summing powers
(defun combine-vars (lvars)
  (let ((combined-power (accumulate + 0 (map power lvars))))
    (cond ((zerop combined-power) empty)
	  (t (mk-var (letter (vcar lvars)) combined-power)))))

;; Produces a list of terms/variables that are not like x in list poly
(defun removelike (x p test selector)
  (cond ((null p) empty)
	((null x) empty)
	((test (selector x) (selector (pcar p))) 
	 (removelike x (pcdr p) test selector))
	(t (cons (car p) (removelike x (pcdr p) test selector)))))

;;; ---------------------------------------------------------------------------
;;; Functions for p-, p* and simplifier

;; Negates the coefficients in a polynomial by multiplying each by -1.
(defun negate (p) (map (lambda (x) (mk-term (* -1 (coef x)) (vars x))) p))

;; Algorithm:
;; For each term in p1, for each term in p2 multiply terms using t*.
;; Then accumulate each cartesian pair into one polynomial with append.
(defun pmult (p1 p2)
  (accumulate append empty (mmap t* p1 p2)))

;; Make a term by multiplying coefficients and just appending variable lists.
;; We'll leave the job of summing variables to (simp-vars) in the (clean) step.
(defun t* (t1 t2)
 (mk-term (* (coef t1) (coef t2))
	  (cond ((and (constantp t1) (constantp t2)) no-vars) 
	        ((constantp t1) (vars t2))
		((constantp t2) (vars t1))
		(t (append (vars t1) (vars t2))))))

;; Asks if coefficients and variables of t1 and t2 are equal using vars=.
(defun t= (t1 t2)
  (cond ((and (constantp t1) (constantp t2)) (= (coef t1) (coef t2)))
	(t (and (= (coef t1) (coef t2))
		(vars= (vars t1) (vars t2))))))

;; Asks if variables of vs1 and vs2 are equal using same method as pequal.
;; Uses v= to actually compare individual variables.
(defun vars= (vs1 vs2) (cond ((and (null vs1) (null vs2)) t)
			     ((and (equal no-vars vs1) (equal no-vars vs2)) t)
			     ((or (equal no-vars vs1) (equal no-vars vs2)) nil)
			     (t (and (= (length vs1) (length vs2))
				     (all (map any (mmap v= vs1 vs2)))))))

;; Asks if v1 and v2 are equal
(defun v= (v1 v2) 
  (and (equal (letter v1) (letter v2))
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
(defun mk-term (coeff variabs) (cons coeff (cons variabs empty)))

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

;; Asks if all the values in list are true (not nil)
(defun all (list)
  (cond ((null list) t)
	(else (and (not (equal nil (car list))) (all (cdr list))))))

;; Asks if any of the values in list are true (not nil)
(defun any (list)
  (cond ((null list) nil)
	(else (or (not (equal nil (car list))) (any (cdr list))))))

;; Nested map abbreviation
(defun mmap (f l1 l2) (map (lambda (x) (map (lambda (y) (f x y)) l2)) l1))

;; Aliases to (hopefully) make code clearer
(setq pcar car) (setq pcdr cdr) (setq coef car) (setq vars cadr) 
(setq vcar car) (setq vcdr cdr) (setq letter car) (setq power cadr) 
(setq empty '()) (setq no-vars '(())) ;; (equal (vars term) no-vars) - constant
