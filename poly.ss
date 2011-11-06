;;(define this-file "poly.ss")
;;(define tests "tests.ss")
;;(define rl (load this-file))
;;(define tst (load tests))

;;; ---------------------------------------------------------------------------
;;; Polynomial operators.
(define (p+ p1 p2) (clean (append p1 p2)))
(define (p- p1 p2) (p+ p1 (negate p2)))
(define (p* p1 p2) (clean (pmult p1 p2)))
(define (p= p1 p2) (null? (p- p1 p2)))

;;; ---------------------------------------------------------------------------
;;; Functions for cleaning input before/after manipulation.
;; A 2-pass algorithm:
;; Pass 1: For each term, combine like variables into one variable, (simp-vars)
;; Pass 2: Combine like terms in whole polynomial into one term. (simp-terms)
(define (clean p) (simp-terms (simp-vars p)))

;; Pass 2.
;; Simplifies the terms in a polynomial by summing collected like terms.
(define (simp-terms p)
  (let ((poly 
  (simplifier p combine-terms vars= (lambda (term) (vars term)))))
    (cond ((equal? no-vars poly) empty)
	  (else poly))))

;; Generic simplifier function used by simp-terms and simp-vars.
;; Takes a poly p you want to simplify, 
;; a combiner to perform the summing step to combine the like terms/vars 
;; into one,
;; a test of equality, either t= or vars= for collecting like terms/vars,
;; and a selector to get inside the term/variable to compare for likeness.
(define (simplifier p combiner eq-test selector)
  (cond ((null? p) empty)
	(else (let ((simplified ;; save it in "simplified"
		   (combiner ;; combine like terms/vars into one
			       (collect-like ;; collect like terms/vars
				 (pcar p)    ;; those that are like 1st term/var
				 p 	    ;; in the whole poly/var list
				 eq-test       ;; using t=/vars= to compare
				 selector)))) ;; selecting vars/power
	     (cond ((null? simplified) empty)
		   (else (cons simplified ;; build a list of simplified terms/vars
		      (simplifier
			(remove-like simplified 
				(pcdr p) eq-test selector)
				  combiner eq-test selector))))))))

;; Combines like terms into one term by summing coefficients
(define (combine-terms like-terms)
  (let ((combined-coef (accumulate + 0 (map coef like-terms))))
    (cond ((zero? combined-coef) empty)
	  (else (mk-term combined-coef (vars (pcar like-terms)))))))

;; Produces a list of terms/variables that are like x in poly p
(define (collect-like x p eq-test selector)
  (cond ((null? p) empty)
	((null? x) empty)
	((eq-test (selector x) (selector (pcar p)))
	 (cons (pcar p) (collect-like x (pcdr p) eq-test selector)))
	(else (collect-like x (pcdr p) eq-test selector))))

;; Pass 1.
;; Simplifies the variables in a polynomial by summing collected like 
;; variables.
(define (simp-vars p)
  (cond ((null? p) empty)
	((constant? (pcar p)) (cons (pcar p) (simp-vars (pcdr p)))) 
	(else (cons (mk-term (coef (pcar p))
			  (simplifier (vars (pcar p))
				      combine-vars 
				      equal? 
				      (lambda (v) (vcar v))))
			  (simp-vars (pcdr p))))))

;; Combines like variables into one variable by summing powers.
(define (combine-vars lvars)
  (let ((combined-power (accumulate + 0 (map power lvars))))
    (cond ((zero? combined-power) empty)
	  (else (mk-var (letter (vcar lvars)) combined-power)))))

;; Produces a list of terms/variables that are not like x in poly p.
(define (remove-like x p eq-test selector)
  (cond ((null? p) empty)
	((null? x) empty)
	((eq-test (selector x) (selector (pcar p))) 
	 (remove-like x (pcdr p) eq-test selector))
	(else (cons (car p) (remove-like x (pcdr p) eq-test selector)))))

;;; ---------------------------------------------------------------------------
;;; Functions for p-, p* and simplifier

;; Negates the coefficients in a polynomial by multiplying each by -1.
(define (negate p) (map (lambda (x) (mk-term (* -1 (coef x)) (vars x))) p))

;; Algorithm:
;; For each term in p1, for each term in p2 multiply terms using t*.
;; Then accumulate each cartesian pair into one polynomial with append.
(define (pmult p1 p2)
  (accumulate append empty (cartesian-map t* p1 p2)))

;; Make a term by multiplying coefficients and just appending variable lists.
;; We'll leave the job of summing variables to (simp-vars) in the (clean) step.
(define (t* t1 t2)
 (mk-term (* (coef t1) (coef t2))
	  (cond ((and (constant? t1) (constant? t2)) no-vars) 
	        ((constant? t1) (vars t2))
		((constant? t2) (vars t1))
		(else (append (vars t1) (vars t2))))))

;; Asks if coefficients and variables of t1 and t2 are equal using vars=.
(define (t= t1 t2)
  (cond ((and (constant? t1) (constant? t2)) (= (coef t1) (coef t2)))
	(else (and (= (coef t1) (coef t2))
		(vars= (vars t1) (vars t2))))))

;; Asks if variables of vs1 and vs2 are equal using same method as p=.
;; Uses v= to actually compare individual variables.
(define (vars= vs1 vs2) (cond ((and (null? vs1) (null? vs2)) #t)
			     ((and (equal? no-vars vs1) (equal? no-vars vs2)) #t)
			     ((or (equal? no-vars vs1) (equal? no-vars vs2)) #f)
			     (else (and (= (length vs1) (length vs2))
				     (all? (map any? (cartesian-map v= vs1 vs2)))))))

;; Asks if v1 and v2 are equal
(define (v= v1 v2) 
  (and (equal? (letter v1) (letter v2))
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
(define (mk-term coeff variabs) (cons coeff (cons variabs empty)))

;; A non-empty variable is a list of two elements.
;; First element is a letter
;; Second element is an number - a power the letter is raised to.
;; A variable may be raised to the power 0.
(define (mk-var ltr pow) (mk-term ltr pow))

;; Asks if term is a constant
;; A term is a constant if it has an integer coefficient, and no variables
(define (constant? term)
  (cond ((null? term) #f)
	((null? (coef term)) #f)
	(else (and (integer? (coef term)) 
		(equal? (vars term) no-vars)))))

;; Asks if all the values in list are true (not #f)
(define (all? l)
  (cond ((null? l) #t)
	(else (and (not (equal? #f (car l))) (all? (cdr l))))))

;; Asks if any of the values in list are true (not #f)
(define (any? l)
  (cond ((null? l) #f)
	(else (or (not (equal? #f (car l))) (any? (cdr l))))))

;; Combines all values in list into one value
(define (accumulate combiner null-value l) 
  (cond ((null? l) null-value) 
	(else (combiner (car l) (accumulate combiner null-value (cdr l))))))

;; Cartesian map abbreviation
(define (cartesian-map f l1 l2) (map (lambda (x) (map (lambda (y) (f x y)) l2)) l1))

;; Alias definitions to separate the polynomial representation from it's manipulation
;; Want change the representation? Just change what the alias does
(define pcar car) (define pcdr cdr) (define coef car) (define vars cadr) 
(define vcar car) (define vcdr cdr) (define letter car) (define power cadr) 
(define empty '()) (define no-vars '(()))
