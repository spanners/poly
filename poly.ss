(define (p+ p1 p2) (clean (append p1 p2)))
(define (p- p1 p2) (p+ p1 (negate p2)))
(define (p* p1 p2) (clean (pmult p1 p2)))
(define (p= p1 p2) (null? (p- p1 p2)))

(define (clean p) (simp-terms (simp-vars p)))

(define (simp-terms p)
  (let ((poly
  (simplifier p combine-terms vars= (lambda (term) (vars term)))))
    (cond ((no-vars? poly) empty)
	  (else poly))))

(define (simplifier p combiner eq-test? selector)
  (cond ((null? p) empty)
	(else (let ((simplified 
		      (combiner (collect-like (pcar p) p eq-test? selector))))
	     (cond ((null? simplified) empty)
		   (else (cons simplified
		      (simplifier
			(remove-like simplified (pcdr p) eq-test? selector)
				  combiner eq-test? selector))))))))

(define (combine-terms like-terms)
  (let ((combined-coef (accumulate + 0 (map coef like-terms))))
    (cond ((zero? combined-coef) empty)
	  (else (mk-term combined-coef (vars (pcar like-terms)))))))

(define (fold-right f end l) (if (null? l) end
    (f (car l) (fold-right f end (cdr l)))))

(define (pfilter eq-test? poly selector tm)
  (fold-right (lambda (x acc) (if (eq-test? (selector x) (selector tm)) (cons x acc) acc)) '() poly))

(define (collect-like x p eq-test? selector)
  (pfilter eq-test? p selector x))

(define (remove-like x p eq-test? selector)
  (pfilter (lambda (a b) (not (eq-test? a b))) p selector x))

(define (simp-vars p)
  (cond ((null? p) empty)
	((constant? (pcar p)) (cons (pcar p) (simp-vars (pcdr p))))
	(else (cons (mk-term (coef (pcar p))
			  (simplifier (vars (pcar p))
				      combine-vars
				      equal?
				      (lambda (v) (vcar v))))
			  (simp-vars (pcdr p))))))

(define (combine-vars like-vars)
  (let ((combined-power (accumulate + 0 (map power like-vars))))
    (cond ((zero? combined-power) empty)
	  (else (mk-var (letter (vcar like-vars)) combined-power)))))

(define (negate p) (map (lambda (x) (mk-term (* -1 (coef x)) (vars x))) p))

(define (pmult p1 p2)
  (accumulate append empty (cartesian-map term* p1 p2)))

(define (term* t1 t2)
 (mk-term (* (coef t1) (coef t2))
	  (cond ((and (constant? t1) (constant? t2)) no-vars) 
	        ((constant? t1) (vars t2))
		((constant? t2) (vars t1))
		(else (append (vars t1) (vars t2))))))

(define (vars= vs1 vs2) (cond ((and (null? vs1) (null? vs2)) #t)
			     ((and (no-vars? vs1) (no-vars? vs2)) #t)
			     ((or (no-vars? vs1) (no-vars? vs2)) #f)
			     (else (and (= (length vs1) (length vs2))
				     (all-true? (map any-true? (cartesian-map v= vs1 vs2)))))))

(define (v= v1 v2) 
  (and (equal? (letter v1) (letter v2))
		       (= (power v1) (power v2))))

(define (mk-term coeff variabs) (cons coeff (cons variabs empty)))

(define (mk-var ltr pow) (mk-term ltr pow))

(define (constant? term)
  (cond ((null? term) #f)
	((null? (coef term)) #f)
	(else (and (integer? (coef term)) 
		(no-vars? (vars term))))))

(define (all-true? list)
  (cond ((null? list) #t)
	(else (and (not (equal? #f (car list))) (all-true? (cdr list))))))

(define (any-true? list)
  (cond ((null? list) #f)
	(else (or (not (equal? #f (car list))) (any-true? (cdr list))))))

(define (no-vars? x)
  (equal? no-vars x))

(define (accumulate combiner null-value list) 
  (cond ((null? list) null-value) 
	(else (combiner (car list) (accumulate combiner null-value (cdr list))))))

(define (cartesian-map f l1 l2) (map (lambda (x) (map (lambda (y) (f x y)) l2)) l1))

(define pcar car)
(define pcdr cdr)
(define coef car)
(define vars cadr)
(define vcar car)
(define vcdr cdr)
(define letter car)
(define power cadr)
(define empty '())
(define no-vars '(()))
