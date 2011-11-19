(require srfi/1) 

(define (p+ p1 p2) (clean (append p1 p2)))
(define (p- p1 p2) (p+ p1 (negatep p2)))
(define (p* p1 p2) (clean (concatenate (cartesian-map term* p1 p2))))
(define (p= p1 p2) (null? (p- p1 p2)))

(define (clean p) (simp-terms (simp-vars p)))

(define (simp-terms p)
  (simplify p combine-terms vars= vars))

(define (simp-vars p)
  (define (simp-vars-helper p result)
    (cond ((null? p) result)
	  ((constant? (pcar p)) (simp-vars-helper (pcdr p) (cons (pcar p) result)))
	  (else (simp-vars-helper (pcdr p) 
				  (cons (mk-term (coef (pcar p)) 
						 (simplify (vars (pcar p)) combine-vars equal? vcar))
					result)))))
    (simp-vars-helper p '()))

(define (simplify p combiner eq-test? selector)
  (define (collect-like x p)
    (filter (λ (a) (eq-test? (selector a) (selector x))) p))
  (define (remove-like x p)
    (filter (λ (a) (not (eq-test? (selector a) (selector x)))) p))
  (define (simplify-helper p result)
    (if (null? p) result
      (let ((simplified (combiner (collect-like (pcar p) p))))
	(if (null? simplified) 
	  (simplify-helper (remove-like (pcar p) (pcdr p)) result)
	(simplify-helper (remove-like simplified (pcdr p)) (cons simplified result))))))
  (simplify-helper p '()))

(define (combine-terms like-terms)
  (let ((combined-coef (foldr + 0 (map coef like-terms))))
    (if (zero? combined-coef) '()
        (mk-term combined-coef (vars (pcar like-terms))))))

(define (combine-vars like-vars)
  (let ((combined-pow (foldr + 0 (map power like-vars))))
    (if (zero? combined-pow) '()
        (mk-var (letter (vcar like-vars)) combined-pow))))

(define (negatep p) (map (λ (x) (mk-term (* -1 (coef x)) (vars x))) p))

(define (term* t1 t2)
  (mk-term (* (coef t1) (coef t2))
           (cond ((and (constant? t1) (constant? t2)) no-vars) 
                 ((constant? t1) (vars t2))
                 ((constant? t2) (vars t1))
                 (else (append (vars t1) (vars t2))))))

(define (vars= vs1 vs2)
  (cond ((and (null? vs1) (null? vs2)) #t)
	((and (no-vars? vs1) (no-vars? vs2)) #t)
	((or (no-vars? vs1) (no-vars? vs2)) #f)
	(else (and (= (length vs1) (length vs2))
		   (every identity (map (λ (l) (any identity l)) (cartesian-map v= vs1 vs2)))))))

(define (v= v1 v2) 
  (and (equal? (letter v1) (letter v2)) (= (power v1) (power v2))))

(define (mk-term coeff variabs) (cons coeff (cons variabs '())))
(define (mk-var ltr pow) (mk-term ltr pow))

(define (no-vars? x) (equal? no-vars x))

(define (constant? term)
    (and (integer? (coef term)) 
	 (no-vars? (vars term))))

(define (cartesian-map f l1 l2) (map (λ (x) (map (λ (y) (f x y)) l2)) l1))

(define pcar car) (define pcdr cdr) (define coef car) (define vars cadr) (define vcar car) 
(define vcdr cdr) (define letter car) (define power cadr) (define no-vars '(()))

(load "tests.ss")
