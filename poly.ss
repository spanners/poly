(define (p+ p1 p2) (clean (append p1 p2)))
(define (p- p1 p2) (p+ p1 (negate-poly p2)))
(define (p* p1 p2) (clean (foldr append '() (cartesian-map term* p1 p2))))
(define (p= p1 p2) (null? (p- p1 p2)))

(define (clean p) (simp-terms (simp-vars p)))

(define (simp-terms p)
  (simplify p combine-terms vars= (lambda (term) (vars term))))

(define (simplify p combiner eq-test? selector)
  (define (simplify-helper p result)
    (if (null? p) result
        (let ((simplified
               (combiner (collect-like (pcar p) p eq-test? selector))))
          (if (null? simplified) result
              (simplify-helper
               (remove-like simplified (pcdr p) eq-test? selector)
               (cons simplified result))))))
  (simplify-helper p '()))

(define (combine-terms like-terms)
  (let ((combined-coef (foldr + 0 (map coef like-terms))))
    (if (zero? combined-coef) '()
        (mk-term combined-coef (vars (pcar like-terms))))))

(define (collect-like x p eq-test? selector)
  (filter (lambda (a) (eq-test? (selector a) (selector x))) p))

(define (remove-like x p eq-test? selector)
  (collect-like x p (lambda (a b) (not (eq-test? a b))) selector))

(define (simp-vars p)
  (define (simp-vars-helper p result)
    (cond ((null? p) result)
          ((constant? (pcar p)) (cons (pcar p) (simp-vars (pcdr p))))
          (else (simp-vars-helper
                 (pcdr p)
                 (cons (mk-term (coef (pcar p))
                                (simplify (vars (pcar p))
                                          combine-vars
                                          equal?
                                          (lambda (v) (vcar v))))
                       result)))))
  (simp-vars-helper p '()))

(define (combine-vars like-vars)
  (let ((combined-pow (foldr + 0 (map power like-vars))))
    (if (zero? combined-pow) '()
        (mk-var (letter (vcar like-vars)) combined-pow))))

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
                   (all-true? (map any-true? (cartesian-map v= vs1 vs2)))))))

(define (v= v1 v2) 
  (and (equal? (letter v1) (letter v2)) (= (power v1) (power v2))))

(define (negate-poly p) (map (lambda (x) (mk-term (* -1 (coef x)) (vars x))) p))

(define (mk-term coeff variabs) (cons coeff (cons variabs '())))

(define (mk-var ltr pow) (mk-term ltr pow))

(define (constant? term)
  (cond ((null? term) #f)
        ((null? (coef term)) #f)
        (else (and (integer? (coef term)) 
                   (no-vars? (vars term))))))

(define (all-true? l) 
  (foldr (lambda (x xs) (and (not (equal? #f x)) xs)) #t l))

(define (any-true? l) 
  (foldr (lambda (x xs) (or (not (equal? #f x)) xs)) #f l))

(define (cartesian-map f l1 l2)
  (map (lambda (x) (map (lambda (y) (f x y)) l2)) l1))

(define (no-vars? x) (equal? no-vars x)) (define pcar car) (define pcdr cdr) 
(define coef car) (define vars cadr) (define vcar car) (define vcdr cdr) 
(define letter car) (define power cadr) (define no-vars '(()))

(load "tests.ss")
