(define (fold-right f end l)
  (if (null? l) end
    (f (car l) (fold-right f end (cdr l)))))

(define (fold-left f end l)
  (if (null? l) end
    (fold-left f (f end (car l)) (cdr l))))

(define (fold-right1 f l)
  (fold-right f (car l) (cdr l)))

(define (fold-left1 f l)
  (fold-left f (car l) (cdr l)))

(define (map f l)
  (fold-right (lambda (x lst) (cons (f x) lst)) '() l))

(define (length l)
  (fold-left (lambda (x lst) (+ x 1)) 0 l))

(define (reverse l)
  (fold-left (lambda (lst x) (cons x lst)) '() l))

(define (sum l)
  (fold-left (lambda (acc x) (+ acc x)) 0 l))

(define (product l)
  (fold-left (lambda (acc x) (* acc x)) 1 l))

(define (max l)
  (fold-left1 (lambda (x y) (if (> x y) x y)) l))

(define (min l)
  (fold-left1 (lambda (x y) (if (< x y) x y)) l))

(define (filter p l)
  (fold-right (lambda (x acc) (if (p x) (cons x acc) acc)) '() l))

(define (quicksort l)
  (if (< (length l) 2) l
    (let ((p (list-ref l (random (length l)))))
      (append (quicksort (filter (lambda (x) (< x p)) l))
	      (filter (lambda (x) (= x p)) l)
	      (quicksort (filter (lambda (x) (> x p)) l))))))
