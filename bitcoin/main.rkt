#lang racket
(require (planet vyzo/crypto:2:3))
(require json)
(require math)

;;Elliptic curve parameters (secp256k1)
(define P 115792089237316195423570985008687907853269984665640564039457584007908834671643)
(define N 115792089237316195423570985008687907852837564279074904382605163141518161494337)
(define A 0)
(define B 0)
(define Gx 55066263022277343669578718895168534326250603453777594175500187360389116729240)
(define Gy 32670510020758816978083085130507043184471273380659243275938904335757337482424)
(define G (cons Gx Gy))

;;Extended Euclidean Algorithm
(define (inv-iter lm hm low high)
  (if (low . > . 1)
      (let* ((r (quotient high low))
             (nm (- hm (* r lm)))
             (new (- high (* r low))))
        (inv-iter nm new lm low))
      lm))

(define (inv a n)
  (let-values ([(lm hm low high) (values 1 0 (modulo a n) n)])
    (modulo (inv-iter lm hm low high) n)))

;;Base switching and utility funcs
(define (append1 lst n)
  (append lst (list n)))

(define (range start stop)
  (if (= start stop)
      empty
      (cons start (range (+ start 1) stop))))

(define (get-code-string base)
  (case base
    [(2) #"01"]
    [(10) #"0123456789"]
    [(16) #"0123456789ABCDEF"]
    [(32) #"abcdefghijklmnopqrstuvwxyz234567"]
    [(58) #"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"]
    [(256) (apply bytes (range 0 256))]
    [else (raise-argument-error 'get-code-string "2, 10, 16, 32, 58, or 256" base)]))

(define (lpad msg symbol length)
  (if ((bytes-length msg) . >= . length)
      msg
      (bytes-append (make-bytes (length . - . (bytes-length msg)) symbol)
                    msg)))

(define (encode-iter val base code result)
  (if (val . > . 0)
      (encode-iter (quotient val base) 
                   base 
                   code 
                   (bytes-append (bytes (bytes-ref code (modulo val base))) result))
      result))
      
(define (encode val base #:minilen [minlen 0])
      (lpad (encode-iter val base (get-code-string base) #"")
            (bytes-ref (get-code-string base) 0)
            minlen))

(define (bytes-find string n #:i [i 0])
  (cond [(= (bytes-ref string i) n) i]
        [(> i (bytes-length string)) -1]
        [else (bytes-find string n #:i (+ i 1))]))

(define (decode-iter string code-string i base result)
  (if ((bytes-length string) . <= . i)
      result
      (decode-iter string 
                   code-string 
                   (+ i 1) 
                   base 
                   (+ (* result base) 
                      (bytes-find code-string (bytes-ref string i))))))

(define (decode string base)
  (decode-iter string (get-code-string base) 0 base 0))

(define (change-base string from to #:minlen [minlen 0])
  (encode (decode string from) to #:minlen minlen))

;;Eliptic curve arithmetic functions
(define inf (cons 0 0))

(define % modulo)

(define (is-inf? p)
  (equal? p inf))

(define (get-parts #:acc [acc empty] . points)
  (if (empty? points)
      (apply values acc)
      (keyword-apply get-parts '(#:acc) (list (append acc (list (caar points) (cdar points)))) (cdr points))))

(define (add-points a b)
  (cond [(is-inf? a) b]
        [(is-inf? b) a]
        [(equal? a b) (double-point a)]
        [(= (car a) (car b)) inf]
        [else
         (let*-values ([(a0 a1 b0 b1) (get-parts a b)]
                       [(m) (modulo (* (- b1 a1) (inv (- b0 a0) P)) P)]
                       [(x) (modulo (- (* m m) a0 b0) P)]
                       [(y) (modulo (- (* m (- a0 x)) a1) P)])
           (cons x y))]))

(define (double-point a)
  (if (is-inf? a)
      inf
      (let*-values ([(a0 a1) (get-parts a)]
                    [(m) (% (* (+ A (* 3 a0 a0)) (inv (* 2 a1) P)) P)]
                    [(x) (% (- (* m m) (* 2 a0)) P)]
                    [(y) (% (- (* m (- a0 x)) a1) P)])
        (cons x y))))

(define (multiply-point a n)
  (cond [(is-inf? a) inf]
        [(= 0 n) inf]
        [(= 1 n) a]
        [(or (< n 0) (<= N n)) (multiply-point a (% n N))]
        [(even? n) (double-point (multiply-point a (/ n 2)))]
        [(odd? n) (add-points a (multiply-point a (- n 1)))]))

;;Functions for handling pubkey and privkey formats.
(define (get-pubkey-format pub)
  (if  (pair? pub)
       'point
       (let ((l (bytes-length pub)))
         (cond [(and (= l 65) (= (bytes-ref pub 0) 4))
                'bin]
               [(and (= l 130) (= (subbytes pub 0 2) #"04"))
                'hex]
               [(and (= l 33) (member (bytes-ref pub 0) '(2 3)))
                'bin-compr]
               [(and (= l 66) (member (subbytes pub 0 2) '(#"02" #"03")))
                'hex-compr]
               [(= l 64) 'bin-electrum]
               [(= l 128) 'hex-electrum]
               [else (raise-argument-error 'get-pubkey-format "pubkey in valid format" pub)]))))
               
(define (encode-pubkey pub format)
  (let*-values ([(pub) (if (not (pair? pub)) (decode-pubkey pub) pub)]
                [(p0 p1) (get-parts pub)])
    (case format
      [('point) pub]
      [('bin) (bytes-append #"\4" (encode p0 256 #:minlen 32) (encode p1 256 #:minlen 32))]
      [('bin-compr) (bytes-append (bytes (+ 2 (% p1 2))) (encode p1 256 #:minlen 32))]
      [('hex) (bytes-append #"04" (encode p0 16 #:minlen 64) (encode p1 16 #:minlen 64))]
      [('hex-compr) (bytes-append #"0" (integer->integer-bytes (+ 2 (% p1 2))) (encode p1 16 #:minlen 64))]
      [('bin-electrum) (bytes-append (encode p0 256 #:minlen 32) (encode p1 256 #:minlen 32))]
      [('hex-electrum) (bytes-append (encode p0 16 #:minlen 64) (encode p1 16 #:minlen 64))]
      [else (raise-argument-error 'encode-pubkey "pubkey in valid format" format)])))

(define (bytes-empty? bytez)
  (= (bytes-length bytez) 0))

(define (correct n)
  (if (< 47 n 59)
      (- n 48)
      (- n 55)))

(define (hex->ascii bytez #:acc [acc #""])
  (if (bytes-empty? bytez) 
      acc
      (let* ([a (correct (bytes-ref bytez 0))]
             [b (correct (bytes-ref bytez 1))]
             [hex (+ (* a 16) b)])
        (hex->ascii (subbytes bytez 2) #:acc (bytes-append acc (bytes hex))))))
        
(define (decode-pubkey pub #:format [format 'None])
  (let ((format (if (equal? format 'None) (get-pubkey-format pub) format)))
    (case format
      [('point) pub]
      [('bin) (cons (decode (subbytes pub 1 33) 256) (decode (subbytes pub 33 65) 256))]
      [('bin-compr)
       (let* ([x (decode (subbytes pub 1 33) 256)]
              [β (modular-expt (+ (* x x x) 7) (/ (+ P 1) 4) P)]
              [y (if (odd? (+ β (bytes-ref pub 0))) (- P β) β)])
         (cons x y))]
      [('hex) (cons (decode (subbytes pub 2 66) 16) (decode (subbytes pub 66 130) 16))]
      [('hex-compr) (decode-pubkey (hex->ascii pub) 'bin-compr)]
      [('bin-electrum) (cons (decode (subbytes pub 0 32) 256) (decode (subbytes pub 32 64) 256))]
      [('hex-electrum) (cons (decode (subbytes pub 0 64) 16) (decode (subbytes pub 64 128) 16))]
      [else (raise-argument-error 'decode-pubkey "pubkey in valid format" format)])))