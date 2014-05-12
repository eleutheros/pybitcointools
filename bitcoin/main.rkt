#lang racket
(require (planet vyzo/crypto:2:3))
(require json)
(require math)

;;Elliptic curve parameters (secp256k1)
(define P 115792089237316195423570985008687907853269984665640564039457584007908834671663)
(define N 115792089237316195423570985008687907852837564279074904382605163141518161494337)
(define A 0)
(define B 7)
(define Gx 55066263022277343669578718895168534326250603453777594175500187360389116729240)
(define Gy 32670510020758816978083085130507043184471273380659243275938904335757337482424)
(define G (cons Gx Gy))

;;Base switching funcs
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
  (if (>= (bytes-length msg) length)
      msg
      (bytes-append (make-bytes (- length (bytes-length msg)) symbol)
                    msg)))

(define (encode-iter val base code result)
  (if (> val 0)
      (encode-iter (quotient val base) 
                   base 
                   code 
                   (bytes-append (bytes (bytes-ref code (modulo val base))) result))
      result))
      
(define (encode val base (minlen 0))
      (lpad (encode-iter val base (get-code-string base) #"")
            (bytes-ref (get-code-string base) 0)
            minlen))

(define (bytes-find bytez n (i 0))
  (cond [(>= i (bytes-length bytez)) -1]
        [(= (bytes-ref bytez i) n) i]
        [else (bytes-find bytez n (+ i 1))]))

(define (decode-iter bytez code-string i base result)
  (if (= (bytes-length bytez) i)
      result
      (decode-iter bytez 
                   code-string 
                   (+ i 1) 
                   base 
                   (+ (* result base) 
                      (bytes-find code-string (bytes-ref bytez i))))))

(define (decode bytez base)
  (decode-iter bytez (get-code-string base) 0 base 0))

(define (change-base string from to (minlen 0))
  (encode (decode string from) to minlen))

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
                       [(m) (modulo (* (- b1 a1) (modular-inverse (- b0 a0) P)) P)]
                       [(x) (modulo (- (* m m) a0 b0) P)]
                       [(y) (modulo (- (* m (- a0 x)) a1) P)])
           (cons x y))]))

(define (double-point a)
  (if (is-inf? a)
      inf
      (let*-values ([(a0 a1) (get-parts a)]
                    [(m) (% (* (+ A (* 3 a0 a0)) (modular-inverse (* 2 a1) P)) P)]
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

;;;Functions for handling pubkey and privkey formats.

(define (get-pubkey-format pub)
  (if  (pair? pub)
       'point
       (case (bytes-length pub)
         [(65) 'bin]
         [(130) 'hex]
         [(33) 'bin-compr]
         [(66) 'hex-compr]
         [(64) 'bin-electrum]
         [(128) 'hex-electrum]
         [else (raise-argument-error 'get-pubkey-format "Invalid pubkey format!" pub)])))
               
(define (encode-pubkey pub format)
  (let*-values ([(pub) (decode-pubkey pub)]
                [(p0 p1) (get-parts pub)])
    (case format
      [(point) pub] ;no change to decoded pubkey (why the fuck would you use an encode function to decode somthing? lol)
      [(bin) (bytes-append #"\4" (encode p0 256 32) (encode p1 256 32))]
      [(bin-compr) (bytes-append (bytes (+ 2 (% p1 2))) (encode p0 256 32))]
      [(hex) (bytes-append #"04" (encode p0 16 64) (encode p1 16 64))]
      [(hex-compr) (bytes-append #"0" (string->bytes/utf-8 (~a (+ 2 (% p1 2)))) (encode p0 16 64))]
      [(bin-electrum) (bytes-append (encode p0 256 32) (encode p1 256 32))]
      [(hex-electrum) (bytes-append (encode p0 16 64) (encode p1 16 64))]
      [else (raise-argument-error 'encode-pubkey "Invalid format for encoding pubkey!" format)])))

;;decoded pubkeys are conses of two large ints, a.k.a. points
(define (decode-pubkey pub)
  (case (get-pubkey-format pub)
    [(point) pub] ;already decoded... I hope I'm not retarded enough to need this
    [(bin) (cons (decode (subbytes pub 1 33) 256) (decode (subbytes pub 33 65) 256))]
    [(bin-compr)
     (let* ([x (decode (subbytes pub 1 33) 256)]
            [beta (modular-expt (+ (* x x x) 7) (/ (+ P 1) 4) P)]
            [y (if (odd? (+ beta (bytes-ref pub 0))) (- P beta) beta)])
       (cons x y))]
    [(hex) (decode-pubkey (encode (decode pub 16) 256 65))]
    [(hex-compr) (decode-pubkey (encode (decode pub 16) 256 33))]
    [(bin-electrum) (decode-pubkey (bytes-append #"\4" pub))] ;electrum stuff is just missing the leading 1 or two bytes
    [(hex-electrum) (decode-pubkey (bytes-append #"04" pub))]))

(define (get-privkey-format priv)
  (if (exact-integer? priv)
      'decimal
      (case (bytes-length priv)
        [(32) 'bin]
        [(33) 'bin-compr]
        [(64) 'hex]
        [(66) 'hex-compr]
        [else
         (let* ([binp (b58check->bin priv)]
                [len (bytes-length binp)])
           (case len
             [(32) 'wif]
             [(33) 'wif-compr]
             [else (raise-argument-error 'get-privkey-format "WIF does not represent privkey" privkey)]))])))

;;decoded privkeys are just huge ints.
(define (encode-privkey priv format (vbyte 0))
  (if (not (exact-integer? priv))
      (encode-privkey (decode-privkey priv) format vbyte)
      (case format
        [('decimal) priv]
        [('bin) (encode priv 256 32)]
        [('bin-compr) (bytes-append (encode priv 256 32) #"\1")]
        [('hex) (encode prive 16 64)]
        [('hex-compr) (bytes-append (encode priv 16 64) #"01")]
        [('wif) (bin->b58check (encode priv 256 32) (+ 128 vbyte))]
        [('wif-compr) (bin->b58check (bytes-append (encode priv 256 32) #"\1") (+ 128 vbyte))]
        [else (raise-argument-error 'encode-privkey "Invalid format!" format)])))

;;encoded privkeys are bytes.
(define (decode-privkey priv)
  (let ([format (get-privkey-format priv)])
    (case format
      [('decimal) priv]
      [('bin) (decode priv 256)]
      [('bin-compr) (decode (subbytes priv 0 32) 256)]
      [('hex) (decode priv 16)]
      [('hex-compr) (decode (subbytes priv 0 64) 16)]
      [('wif) (decode (b58check->bin priv) 256)]
      [('wif-compr) (decode (subbytes (b58check->bin priv) 0 32) 256)])))

(define (add-pubkeys p1 p2)
  (let ([format (get-pubkey-format p1)])
    (encode-pubkey (add-points (decode-pubkey p1) (decode-pubkey p2)) format)))

(define (add-privkeys p1 p2)
  (let ([format (get-privkey-format p1)])
    (encode-privkey (+ (decode-privkey p1) (decode-privkey p2)) format)))
  
(define (multiply pub priv)
  (let ([format (get-pubkey-format pub)]
        [pub (decode-pubkey pub)]
        [priv (decode-privkey priv)])
    (if (and (not (is-inf? pub))
             (not (= (% (- (expt (cdr pub) 2) ;make sure the pubkey is on our curve
                           (expt (car pub) 3) ;y^2 = x^3 + ax + b
                           (* a (car pub))    ;y^2 - x^3 - ax - b = 0 (mod P)
                           b) 
                        P) 
                     0)))
        (raise-argument-error 'multiply "Point not on curve" pub)
        (encode-pubkey (multiply-point pub priv) format))))

(define (divide pub priv)
  (let ([factor (inv (decode-privkey priv) N)])
    (multiply pub factor)))

(define (compress pub)
  (case (get-pubkey-format pub)
    [('bin) (encode-pubkey  pub 'bin-compr)]
    [('hex 'decimal) (encode-pubkey pub 'hex-compr)]
    [else pub]))
