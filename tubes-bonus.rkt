;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname tubes-bonus) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor mixed-fraction #f #t none #f () #t)))

;; ****************************************************************************

(require "lib-tubes.rkt")

;; A Game is (make-game Nat Nat (listof (listof Sym)))
(define-struct game (tubesize maxcolours tubes))

;; (check-colour? size num los) produces true if each symbol in the list [los]
;; appears exactly [size] times and if there are at most [num] different symbols
;; else, it produces false

;; check-colour?: Nat Nat (listof Sym) -> Bool
(define (check-colour? size num los)
  (local
    [;; (remove-first lst) removes all instances of the first element from [lst]
     ;; remove-first: (listof Sym) -> (listof Sym)
     (define (remove-first lst)
       (filter (lambda (x) (not (symbol=? (first lst) x))) lst))

     ;; (count-first lst) counts the number of times the first element appears in [lst]
     ;; count-first: (listof Sym) -> Nat
     (define (count-first lst)
       (foldl (lambda (x rror) (cond [(symbol=? (first lst) x) (+ 1 rror)]
                                     [else rror])) 0 lst))]
    (cond
      [(empty? los) true]
      [(or (<= num 0) (not (= (count-first los) size))) false]
      [else (check-colour? size (sub1 num) (remove-first los))])))


;; ****************************************************************************

;; (valid-game? gm) produces true if [gm] is a valid game, and false otherwise.
;; A Game is valid if:
; - All tubes have at most tubesize symbols in them
; - there are at most maxcolours different symbols
; - there are exactly tubesize occurrences of each different symbol

;; valid-game?: Game -> Bool
(define (valid-game? gm)
  (and (andmap (lambda (x) (<= (length x) (game-tubesize gm))) (game-tubes gm))
       (check-colour? (game-tubesize gm) (game-maxcolours gm)
                      (foldl append empty (game-tubes gm)))))

;; ****************************************************************************

;; (remove-completed gm) produces a Game similar to [gm] but has any completed
;; tubes removed. Where a "completed tube" is full of balls of the same colour.
;; After removing completed tubes, it updates maxcolours to be the number of colours left.

;; remove-completed: Game -> Game
;; Requires: gm is a valid game
(define (remove-completed gm)
  (local [;; (not-completed? tube) returns true if the tube is completed
          ;; not-completed?: (listof Sym) -> Bool
          (define (not-completed? tube)
            (or (< (length tube) (game-tubesize gm))
                (not (or (<= (length tube) 1)
                         (andmap (lambda (y) (symbol=? y (first tube))) (rest tube))))))]
    
    (make-game (game-tubesize gm)
               (- (game-maxcolours gm)
                  (foldl (lambda (x rror) (cond [(not-completed? x) rror]
                                                [else (add1 rror)])) 0 (game-tubes gm)))
               (filter not-completed? (game-tubes gm)))))


;; ****************************************************************************

;; (finished-game? gm) produces true if [gm] is a finished Game and false otherwise.
;; A Game is finished if all tubes are either empty or full with balls of the same colour
;; Or if there are no tubes

;; finished-game?: Game -> Bool
(define (finished-game? gm)
  (or (empty? (game-tubes (remove-completed gm)))
      (andmap (lambda (x) (empty? x)) (game-tubes (remove-completed gm)))))

;; ****************************************************************************

;; (num-blocks llos) produces the number of "blocks" contained in [llos]
;;  A block is a consecutive sequence of identical symbols within one list

;; num-blocks: (listof (listof Sym)) -> Nat
(define (num-blocks llos)
  (local
    [(define (num-blocks-single los)
       (cond
         [(or (boolean? los) (empty? los)) 0]
         [(= (length los) 1) 1]
         [else (+ 1 (num-blocks-single (memf (lambda (x) (not (symbol=? (first los) x))) los)))]))]
    (apply + (map num-blocks-single llos))))


;; ****************************************************************************

;; (equiv-game? gm1 gm2) produces true if [gm1] and [gm2] are equivalent,
;; and false otherwise.
;; Two games are equivalent if they have the same maxcolour, tubesize,  number of
;; tubes and the tubes contain identical balls in identical order within the tube.
;; The ordering of the tubes may be different


;; equiv-game?: Game Game -> Bool
(define (equiv-game? gm1 gm2)
  (local
    [;; (has-tubes-of tubes1 tubes2) returns true if all tubes of tubes1 are in tubes2
     ;; has-tubes-of: (listof (listof Sym)) (listof (listof Sym)) -> Bool
     (define (has-tubes-of tubes1 tubes2)
       (andmap (lambda (tube) (ormap (lambda (y) (equal? y tube)) tubes2)) tubes1))]
    
    (and (= (game-maxcolours gm1) (game-maxcolours gm2))
         (= (game-tubesize gm1) (game-tubesize gm2))
         (= (length (game-tubes gm1)) (length (game-tubes gm2)))
         (has-tubes-of (game-tubes gm1) (game-tubes gm2))
         (has-tubes-of (game-tubes gm2) (game-tubes gm1))
         (= (length (game-tubes gm1)) (length (game-tubes gm2))))))


;; ****************************************************************************

;; (all-equiv? log1 log2) produces true if every game in [log1] has one equivalent
;; game in [log2], and every game in log2 has one equivalent game in log1,
;; and false otherwise.


;; all-equiv?: (listof Game) (listof Game) -> Bool
(define (all-equiv? log1 log2)
  (local
    [;; (is-subset-of log1 log2) produces true if all games in [log1] are present in [log2]
     ;; is-subset-of: (listof Game) (listof Game) -> Bool
     (define (is-subset-of log1 log2)
       (andmap (lambda (game) (ormap (lambda (y) (equiv-game? y game)) log2)) log1))]
    
    (and (is-subset-of log1 log2)
         (is-subset-of log2 log1)
         (= (length log1) (length log2)))))

;; ****************************************************************************

;; (next-games gm) produces a list of Games that can happen by moving one ball from gm
;; next-games: Game -> (listof Game)
(define (next-games gm)
  (foldr (lambda (tube-no rror) (append (gms-after-removing tube-no gm) rror))
         empty (sort-removals (build-list (length (game-tubes gm)) (lambda (x) x)) gm)))


;; for every tube index except the one being removed from
(define (gms-after-removing tube-no gm)
  (foldr (lambda (new-tube rror) (cond [(false? (new-gm tube-no new-tube gm)) rror]
                                       [else (cons (new-gm tube-no new-tube gm) rror)]))
         empty (remove tube-no (build-list (length (game-tubes gm)) (lambda (x) x)))))


;; produces a game where the top element of tube-no has been moved to new-tube
(define (new-gm tube-no new-tube gm)
  ((lambda (val)
     (cond [(false? val) false]
           [else
            (make-game (game-tubesize gm)
                       (game-maxcolours gm)
                       val)]))
   (foldr (lambda (x rror)
            ; new-tube is full
            (cond [(= (game-tubesize gm) (length (list-ref (game-tubes gm) new-tube))) false]
                  ; if the tube-no tube is empty
                  [(empty? (list-ref (game-tubes gm) tube-no)) false]
                  [(= x tube-no) (cons (rest (list-ref (game-tubes gm) x)) rror)]
                  [(= x new-tube)
                   (cons (cons (first (list-ref (game-tubes gm) tube-no))
                               (list-ref (game-tubes gm) new-tube)) rror)]
                  ; do not move ball to duplicate tubes
                  [(ormap (lambda (x) (equal? (list-ref (game-tubes gm) x)
                                              (list-ref (game-tubes gm) new-tube)))
                          (build-list new-tube (lambda (y) y))) rror]
                  [else (cons (list-ref (game-tubes gm) x) rror)]))     
          empty (build-list (length (game-tubes gm)) (lambda (x) x)))))

;; ****************************************************************************

(define (sort-games log)
  ; lambda will return whether the first game will take less time than second
  (quicksort log (lambda (gm1 gm2) (> (points (game-tubes gm1)) (points (game-tubes gm2))))))

(define (points tube-lst)
  (foldl (lambda (tube rror)
           (+ rror (points-t tube))) 0 tube-lst))

(define (points-t tube)
  (local [(define rev (reverse tube))]
    (- (length tube)
       (length ((lambda (val)
                  (cond [(boolean? val) empty]
                        [else val]))
                (memf (lambda (x) (not (symbol=? x (first rev)))) rev))))))


;; (sort-removals) sorts tubes in order of removal/ not-completed
(define (sort-removals indices gm)
  (local
    [(define (not-completed? tube)
       (or (< (length (list-ref (game-tubes gm) tube)) (game-tubesize gm))
           (not (or (<= (length (list-ref (game-tubes gm) tube)) 1)
                    (andmap (lambda (y) (symbol=? y (first (list-ref (game-tubes gm) tube))))
                            (rest (list-ref (game-tubes gm) tube)))))))]
    (quicksort indices (lambda (tube1 tube2) (cond [(not-completed? tube2) false]
                                                   [(not-completed? tube1) true]
                                                   [else false])))))

;; ****************************************************************************

;; (solve gm draw-option) determines if the game gm is solveable,
;; and will also draw each possible move depending on the draw-option

;; solve: Game (anyof 'off 'norm 'slow 'fast) -> Bool
(define (solve gm draw-option)
  (local
    [(define setup (puzzle-setup gm draw-option))                
     (define (solve-helper to-visit visited)
       (cond
         [(empty? to-visit) false]
         [else
          (local
            [(define draw (draw-board (first to-visit) draw-option))] 
            (cond
              [(finished-game? (first to-visit)) true]
              [(member? (first to-visit) visited)
               (solve-helper (rest to-visit) visited)]
              [else
               (local [(define nbrs (sort-games (next-games (first to-visit))))
                       (define new (filter (lambda (x) (not (member? x visited))) nbrs))
                       (define new-to-visit (append new (rest to-visit)))
                       (define new-visited (cons (first to-visit) visited))]
                 (solve-helper new-to-visit new-visited))]))]))]
    (solve-helper (list gm) empty)))
