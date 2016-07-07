#lang racket

(require r5rs)

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      false))

; create a register with the specified name 5.2.1
(define (make-register name)
  (let ((contents '*unassigned*)
        (trace-on false))
    (define (dispatch message)
      (cond ((eq? message 'get) contents)
            ((eq? message 'set)
             (lambda (value)
               (if trace-on
                   (displayln (list name contents value)))
               (set! contents value)))
            ((eq? message 'trace-on) (set! trace-on true))
            ((eq? message 'trace-off) (set! trace-on false))
            (else (error "Unkown request -- REGISTER" message))))
    dispatch))
(define (get-contents register)
  (register 'get))
(define (set-contents! register value)
  ((register 'set) value))

(define (trace-on-register machine register-name)
  ((get-register machine register-name) 'trace-on)
  'register-trace-on)
(define (trace-off-register machine register-name)
  ((get-register machine register-name) 'trace-off)
  'register-trace-off)

; stack 5.2.1 (old)
;(define (make-stack)
;  (let ((s '()))
;    (define (push x)
;      (set! s (cons x s)))
;    (define (pop)
;      (if (null? s)
;          (error "Empty stack -- POP")
;          (let ((top (car s)))
;            (set! s (cdr s))
;            top)))
;    (define (initialize)
;      (set! s '())
;      'done)
;    (define (dispatch message)
;      (cond ((eq? message 'push) push)
;            ((eq? message 'pop) (pop))
;            ((eq? message 'initialize) (initialize))
;            (else (error "Unkown request -- STACK" message))))
;    dispatch))
; stack 5.2.4 (new) has a spy function
(define (make-stack)
  (let ((s '())
        (number-pushes 0)
        (max-depth 0)
        (current-depth 0))
    (define (push x)
      (set! s (cons x s))
      (set! number-pushes (+ number-pushes 1))
      (set! current-depth (+ current-depth 1))
      (set! max-depth (max current-depth max-depth)))
    (define (pop)
      (if (null? s)
          (error "Empty stack -- POP")
          (let ((top (car s)))
            (set! s (cdr s))
            (set! current-depth (- current-depth 1))
            top)))
    (define (initialize)
      (set! s '())
      (set! number-pushes 0)
      (set! max-depth 0)
      (set! current-depth 0)
      'done)
    (define (print-statistics)
      (displayln (list 'total-pushes '= number-pushes
                     'maximum-depth '= max-depth))
      (newline))
    (define (dispatch message)
      (cond ((eq? message 'push) push)
            ((eq? message 'pop) (pop))
            ((eq? message 'initialize) (initialize))
            ((eq? message 'print-statistics)
             (print-statistics))
            (else (error "Unkown request -- STACK" message))))
    dispatch))
(define (pop stack)
  (stack 'pop))
(define (push stack value)
  ((stack 'push) value))

; elementary machine 5.2.1, update the initialization of the-ops in 5.2.4
; update in ex5.15: instruction counts
; update in ex5.16: instruction traces
; update in ex5.19: break point
(define (make-new-machine)
  (let ((pc (make-register 'pc))
        (flag (make-register 'flag))
        (stack (make-stack))
        (the-instruction-sequence '())
        (instruction-number 0)
        (trace-on false)
        (labels '())
        (current-label '*unassign*)
        (current-line 0)
        (breakpoint-line 0)
        (break-on true))
    (let ((the-ops
           (list (list 'initialize-stack
                       (lambda () (stack 'initialize)))
                 (list 'print-stack-statistics
                       (lambda () (stack 'print-statistics)))))
          (register-table
           (list (list 'pc pc) (list 'flag flag))))
      (define (allocate-register name)
        (if (assoc name register-table)
            (error "Multiply defined register: " name)
            (set! register-table
                  (cons (list name (make-register name))
                        register-table)))
        'register-allocated)
      (define (lookup-register name)
        (let ((val (assoc name register-table)))
          (if val
              (cadr val)
              (begin
                (allocate-register name)
                (lookup-register name)))))
      (define (execute)
        (let ((insts (get-contents pc)))
          (if (null? insts)
              'done
              (begin
                (if (and (not (null? (instruction-text (car insts))))
                         (assoc (instruction-text (car insts)) labels))
                    (begin
                      (set! current-label (instruction-text (car insts)))
                      (set! breakpoint-line (cdr (assoc current-label labels)))
                      (set! current-line 0)))
                (set! current-line (+ current-line 1))
                (if (and (= current-line breakpoint-line) break-on)
                    (begin
                      (set! break-on false)
                      (displayln (list "breakpoint here" current-label current-line)))
                    (begin
                      (if trace-on
                          (displayln (instruction-text (car insts))))
                      (set! break-on true)))
                ((instruction-execution-proc (car insts)))
                (set! instruction-number (+ instruction-number 1)) ; increase the instruction number
                (execute)))))
      (define (cancel-breakpoint label)
        (define (delete-label acc-labels orig-labels)
          (cond ((null? orig-labels) (error "The label is not in the machine -- MAKE-NEW-MACHINE" label))
                ((eq? (caar orig-labels) label) (append acc-labels (cdr orig-labels)))
                (else (delete-label (cons (car orig-labels) acc-labels) (cdr orig-labels)))))
        (set! labels (delete-label '() labels)))
      (define (print-instruction-number)
        (displayln (list 'current-instruction-number '= instruction-number)))
      (define (dispatch message)
        (cond ((eq? message 'start)
               (set-contents! pc the-instruction-sequence)
               (set! instruction-number 0)
               (execute))
              ((eq? message 'install-instruction-sequence)
               (lambda (seq) (set! the-instruction-sequence seq)))
              ((eq? message 'allocate-register) allocate-register)
              ((eq? message 'get-register) lookup-register)
              ((eq? message 'install-operations)
               (lambda (ops) (set! the-ops (append the-ops ops))))
              ((eq? message 'print-instruction-number) (print-instruction-number))
              ((eq? message 'trace-on) (set! trace-on true))
              ((eq? message 'trace-off) (set! trace-on false))
              ((eq? message 'set-breakpoint)
               (lambda (label n) (set! labels (cons (cons label n) labels))))
              ((eq? message 'cancel-breakpoint)
               (lambda (label) (cancel-breakpoint label)))
              ((eq? message 'cancel-all-breakpoints) (set! labels '()))
              ((eq? message 'process-machine) (execute))
              ((eq? message 'stack) stack)
              ((eq? message 'operations) the-ops)
              (else (error "Unkown request -- MACHINE" message))))
      dispatch)))
(define (start machine)
  (machine 'start))
(define (get-register-contents machine register-name)
  (get-contents (get-register machine register-name)))
(define (set-register-contents! machine register-name value)
  (set-contents! (get-register machine register-name) value)
  'done)
(define (get-register machine register-name)
  ((machine 'get-register) register-name))

(define (trace-on-instruction machine)
  (machine 'trace-on)
  'instruction-trace-on)
(define (trace-off-instruction machine)
  (machine 'trace-off)
  'instruction-trace-off)

(define (set-breakpoint machine label n)
  ((machine 'set-breakpoint) label n))
(define (cancel-breakpoint machine label)
  ((machine 'cancel-breakpoint) label))
(define (cancel-all-breakpoints machine)
  (machine 'cancel-all-breakpoints))
(define (process-machine machine)
  (machine 'process-machine))


; assemble programming 5.2.2
(define (assemble controller-text machine)
  (extract-labels controller-text
                  (lambda (insts labels)
                    (update-insts! insts labels machine)
                    insts)))

;;;;;; updated in ex5.8
(define (extract-labels text receive)
  (if (null? text)
      (receive '() '())
      (extract-labels (cdr text)
                      (lambda (insts labels)
                        (let ((next-inst (car text)))
                          (if (symbol? next-inst)
                              (let ((exist? (assoc next-inst labels))) ; check if it exists in the labels
                                (if exist?
                                    (error "Multiply defined label" next-inst)
                                    (receive insts
                                             (cons (make-label-entry next-inst insts)
                                                   labels))))
                              (receive (cons (make-instruction next-inst)
                                             insts)
                                       labels)))))))

(define (update-insts! insts labels machine)
  (let ((pc (get-register machine 'pc))
        (flag (get-register machine 'flag))
        (stack (machine 'stack))
        (ops (machine 'operations)))
    (for-each
     (lambda (inst)
       (set-instruction-execution-proc!
        inst
        (make-execution-procedure
         (instruction-text inst) labels machine
         pc flag stack ops)))
     insts)))
(define (make-instruction text)
  (cons text '()))
(define (instruction-text inst)
  (car inst))
(define (instruction-execution-proc inst)
  (cdr inst))
(define (set-instruction-execution-proc! inst proc)
  (set-cdr! inst proc))

(define (make-label-entry label-name insts)
  (cons label-name insts))
(define (lookup-label labels label-name)
  (let ((val (assoc label-name labels)))
    (if val
        (cdr val)
        (error "Undefined label -- ASSEMBLE" label-name))))

; create execution procedures for instructions 5.2.3
; update in ex5.10: add two procedures INC and DEC
(define (make-execution-procedure inst labels machine pc flag stack ops)
  (cond ((eq? (car inst) 'assign)
         (make-assign inst machine labels ops pc))
        ((eq? (car inst) 'test)
         (make-test inst machine labels ops flag pc))
        ((eq? (car inst) 'branch)
         (make-branch inst machine labels flag pc))
        ((eq? (car inst) 'goto)
         (make-goto inst machine labels pc))
        ((eq? (car inst) 'save)
         (make-save inst machine stack pc))
        ((eq? (car inst) 'restore)
         (make-restore inst machine stack pc))
        ((eq? (car inst) 'inc)
         (make-inc inst machine pc))
        ((eq? (car inst) 'dec)
         (make-dec inst machine pc))
        ((eq? (car inst) 'perform)
         (make-perform inst machine labels ops pc))
        (else (error "Unknown instruction type -- ASSEMBLE" inst))))
; update the pc
(define (advance-pc pc)
  (set-contents! pc (cdr (get-contents pc))))

; update in ex5.10: add two procedures INC and DEC
(define (make-inc inst machine pc)
  (let ((target (get-register machine (inc-dec-reg-name inst))))
    (let ((value (get-contents target)))
      (lambda ()
        (set-contents! target (+ value 1))
        (advance-pc pc)))))
(define (make-dec inst machine pc)
  (let ((target (get-register machine (inc-dec-reg-name inst))))
    (let ((value (get-contents target)))
      (lambda ()
        (set-contents! target (- value 1))
        (advance-pc pc)))))
(define (inc-dec-reg-name instruction)
  (cadr instruction))

; assign
(define (make-assign inst machine labels operations pc)
  (let ((target (get-register machine (assign-reg-name inst)))
        (value-exp (assign-value-exp inst)))
    (let ((value-proc
           (if (operation-exp? value-exp)
               (make-operation-exp value-exp machine labels operations)
               (make-primitive-exp (car value-exp) machine labels))))
      (lambda ()
        (set-contents! target (value-proc))
        (advance-pc pc)))))
(define (assign-reg-name assign-instruction)
  (cadr assign-instruction))
(define (assign-value-exp assign-instruction)
  (cddr assign-instruction))
; test
(define (make-test inst machine labels operations flag pc)
  (let ((condition (test-condition inst)))
    (if (operation-exp? condition)
        (let ((condition-proc
               (make-operation-exp
                condition machine labels operations)))
          (lambda ()
            (set-contents! flag (condition-proc))
            (advance-pc pc)))
        (error "Bad TEST instruction -- ASSEMBLE" inst))))
(define (test-condition test-instruction)
  (cdr test-instruction))
; branch
(define (make-branch inst machine labels flag pc)
  (let ((dest (branch-dest inst)))
    (if (label-exp? dest)
        (let ((insts
               (lookup-label labels (label-exp-label dest))))
          (lambda ()
            (if (get-contents flag)
                (set-contents! pc insts)
                (advance-pc pc))))
        (error "Bad BRANCH instruction -- ASSEMBLE" inst))))
(define (branch-dest branch-instruction)
  (cadr branch-instruction))
; goto
(define (make-goto inst machine labels pc)
  (let ((dest (goto-dest inst)))
    (cond ((label-exp? dest)
           (let ((insts (lookup-label labels (label-exp-label dest))))
             (lambda () (set-contents! pc insts))))
          ((register-exp? dest)
           (let ((reg (get-register machine (register-exp-reg dest))))
             (lambda () (set-contents! pc (get-contents reg)))))
          (else (error "Bad GOTO instruction -- ASSEMBLE" inst)))))
(define (goto-dest goto-instruction)
  (cadr goto-instruction))
; save and restore
(define (make-save inst machine stack pc)
  (let ((reg (get-register machine (stack-inst-reg-name inst))))
    (lambda ()
      (push stack (get-contents reg))
      (advance-pc pc))))
(define (make-restore inst machine stack pc)
  (let ((reg (get-register machine (stack-inst-reg-name inst))))
    (lambda ()
      (set-contents! reg (pop stack))
      (advance-pc pc))))
(define (stack-inst-reg-name stack-instruction)
  (cadr stack-instruction))
; perform
(define (make-perform inst machine labels operations pc)
  (let ((action (perform-action inst)))
    (if (operation-exp? action)
        (let ((action-proc (make-operation-exp action machine labels operations)))
          (lambda ()
            (action-proc)
            (advance-pc pc)))
        (error "Bad PERFORM instruction -- ASSEMBLE" inst))))
(define (perform-action perform-instruction)
  (cdr perform-instruction))
; sub-expression
(define (make-primitive-exp exp machine labels)
  (cond ((constant-exp? exp)
         (let ((c (constant-exp-value exp)))
           (lambda () c)))
        ((label-exp? exp)
         (let ((insts (lookup-label labels (label-exp-label exp))))
           (lambda () insts)))
        ((register-exp? exp)
         (let ((r (get-register machine (register-exp-reg exp))))
           (lambda () (get-contents r))))
        (else (error "Unkown expression type -- ASSEMBLE" exp))))
(define (register-exp? exp) (tagged-list? exp 'reg))
(define (register-exp-reg exp) (cadr exp))
(define (constant-exp? exp) (tagged-list? exp 'const))
(define (constant-exp-value exp) (cadr exp))
(define (label-exp? exp) (tagged-list? exp 'label))
(define (label-exp-label exp) (cadr exp))
; machine operation
; update in ex5.9
(define (make-operation-exp exp machine labels operations)
  (let ((op (lookup-prim (operation-exp-op exp) operations))
        (aprocs (map (lambda (e)
                       (if (label-exp? e)
                           (error "Can't operate on labels -- ASSEMBLE" e)
                           (make-primitive-exp e machine labels)))
                     (operation-exp-operands exp))))
    (lambda ()
      (apply op (map (lambda (p) (p)) aprocs)))))
(define (operation-exp? exp)
  (and (pair? exp) (tagged-list? (car exp) 'op)))
(define (operation-exp-op operation-exp)
  (cadr (car operation-exp)))
(define (operation-exp-operands operation-exp)
  (cdr operation-exp))
(define (lookup-prim symbol operations)
  (let ((val (assoc symbol operations)))
    (if val
        (cadr val)
        (error "Unkown operation -- ASSEMBLE" symbol))))



; create a register machine with specified registers, operations and controller 5.2.1
(define (make-machine register-names ops controller-text)
  (let ((machine (make-new-machine)))
    (for-each (lambda (register-name)
                ((machine 'allocate-register) register-name))
              register-names)
    ((machine 'install-operations) ops)
    ((machine 'install-instruction-sequence)
     (assemble controller-text machine))
    machine))


; some machine samples
; a gcd machine
(define gcd-machine
  (make-machine
   '(a b t)
   (list (list 'rem remainder) (list '= =))
   '(test-b
     (test (op =) (reg b) (const 0))
     (branch (label gcd-done))
     (assign t (op rem) (reg a) (reg b))
     (assign a (reg b))
     (assign b (reg t))
     (goto (label test-b))
     gcd-done)))

(displayln "# 1. gcd(24, 18) = 6")
(set-register-contents! gcd-machine 'a 24)
(set-register-contents! gcd-machine 'b 18)
(start gcd-machine)
(get-register-contents gcd-machine 'a)
(gcd-machine 'print-instruction-number)
((gcd-machine 'stack) 'print-statistics)

(displayln "# 2. gcd(204, 40) = 4")
(set-register-contents! gcd-machine 'a 204)
(set-register-contents! gcd-machine 'b 40)
(start gcd-machine)
(get-register-contents gcd-machine 'a)
(gcd-machine 'print-instruction-number)
((gcd-machine 'stack) 'print-statistics)

; a fibbonacci machine
(define fib-machine
  (make-machine
   '(a b t n continue val)
   (list (list 'rem remainder) (list '= =) (list '< <) (list '+ +) (list '- -))
   '(fib-start
     (assign continue (label fib-done))
     fib-loop
     (test (op <) (reg n) (const 2))
     (branch (label immediate-answer))
     ;; set-up to compute Fib(n-1)
     (save continue)
     (assign continue (label afterfib-n-1))
     (save n)
     (assign n (op -) (reg n) (const 1))
     (goto (label fib-loop))
     afterfib-n-1
     (restore n)
     (restore continue)
     ;; set-up to compute Fib(n-2)
     (assign n (op -) (reg n) (const 2))
     (save continue)
     (assign continue (label afterfib-n-2))
     (save val)
     (goto (label fib-loop))
     afterfib-n-2
     (assign n (reg val))
     (restore val)
     (restore continue)
     (assign val (op +) (reg val) (reg n))
     (goto (reg continue))
     immediate-answer
     (assign val (reg n))
     (goto (reg continue))
     fib-done)))

(displayln "# 3. fib(7) = 13")
(set-register-contents! fib-machine 'n 7)
(start fib-machine)
(get-register-contents fib-machine 'val)
(fib-machine 'print-instruction-number)
((fib-machine 'stack) 'print-statistics)

(displayln "# 4. fib(10) = 55")
(set-register-contents! fib-machine 'n 10)
(start fib-machine)
(get-register-contents fib-machine 'val)
(fib-machine 'print-instruction-number)
((fib-machine 'stack) 'print-statistics)

; a factorial machine
(define fac-machine
  (make-machine
   '(n val continue)
   (list (list '= =) (list '* *) (list '- -))
   '(fact-start
     (assign continue (label fact-done))
     fact-loop
     (test (op =) (reg n) (const 1))
     (branch (label base-case))
     ;; set up for the recursive call by saving n and continue.
     ;; set up continue so that the computation will continue
     ;; at after-fact when the subroutine returns.
     (save continue)
     (save n)
     (assign n (op -) (reg n) (const 1))
     (assign continue (label after-fact))
     (goto (label fact-loop))
     after-fact
     (restore n)
     (restore continue)
     (assign val (op *) (reg n) (reg val))
     (goto (reg continue))
     base-case
     (assign val (const 1))
     (goto (reg continue))
     fact-done)))

(displayln "# 5. fact(4) = 24")
(set-register-contents! fac-machine 'n 4)
(start fac-machine)
(get-register-contents fac-machine 'val)
(fac-machine 'print-instruction-number)
((fac-machine 'stack) 'print-statistics)

(displayln "# 6. fact(6) = 720")
(set-register-contents! fac-machine 'n 6)
(start fac-machine)
(get-register-contents fac-machine 'val)
(fac-machine 'print-instruction-number)
((fac-machine 'stack) 'print-statistics)


; garbage collector 5.3, can't run....
(define (broken-heart? x)
  'done)
(define registers '(free scan new old new-cars new-cdrs relocate-continue root oldcr the-cars the-cdrs temp))
(define operations
  (list (list '= =)
        (list '+ +)
        (list 'vector-ref vector-ref)
        (list 'vector-set! vector-set!)
        (list 'pair? pair?)
        (list 'broken-heart? broken-heart?)))
(define garbage-collector-program
  '(begin-garbage-collection
     (assign free (const 0))
     (assign scan (const 0))
     (assign old (reg root))
     (assign relocate-continue (label reassign-root))
     (goto (label relocate-old-result-in-new))
     
     reassign-root
     (assign root (reg new))
     (goto (label gc-loop))
     
     gc-loop
     (test (op =) (reg scan) (reg free))
     (branch (label gc-flip))
     (assign old (op vector-ref) (reg new-cars) (reg scan))
     (assign relocate-continue (label update-car))
     (goto (label relocate-old-result-in-new))

     update-car
     (perform (op vector-set!) (reg new-cars) (reg scan) (reg new))
     (assign old (op vector-ref) (reg new-cdrs) (reg scan))
     (goto (label relocate-old-result-in-new))

     update-cdr
     (perform (op vector-set!) (reg new-cdrs) (reg scan) (reg new))
     (assign scan (op +) (reg scan) (const 1))
     (goto (label gc-loop))

     relocate-old-result-in-new
     (test (op pair?) (reg old))
     (branch (label pair))
     (assign new (reg old))
     (goto (reg relocate-continue))

     pair
     (assign oldcr (op vector-ref) (reg the-cars) (reg old))
     (test (op broken-heart?) (reg oldcr))
     (branch (label already-moved))
     (assign new (reg free))
     (assign free (op +) (reg free) (const 1))
     (perform (op vector-set!) (reg new-cars) (reg new) (reg oldcr))
     (assign oldcr (op vector-ref) (reg the-cdrs) (reg old))
     (perform (op vector-set!) (reg new-cdrs) (reg new) (reg oldcr))
     (perform (op vector-set!) (reg the-cars) (reg old) (const broken-heart))
     (perform (op vector-set!) (reg the-cdrs) (reg old) (reg new))
     (goto (reg relocate-continue))

     already-moved
     (assign new (op vector-ref) (reg the-cdrs) (reg old))
     (goto (reg relocate-continue))

     gc-flip
     (assign temp (reg the-cdrs))
     (assign the-cdrs (reg new-cdrs))
     (assign new-cdrs (reg temp))
     (assign temp (reg the-cars))
     (assign the-cars (reg new-cars))
     (assign new-cars (reg temp))))
(define garbage-collector
  (make-machine registers operations garbage-collector-program))
