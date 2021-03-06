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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; 5.4
; some basic procedures
(define (self-evaluating? exp)
  (cond ((number? exp) true)
        ((string? exp) true)
        (else false)))
(define (variable? exp) (symbol? exp))
(define (quoted? exp) (tagged-list? exp 'quote))
(define (assignment? exp)
  (tagged-list? exp 'set!))
(define (definition? exp)
  (tagged-list? exp 'define))
(define (if? exp) (tagged-list? exp 'if))
(define (lambda? exp) (tagged-list? exp 'lambda))
(define (begin? exp) (tagged-list? exp 'begin))
(define (application? exp) (pair? exp))

(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (if (eq? (car vals) '*unassigned*)
                 (error "Variable is unassigned" var)
                 (car vals)))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))
(define (enclosing-environment env) (cdr env))
(define (first-frame env) (car env))
(define the-empty-environment '())
(define (frame-variables frame) (car frame))
(define (frame-values frame) (cdr frame))
(define (text-of-quotation exp) (cadr exp))
(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))
(define (make-procedure parameters body env)
  (if (contain-defines? body)
      (list 'procedure parameters (scan-out-defines body) env)
      (list 'procedure parameters body env)))

(define (contain-defines? exp)
  (if (null? exp)
      false
      (or (and (pair? exp) (definition? (car exp)))
          (and (pair? exp) (contain-defines? (cdr exp))))))
(define (scan-out-defines body)
  (define (name-unassigned defines)
    (map (lambda (x) (list (definition-variable x) '*unassigned*)) defines))
  (define (set-values defines)
    (map (lambda (x) (list 'set! (definition-variable x) (definition-value x)))
         defines))
  (define (defines->let exp defines not-defines)
    (cond ((null? exp)
           (if (null? defines)
               body
               (list (list 'let (name-unassigned defines)
                           (make-begin (append (set-values defines)
                                               (reverse not-defines)))))))
          ((definition? (car exp))
           (defines->let (cdr exp) (cons (car exp) defines) not-defines))
          (else (defines->let (cdr exp) defines (cons (car exp) not-defines)))))
  (defines->let body '() '()))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))
(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp) ; formal parameters
                   (cddr exp)))) ; body

(define (make-begin seq) (cons 'begin seq))
(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

(define (operator exp) (car exp))
(define (operands exp) (cdr exp))
(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))
(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))
(define (compound-procedure? p)
  (tagged-list? p 'procedure))
(define (apply-primitive-procedure proc args)
  (apply (primitive-implementation proc) args))
(define (primitive-implementation proc) (cadr proc))

(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))
(define (extend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error "Too many arguments supplied" vars vals)
          (error "Too few arguments supplied" vars vals))))
(define (make-frame variables values)
  (cons variables values))
(define (begin-actions exp) (cdr exp))
(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))
(define (if-predicate exp) (cadr exp))
(define (if-consequent exp) (caddr exp))
(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      'false))
(define (true? x)
  (not (eq? x false)))
(define (false? x)
  (eq? x false))
(define (assignment-variable exp) (cadr exp))
(define (assignment-value exp) (caddr exp))
(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET!" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))
(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond ((null? vars)
             (add-binding-to-frame! var val frame))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (scan (frame-variables frame)
          (frame-values frame))))
(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (frame-variables frame)))
  (set-cdr! frame (cons val (frame-values frame))))
(define (cond? exp) (tagged-list? exp 'cond))
(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))
(define (expand-clauses clauses)
  (if (null? clauses)
      'false
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (error "ELSE clause isn't the last -- COND->IF" clauses))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))
(define (cond-clauses exp) (cdr exp))
(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))
(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))
(define (cond-predicate clause) (car clause))
(define (cond-actions clause) (cdr clause))
(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))

(define (primitive-procedure-names)
  (map car primitive-procedures))
(define (primitive-procedure-objects)
  (map (lambda (proc) (list 'primitive (cadr proc)))
       primitive-procedures))
(define primitive-procedures
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'cons cons)
        (list 'null? null?)
        (list '* *)
        (list '+ +)
        (list '- -)
        (list '/ /)
        (list '> >)
        (list '< <)
        (list '= =)
        ))
(define (setup-environment)
  (let ((initial-env
         (extend-environment (primitive-procedure-names)
                             (primitive-procedure-objects)
                             the-empty-environment)))
    (define-variable! 'true true initial-env)
    (define-variable! 'false false initial-env)
    initial-env))
(define the-global-environment (setup-environment))
(define (get-global-environment)
  the-global-environment)

(define (prompt-for-input string)
  (newline) (newline) (display string) (newline))
(define (announce-output string)
  (newline) (display string) (newline))
(define (user-print object)
  (if (compound-procedure? object)
      (display (list 'compound-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))

(define (let? exp) (tagged-list? exp 'let))
(define (let-vars exp) (map car (cadr exp)))
(define (let-exps exp) (map cadr (cadr exp)))
(define (let-body exp) (cddr exp))
(define (let->combination exp)
  (make-lambda (let-vars exp) (let-body exp)))


; new procedures
(define (empty-arglist) '())
(define (adjoin-arg arg arglist)
  (append arglist (list arg)))
(define (last-operand? ops)
  (null? (cdr ops)))


; registers
(define eceval-registers
  '(exp env val continue proc argl unev))
; operations
; update in ex5.23 ... add cond expression
(define eceval-operations
  (list (list 'self-evaluating? self-evaluating?)
        (list 'variable? variable?)
        (list 'quoted? quoted?)
        (list 'assignment? assignment?)
        (list 'definition? definition?)
        (list 'if? if?)
        (list 'lambda? lambda?)
        (list 'begin? begin?)
        (list 'application? application?)
        (list 'lookup-variable-value lookup-variable-value)
        (list 'text-of-quotation text-of-quotation)
        (list 'lambda-parameters lambda-parameters)
        (list 'lambda-body lambda-body)
        (list 'make-procedure make-procedure)
        (list 'operands operands)
        (list 'operator operator)
        (list 'empty-arglist empty-arglist)
        (list 'adjoin-arg adjoin-arg)
        (list 'last-operand? last-operand?)
        (list 'first-operand first-operand)
        (list 'no-operands? no-operands?)
        (list 'rest-operands rest-operands)
        (list 'primitive-procedure? primitive-procedure?)
        (list 'compound-procedure? compound-procedure?)
        (list 'apply-primitive-procedure apply-primitive-procedure)
        (list 'procedure-parameters procedure-parameters)
        (list 'procedure-environment procedure-environment)
        (list 'procedure-body procedure-body)
        (list 'extend-environment extend-environment)
        (list 'begin-actions begin-actions)
        (list 'first-exp first-exp)
        (list 'last-exp? last-exp?)
        (list 'rest-exps rest-exps)
        (list 'if-predicate if-predicate)
        (list 'if-alternative if-alternative)
        (list 'if-consequent if-consequent)
        (list 'true? true?)
        (list 'assignment-variable assignment-variable)
        (list 'assignment-value assignment-value)
        (list 'set-variable-value! set-variable-value!)
        (list 'definition-variable definition-variable)
        (list 'definition-value definition-value)
        (list 'define-variable! define-variable!)
        (list 'cond? cond?)
        (list 'cond->if cond->if)
        (list 'prompt-for-input prompt-for-input)
        (list 'read read)
        (list 'get-global-environment get-global-environment)
        (list 'announce-output announce-output)
        (list 'user-print user-print)
        ))

; assemble codes
(define eceval-code
  '(; driver loop
    read-eval-print-loop
    (perform (op initialize-stack))
    (perform (op prompt-for-input) (const ";;; EC-Eval input: "))
    (assign exp (op read))
    (assign env (op get-global-environment))
    (assign continue (label print-result))
    (goto (label eval-dispatch))

    print-result ; update to print statistic information
    (perform (op print-stack-statistics))
    (perform (op announce-output) (const ";;; EC-Eval value: "))
    (perform (op user-print) (reg val))
    (goto (label read-eval-print-loop))

    unkown-expression-type
    (assign val (const unkown-expression-type-error))
    (goto (label signal-error))

    unkown-procedure-type
    (restore continue)
    (assign val (const unkown-procedure-type-error))
    (goto (label signal-error))

    signal-error
    (perform (op user-print) (reg val))
    (goto (label read-eval-print-loop))
    
    ; eval procedure
    ; update in ex5.23: add cond expression
    eval-dispatch
    (test (op self-evaluating?) (reg exp))
    (branch (label ev-self-eval))
    (test (op variable?) (reg exp))
    (branch (label ev-variable))
    (test (op quoted?) (reg exp))
    (branch (label ev-quoted))
    (test (op assignment?) (reg exp))
    (branch (label ev-assignment))
    (test (op definition?) (reg exp))
    (branch (label ev-definition))
    (test (op if?) (reg exp))
    (branch (label ev-if))
    (test (op lambda?) (reg exp))
    (branch (label ev-lambda))
    (test (op begin?) (reg exp))
    (branch (label ev-begin))
    (test (op cond?) (reg exp))
    (branch (label ev-cond))
    (test (op application?) (reg exp))
    (branch (label ev-application))
    (goto (label unkown-expression-type))

    ; simple expression
    ev-self-eval
    (assign val (reg exp))
    (goto (reg continue))

    ev-variable
    (assign val (op lookup-variable-value) (reg exp) (reg env))
    (goto (reg continue))

    ev-quoted
    (assign val (op text-of-quotation) (reg exp))
    (goto (reg continue))

    ev-lambda
    (assign unev (op lambda-parameters) (reg exp))
    (assign exp (op lambda-body) (reg exp))
    (assign val (op make-procedure)
            (reg unev) (reg exp) (reg env))
    (goto (reg continue))

    ; procedure application evaluating
    ev-application
    (save continue)
    (save env)
    (assign unev (op operands) (reg exp))
    (save unev)
    (assign exp (op operator) (reg exp))
    (assign continue (label ev-appl-did-operator))
    (goto (label eval-dispatch))

    ev-appl-did-operator
    (restore unev) ; oeprands
    (restore env)
    (assign argl (op empty-arglist))
    (assign proc (reg val)) ; operator
    (test (op no-operands?) (reg unev))
    (branch (label apply-dispatch))
    (save proc)

    ev-appl-operand-loop
    (save argl)
    (assign exp (op first-operand) (reg unev))
    (test (op last-operand?) (reg unev))
    (branch (label ev-appl-last-arg))
    (save env)
    (save unev)
    (assign continue (label ev-appl-accumulate-arg))
    (goto (label eval-dispatch))

    ev-appl-accumulate-arg
    (restore unev)
    (restore env)
    (restore argl)
    (assign argl (op adjoin-arg) (reg val) (reg argl))
    (assign unev (op rest-operands) (reg unev))
    (goto (label ev-appl-operand-loop))

    ev-appl-last-arg
    (assign continue (label ev-appl-accum-last-arg))
    (goto (label eval-dispatch))

    ev-appl-accum-last-arg
    (restore argl)
    (assign argl (op adjoin-arg) (reg val) (reg argl))
    (restore proc)
    (goto (label apply-dispatch))

    ; procedure application
    apply-dispatch
    (test (op primitive-procedure?) (reg proc))
    (branch (label primitive-apply))
    (test (op compound-procedure?) (reg proc))
    (branch (label compound-apply))
    (goto (label unkown-procedure-type))

    primitive-apply
    (assign val (op apply-primitive-procedure) (reg proc) (reg argl))
    (restore continue)
    (goto (reg continue))

    compound-apply
    (assign unev (op procedure-parameters) (reg proc))
    (assign env (op procedure-environment) (reg proc))
    (assign env (op extend-environment) (reg unev) (reg argl) (reg env))
    (assign unev (op procedure-body) (reg proc))
    (goto (label ev-sequence))

    ; sequence evaluating and tail recursion
    ev-begin
    (assign unev (op begin-actions) (reg exp))
    (save continue)
    (goto (label ev-sequence))

    ev-sequence
    (assign exp (op first-exp) (reg unev))
    (test (op last-exp?) (reg unev))
    (branch (label ev-sequence-last-exp))
    (save unev)
    (save env)
    (assign continue (label ev-sequence-continue))
    (goto (label eval-dispatch))

    ev-sequence-continue
    (restore env)
    (restore unev)
    (assign unev (op rest-exps) (reg unev))
    (goto (label ev-sequence))

    ev-sequence-last-exp
    (restore continue)
    (goto (label eval-dispatch))

    ; cond ...... added in ex5.23
    ev-cond
    (assign exp (op cond->if) (reg exp))
    (goto (label ev-if))

    ; if
    ev-if
    (save exp)
    (save env)
    (save continue)
    (assign continue (label ev-if-decide))
    (assign exp (op if-predicate) (reg exp))
    (goto (label eval-dispatch))

    ev-if-decide
    (restore continue)
    (restore env)
    (restore exp)
    (test (op true?) (reg val))
    (branch (label ev-if-consequent))

    ev-if-alternative
    (assign exp (op if-alternative) (reg exp))
    (goto (label eval-dispatch))

    ev-if-consequent
    (assign exp (op if-consequent) (reg exp))
    (goto (label eval-dispatch))

    ; assignment
    ev-assignment
    (assign unev (op assignment-variable) (reg exp))
    (save unev)
    (assign exp (op assignment-value) (reg exp))
    (save env)
    (save continue)
    (assign continue (label ev-assignment-l))
    (goto (label eval-dispatch))

    ev-assignment-l
    (restore continue)
    (restore env)
    (restore unev)
    (perform (op set-variable-value!) (reg unev) (reg val) (reg env))
    (assign val (const ok))
    (goto (reg continue))

    ; definition
    ev-definition
    (assign unev (op definition-variable) (reg exp))
    (save unev)
    (assign exp (op definition-value) (reg exp))
    (save env)
    (save continue)
    (assign continue (label ev-definition-l))
    (goto (label eval-dispatch))

    ev-definition-l
    (restore continue)
    (restore env)
    (restore unev)
    (perform (op define-variable!) (reg unev) (reg val) (reg env))
    (assign val (const ok))
    (goto (reg continue))
    ))


; make the machine
(define eceval
  (make-machine
   eceval-registers
   eceval-operations
   eceval-code))

(start eceval)
