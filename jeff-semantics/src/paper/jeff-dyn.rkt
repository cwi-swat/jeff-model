#lang racket

(require redex)

(require "jeff.rkt")

(caching-enabled? #f) ; to simulate printing to standard output in metafunctions

(define-language REDEX)

(provide jeff-dyn)
(provide Red)
(provide substitute)
;(provide custom-substitute)
;(provide substitute-all)
(provide mbody)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;                           ;;;;
;;;;        Grammar            ;;;;
;;;;                           ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-extended-language jeff-dyn
  jeff
  (E ::=
     ;(resume e)
     hole
     (E f)
     (E < T ... > m ee ...)
     (v < T ... > m v ... E ee ...)
     (new N  v ... E ee ...)
     (op C < T ... > < T ... > m v ... E ee ...) ;; effect cal
     (with E ee)
     (with v E)
     (val x T E ee)
     ;(val x T v E)  
     )
 
   #:binding-forms
  (method (header mod < (Y << N) ... > T m ((T_1 x) ...) Ξ) ee #:refers-to (shadow x ...))
  (val x T ee_1 ee_2 #:refers-to x)
  )
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;                           ;;;;
;;;;    Helper functions       ;;;;
;;;;                           ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;(define-metafunction jeff-dyn
;  contains-effect : p C m -> boolean
;  [(contains-effect p C m_op)
;   #t
;   (where (class C (fd_1 ...) N_parent (N_1 ...) md_1 ...)
;          (class-lookup p C))
;   (where (md_2 ... (method (eff-header T m_op ((T_1 x_1) ...)) (cap_1 ...) e) md_3 ...)
;          (md_1 ...))]
;
;  [(contains-effect p C m_op)
;   #f
;   (where (class C (fd_1 ...) C_Object (N_1 ...) md_1 ...)
;          (class-lookup p C))
;   (side-condition (eq? (term C_Object) 'Object))]
;
;  [(contains-effect p C m_op)
;   (contains-effect p N_parent m_op)
;   (where (class C (fd_1 ...) N_parent (N_1 ...) md_1 ...)
;          (class-lookup p C))])


(define-metafunction jeff-dyn
  method-name : mh -> m
  [(method-name (header T m ((T_1 x) ...))) m]
  [(method-name (eff-header T m ((T_1 x) ...))) m])

(define-metafunction jeff-dyn
  is-native : p C m -> boolean
  [(is-native p C m)
   #t
   (where (class C < T_0 ... > class-args
            ((U f) ...) implements (N_1 ...)
            md_1 ...
            (method (header native < ( Z << P ) ... > T m ((T_1 x_1) ...) Ξ) ee)
            md_2 ...)
          (class-lookup p C))]
  [(is-native p C m)
   #f])


(define-metafunction jeff-dyn
  is-innermost : p N E -> boolean
  [(is-innermost p N hole)
   #t]
  [(is-innermost p N (with (new Q v ...) E))
   (is-innermost p N E)
   (where #f (<: p () Q N))]
  [(is-innermost p N (with (new Q v ...) E))
   #f
   (where #t (<: p () Q N))]
  [(is-innermost p N (E f))
   (is-innermost p N E)]
  [(is-innermost p N (E < T ... > m ee ...))
   (is-innermost p N E)]
  [(is-innermost p N (v < T ... > m v_1 ... E ee ...))
   (is-innermost p N E)]
  [(is-innermost p N (new N  v ... E ee ...))
   (is-innermost p N E)]
  [(is-innermost p N (op C < T ... > < T ... > m v ... E ee ...))
   (is-innermost p N E)]
  [(is-innermost p N (with E ee))
   (is-innermost p N E)]
  [(is-innermost p N (val x T E ee))
   (is-innermost p N E)])
  

(define-metafunction jeff-dyn
  mbody : p m (T ...) N -> ((x ...) ee)
  ; m defined in C
  [(mbody p m (V ...) (C < T ... >))
   ((x_1 ...) (substitute-all ee (X ... Y ...) (T ... V ...)))
   (where #t (debug (term ("mbody" m (V ...) (C < T ... >)))))
   (where (class C < (X << N_0) ... > class-args ((S f) ...) implements (N_1 ...) md_1 ...)
          (class-lookup p C))
   (where (md_2 ...
           (method (header mod < ( Y << Q ) ... > U m ((U_1 x_1) ..._1) Ξ) ee)
           md_3 ...) (md_1 ...))
   ])
   

; Generic function

;(define-metafunction jeff-dyn ;; it *has to* be deffined over language jeff (previously it was REDEX and the substitution was simply not working)
;  custom-substitute : any any any -> any
;  [(custom-substitute (e_0 m e_1 ...) any_x any_1)
;   ((custom-substitute e_0 any_x any_1) m (custom-substitute e_1 any_x any_1) ...)]
;  [(custom-substitute (with e_1 e_2) any_x any_1)
;   (with (custom-substitute e_1 any_x any_1) (custom-substitute e_2 any_x any_1))]
;  [(custom-substitute (λ ((T x_1) ...) e) any_x any_1)
;   (λ ((T (substitute x_1 any_x any_1)) ...) (custom-substitute e any_x any_1))]
;  [(custom-substitute (op m e_1 ...) any_x any_1)
;   (op m (custom-substitute e_1 any_x any_1) ...)]
;  [(custom-substitute ((super-ctx e_1 e_2) e_3 ...) any_x any_1) 
;   ((super-ctx (custom-substitute e_1 any_x any_1) (custom-substitute e_2 any_x any_1)) (custom-substitute e_3 any_x any_1) ...)]
;  [(custom-substitute (as C e_1 e_2) any_x any_1)
;   (as C (custom-substitute e_1 any_x any_1) (custom-substitute e_2 any_x any_1))]
;  [(custom-substitute (super e_1 ...) any_x any_1)
;   ((custom-substitute super any_x any_1) (custom-substitute e_1 any_x any_1) ...)]
;  [(custom-substitute (new C e_1 ...) any_x any_1)
;   (new C (custom-substitute e_1 any_x any_1) ...)]
;  [(custom-substitute (virtual-new e_1 ...) any_x any_1)
;   (virtual-new (custom-substitute e_1 any_x any_1) ...)]
;  [(custom-substitute (val x T e_1 e_2) any_x any_1)
;   (val (substitute x any_x any_1) T (custom-substitute e_1 any_x any_1) (custom-substitute e_2 any_x any_1))]
;  [(custom-substitute x any_x any_1)
;   (substitute x any_x any_1)]
; [(custom-substitute super super any_1)
;   any_1]
;  [(custom-substitute e any_x any_1)
;   (substitute e any_x any_1)])


;(define-metafunction jeff-dyn ;; it *has to* be deffined over language jeff (previously it was REDEX and the substitution was simply not working)
;  substitute-all : any (any ...) (any ...) -> any
;  [(substitute-all any () ()) any]
;                                       
;  [(substitute-all any (any_x1 any_x2 ...) (any_v1 any_v2 ...))
;   (substitute-all
;    (custom-substitute any any_x1 any_v1)
;    (any_x2 ...)
;    (any_v2 ...))])
   
;; Native methods

;(define-metafunction jeff-dyn
;  call-native-method : p v m cd v ... -> v
;  [(call-native-method p (new Int number_0) m (class C (fd_1 ...) N_parent (N_1 ...) md_1 ... (method (native-header T m ((T_1 x_1) ...)) (cap_1 ...) e) md_2 ...) v ...)
;   ,(case (term m)
;      [(+)
;       (if (redex-match jeff (((new Int number_1))) (term ((v ...))))
;           (term (new Int ,(+ (term number_0) (caddar (term (v ...))))))
;           (error "wrong arguments to +"))]
;      [(equals)
;       (if (redex-match jeff (((new Int number_1))) (term ((v ...))))
;           (if (eq? (term number_0) (caddar (term (v ...))))
;               (term (new True))
;               (term (new False)))
;           (error "wrong arguments to equals"))]
;      [(>=)
;       (if (redex-match jeff (((new Int number_1))) (term ((v ...))))
;           (if (>= (term number_0) (caddar (term (v ...))))
;               (term (new True))
;               (term (new False)))
;           (error "wrong arguments to >="))])])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;                           ;;;;
;;;;        Reduction          ;;;;
;;;;                           ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define Red
  (reduction-relation
   jeff-dyn
   #:domain (ee p)
   
   (--> ((in-hole E ((new N v ...) f_i)) p)
        ((in-hole E v_i) p)
        "E-FIELD-LOOKUP"
        (where ((N_1 f_1) ...) (fields p N))
        (where/hidden ((f_0 v_0) ... (f_i v_i) (f_i+1 v_i+1) ...) 
                      ((f_1 v) ...)))
  
   
   (--> ((in-hole E ((new N v ...) < V ... >  m v_1 ..._1)) p)
        ((in-hole E (substitute-all ee_0 (this x ...) ((new N v ...) v_1 ...)))
                  p)
        "E-METHOD-CALL"
        (where (C < T_0 ... >) N)
        (side-condition (not (term (is-native p C m))))
        ;(where (class C (fd_1 ...) N_parent (C_2 ...) md_1 ...)  (class-lookup p C))
        (where ((x ..._1) ee_0) (mbody p m (V ...) N))
        )
   
   (--> ((in-hole E ((new N v ...) < V ... > m v_1 ...)) p)
        ((in-hole E (call-native-method p (new N v ...) m
                                        (class C < ( Y << P ) > class-args ((U f) ...) implements (N_1 ...) md_1 ... (method (header native < V ... > T m ((T_1 x_1) ...) Ξ)  ee_dummy) md_2 ...)
                                        v_1 ...)) p)
        "E-METHOD-NATIVE-CALL"
        (where (C < W ... >) N)
        (side-condition (term (is-native p C m)))
        (where (class C < ( Y << P ) > class-args ((U f) ...) implements (N_1 ...) md_1 ... (method (header native < V ... > T m ((T_1 x_1) ...) Ξ)  ee_dummy) md_2 ...) (class-lookup p C)))
   
   
   (--> ((in-hole E (with (new N v_1 ...) v)) p)
        ((in-hole E ((new N v_1 ...) < > return v)) p)
        "E-RETURN")

   (--> ((in-hole E ((newResume x_v x_h ee_0) < > resume v_1 v_2)) p)
        ((in-hole E (substitute-all ee_0 (x_v x_h) (v_1 v_2))) p)
        "E-RESUME")
        
   (--> ((in-hole E (with (new Q v_0 ...) (in-hole E_1 (op C < V ... > < W ... > m_op v_1 ..._1)))) p)
        ((in-hole E (substitute-all ee_0
                                    (this there x ...)
                                    ((new Q v_0 ...) v_there v_1 ...))) 
         p)
        "E-OPMATCH-PARAMS"
        (where #t (is-innermost p (C < V ... >) E_1 ))
        (where #t (debug "OK-1"))
        (where N (C < V ... >))
        (where #t (debug "OK0"))
        (where (D < U ... > ) Q)
        (where #t (debug "OK1"))
        (where #t (<: p () Q N))
        (where #t (debug "OK2"))
        (where (x_v) (,(gensym 'v)))
        (where (x_h) (,(gensym 'h)))
        (where #t (debug "OK3"))
        (where v_there (newResume
                           x_v x_h
                           (with x_h (in-hole E_1 x_v))))
        (where #t (debug "OK4"))
        (where ((x ..._1) ee_0) (mbody p m_op (W ...) Q))
        (where #t (debug "OK5"))
        )


   (--> ((in-hole E (val x T v ee)) p)
        ((in-hole E (substitute ee x v)) p)
        "E-LET")
   )
)



