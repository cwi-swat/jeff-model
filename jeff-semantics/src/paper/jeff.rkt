#lang racket

(require redex)

(caching-enabled? #f)

(provide debug)
(provide ⊢)
(provide jeff)
(provide fields)
(provide class-lookup)
(provide <:)
(provide <=)
(provide <=1)
;(provide oneof-<:)
;(provide bound)
(provide mtype)
(provide mtype-interface)
;(provide method-in)
(provide override)
;(provide ok)
;(provide handler-result-type)
(provide substitute-all)
(provide class-ok)
;(provide interface-ok)
;(provide method-ok-in)
(provide method-header-ok-in)
(provide find-mtype-interface)
(provide add-built-in)
;(provide lookup-bound)
;(provide bound)
;(provide header-in)
;(provide effect-interfaces)
;(provide effectful-interface)
;(provide interfaces-methods)
;(provide class-methods)
;(provide is-interface)
;(provide all-interfaces)

;(provide latentaux)

(define verbose #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;                           ;;;;
;;;;        Grammar            ;;;;
;;;;                           ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-language jeff
  (p ::= (program
          id ...
          cd ...
          ))
  (id ::= (interface C < (Y << N) ... > extends (N ...) mh ...))
  (cd ::=
      (class C < (Y << N) ... > class-args ((T f) ...) implements (N ...) md ...))
  (mod ::= simple effect native)
  (mh ::=
      (header mod < (Y << N) ... > T m ((T x) ...) Ξ))
  (md ::= (method mh ee))
  (ee ::=
     ;(resume e)
     (ee f)
     (ee < T ... > m ee ...) ;; method call
     (new N ee ...)
     (op C < T ... > < T ... > m ee ...) ;; effect cal
     (with ee ee)
     (val x T ee ee)  ;; binding (do)
     v)           ;; value
  (v :=
      x
      (new N v ...)
      (newResume x x ee))
  (N M P Q ::= (C < T ... >))
  (T S U V W ::= Y N)
  (C B D ::= variable-not-otherwise-mentioned)
  (m n ::= variable-not-otherwise-mentioned)
  (x y z ::= variable-not-otherwise-mentioned)
  (f g ::= variable-not-otherwise-mentioned)
  (X Y Z ::= variable-not-otherwise-mentioned)
  (Ξ ::=
     (N ...))
  (Γ ::= ((x T) ...))
  (Δ ::= ((Y N) ...))

  ;; alias
  (tp ::= (Y << N))
  (par ::= (T f))
  
  ;(method (mod header < (Y_1 << N_1) ... > T m ((T_1 x) ...) (effs (T_field f_field) ...)) ee #:refers-to (shadow Y_1 ...))
  ;(class C <(Y_1 << N_1) ... > class-args ((T_field f_field) ...) extends N implements (N_0 ...) md #:refers-to (shadow Y_1 ...) ...)
  )

(define-metafunction jeff
  add-built-in : p -> p
  [(add-built-in (program id ... cd ...))
   (program
    (interface Object < > extends ( ))
    (interface Handler < (Out << (Object < >))  (In << (Object < >))  > extends ((Object < >))
      (header simple < > Out return ((In in) ) ( )))
    (interface Resume < (T << (Object < >)) (Out << (Object < >)) (In << (Object < >))  > extends ((Object < >))
      (header simple < > Out resume ((T x) ((Handler < Out In >) h) ) ( )))
    id ...
    cd ...)])

(define-metafunction jeff 
  debug : any ... -> boolean
  [(debug) #t]
  [(debug any_1 any_2 ...)
   ,(begin
      (if verbose (display (term any_1)) #t)
      (if verbose (newline) #t)
      (term (debug any_2 ...)))])


;; FIXED sustitution problem!
(define-metafunction jeff ;; it *has to* be deffined over language jeff (previously it was REDEX and the substitution was simply not working)
  substitute-all : any (any ...) (any ...) -> any
  [(substitute-all any () ()) any]
                                       
  [(substitute-all any (any_x1 any_x2 ...) (any_v1 any_v2 ...))
   (substitute-all
    (substitute any any_x1 any_v1)
    (any_x2 ...)
    (any_v2 ...))])

(define-metafunction jeff 
  class-lookup : p C -> any
  [(class-lookup (program id_1 ... cd_1 ... (class C < tp ... > class-args (par ...) implements (P ...) md ...) cd_2 ...) C)
    (class C < tp ... > class-args (par ...) implements (P ...) md ...)]
  [(class-lookup (program id_1 ... (interface C < tp ... > extends (N ...) mh ...) id_2 ... cd_1 ...) C)
   (interface C < tp ... > extends (N ...) mh ...)]
  [(class-lookup p C) #f])

(define-metafunction jeff
  fields : p N -> ((T f) ...)
  [(fields p (C < T ... >))
   (((substitute-all U (Y ...) (T ...)) f) ...)
   (where (class C < (Y << N_0) ... > class-args ((U f) ...) implements (N_1 ...) md_1 ...)
          (class-lookup p C))])


(define-metafunction jeff
  fields-interface : p T -> ((T f) ...)
  [(fields-interface p (C < T ... >))
   ()
   (where (interface C < tp ... > extends (N ...) mh ...)
          (class-lookup p C))]
  [(fields-interface p T)
   (fields p T)])
   
;(term (try (X) ((Object < >)) ((Object < X >))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;                           ;;;;
;;;;       Type rules          ;;;;
;;;;                           ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Subtyping
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
The subptying rule is different from the one that is in TAPL.
We defined it in the way so it would be algorithmic, avoiding
choosing a "middle-man" non-deterministically in the case of 
the transitivity rule, so the latter one is not present 
anymore.
|#

(define-judgment-form jeff
  #:mode (oneof-<: I I I I) 
  #:contract (oneof-<: p Δ (T ...) T)
  [(<: p Δ T_1 T)
   ----------
   (oneof-<: p Δ (T_1 T_2 ...) T)]
  
  [(oneof-<: p Δ (T_2 ...) T)   
   ---------------
   (oneof-<: p Δ (T_1 T_2 ...) T)]
  )


(define-judgment-form jeff
  #:mode (<: I I I I) 
  #:contract (<: p Δ T T)
  [
   ----------
   (<: p Δ T T)]

  [----------
   (<: p Δ N (Object < >))] ;; TODO Added for interfaces to be subtypes of Object (is it correct?)
  [(side-condition ,(member (term Y) (map car (term Δ))))
   (where N (lookup-bound Δ Y))
   ----------
   (<: p Δ Y N)]
  
  ; (class C < tp ... > class-args ((T_field f_field) ...) extends N implements (N ...) md ...))
;  [(where  (class C < (Y << N_0) ... > class-args ((T_field f_field) ...) extends N implements (N_2 ...) md ...)
;           (class-lookup p C))
;   (where T_r (substitute-all N (Y ...) (T ...)))
;   (<: p Δ T_r T_1)
;   ---------------
;   (<: p Δ (C < T ... >) T_1)
;   
;   ]
  
  [(where  (class C < (Y << N_0) ... > class-args ((T_field f_field) ...) implements (N_2 ...) md ...)
           (class-lookup p C))
   (where (T_1 ...) ((substitute-all N_2 (Y ...) (T ...)) ...))
   (oneof-<: p Δ (T_1 ...) S_1)
   ---------------
   (<: p Δ (C < T ... >) S_1)]
  ;; TODO subtyping between interfaces

  [(where  (interface C < (Y << N_0) ... > extends (N_2 ...) md ...)
           (class-lookup p C))
   (where (T_1 ...) ((substitute-all N_2 (Y ...) (T ...)) ...))
   (oneof-<: p Δ (T_1 ...) S_1)
   ---------------
   (<: p Δ (C < T ... >) S_1)]
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Subeffecting
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-judgment-form jeff
  #:mode (<=1 I I I I) 
  #:contract (<=1 p Δ Ξ T)
  [(<: p Δ U_1 T)
   ----------
   (<=1 p Δ (U_1 U_2 ...) T)]
  [(<=1 p Δ (U_2 ...) T)
   ----------
   (<=1 p Δ (U_1 U_2 ...) T)])
  
  

(define-judgment-form jeff
  #:mode (<= I I I I) 
  #:contract (<= p Δ Ξ Ξ)
  [(side-condition (debug (("<=1" p Δ Ξ T_1) ...)))
   (<=1 p Δ Ξ T_1) ...
   ----------
   (<= p Δ Ξ (T_1 ...))])
  


(define-metafunction jeff
  method-in : m md ... -> any
  [(method-in m md_0 ... (method (header mod < (Y << N) ... > T_r m ((T x) ...)  Ξ_2) ee)  md_1 ...)
   (mod ((Y << N) ...) T_r m ((T x) ...) Ξ_2 ee)] 
  [(method-in m md_0 ...) #f])

(define-metafunction jeff
  header-in : m mh ... -> any
  [(header-in m mh_0 ... (header mod < (Y << N) ... > T_r m ((T x) ...)  Ξ_2) mh_1 ...)
   (mod ((Y << N) ...) T_r m ((T x) ...) Ξ_2)] 
  [(header-in m mh_0 ...) #f])



(define-metafunction jeff
  mtype : p m T -> any  
  ; m is defined in class C
  [(mtype p m (C < T_0 ... >))
   any_c
   (where  (class C < (Z << P) ... > class-args (par ...) implements (N_1 ...) md_1 ...)
           (class-lookup p C))
   (where (mod ((Y << N) ...) T_r m ((T x) ...) Ξ_2 ee)
          (method-in m md_1 ...))
   (where any_c (substitute-all (mod ((Y << N) ...) ((T x) ...) T_r Ξ_2) (Z ...) (T_0 ...)))]
  [(mtype p m (C < T_0 ... >))
   (mtype p m T_c)
   (where  (class C < (Z << P) ... > class-args (par ...) implements (N_1  ...) md_1 ...)
           (class-lookup p C))
   (where #f (method-in m md_1 ...))
   (where T_c (substitute-all N_parent (Z ...) (T_0 ...)))]
  [(mtype p m (C < T_0 ... >))
   (mtype-interface p m (C < T_0 ... > ))
   (where (interface C < (Z << P) ... > extends (N_parent ...) mh_1 ...)
           (class-lookup p C))]
  ; m not defined in C
)

(define-metafunction jeff
  mtype-interface : p m T -> any
  ; m is defined in interface C
  [(mtype-interface p m (C < T_0 ... >))
   any_c2
   (where (interface C < (Z << P) ... > extends (N_parent ...) mh_1 ...)
          (class-lookup p C))
   (where (mod ((Y << N) ...) T_r m ((T x) ...) Ξ_2)
          (header-in m mh_1 ...))
   ;; TODO this is workaround, because:
   ;;      (substitute-all U (C T U) ( (DefaultState < T >) (Unit < >) (StateResult < T >)))
   ;;    is different from
   ;;      (substitute-all U (U T C) ((StateResult < T >) (Unit < >) (DefaultState < T >))))
  
   (where (Z_gen ...) ,(map (λ x (gensym (first x))) (term (Z ...))))
   (where any_c (substitute-all (mod ((Y << N) ...) ((T x) ...) T_r Ξ_2) (Z ...) (Z_gen ...)))
   (where any_c2 (substitute-all any_c (Z_gen ...) (T_0 ...)))
   ;(where any_c3 (substitute-all any_c2 (Z_gen ...) (Z ...)))
   ]
  ; m not defined in interface C
  [(mtype-interface p m (C < T_0 ... >))
   (find-mtype-interface p m (T_c ...))
   (where (interface C < (Z << P) ... > extends (N_parent ...) mh_1 ...)
          (class-lookup p C))
   (where #f (header-in m mh_1 ...))
   (where (T_c ...) ((substitute-all N_parent (Z ...) (T_0 ...)) ...))])
  

(define-metafunction jeff
  find-mtype-interface : p m (T ...) -> any
  [(find-mtype-interface p m ())
  #f]
  [(find-mtype-interface p m ((C < T_0 ... >) T_1 ...))
   (find-mtype-interface p m (T_1 ...))
   (where #t (debug "find-mtype-interface::2::1"))
   (where (interface C < (Z << P) ... > extends (N_parent ...) mh_1 ...)
          (class-lookup p C))
   (where #t (debug "find-mtype-interface::2::2"))
   (where #f (mtype-interface p m (C < T_0 ... >)))
   (where #t (debug "find-mtype-interface::2::3"))]
  [(find-mtype-interface p m ((C < T_0 ... >) T_1 ...))
   any_c
   (where #t (debug "find-mtype-interface::3::1"))
   (where #t (debug ("class-lookup" (term C))))
   (where (interface C < (Z << P) ... > extends (N_parent ...) mh_1 ...)
          (class-lookup p C))
   (where #t (debug "find-mtype-interface::3::2"))
   (where any_c (mtype-interface p m (C < T_0 ... >)))
   (where #t (debug "find-mtype-interface::3::3"))
   (side-condition (not (eq? (term any_c) #f)))
   (where #t (debug "find-mtype-interface::3::4"))]
  )



; Environment lookup
(define-metafunction jeff
  lookup-type : Γ x -> T
  [(lookup-type ((x_0 T_0) ... (x_i T_i) (x_i+1 T_i+1) ...) x_i) 
   T_i])

(define-metafunction jeff
  lookup-bound : Δ Y -> N
  [(lookup-bound ((Y_0 N_0) ... (Y_i N_i) (Y_i+1 N_i+1) ...) Y_i) 
   N_i])



(define-metafunction jeff
  bound : Δ T -> N
  [(bound Δ Y) (lookup-bound Δ Y)]
  [(bound Δ N) N])

(define-judgment-form jeff
  #:mode (ok I I I)
  #:contract (ok p Δ T)
  [----------------------
   (ok p Δ (Object < >))]
  [(where ((Y_0 N_0) ... (Y N) (Y_1 N_1) ...) Δ)
   ----------------------
   (ok p Δ Y)]
  [(where (class C < (Y << N) ... > class-args (par ...) implements (N_1 ...) md_1 ...)
          (class-lookup p C))
   (ok p Δ T) ...
   (where (U_s ...) ((substitute-all N (Y ...) (T ...)) ...))
   (<: p Δ T U_s) ...
   ----------------------
   (ok p Δ (C < T ... >))]
  [(where (interface C < (Y << N) ... > extends (N_1 ...) mh ...)
          (class-lookup p C))
   (ok p Δ T) ...
   (where (U_s ...) ((substitute-all N (Y ...) (T ...)) ...))
   (<: p Δ T U_s) ...
   ----------------------
   (ok p Δ (C < T ... >))]
  )


(define-metafunction jeff
  is-interface : p N -> boolean
  [(is-interface p (C < T ... >))
   #t
   (where (interface C < (Z << P) ... > extends (N_parent ...) mh_1 ...)
          (class-lookup p C))]
  [(is-interface p (C < T ... >))
   #f])
  
; Expression typing
(define-judgment-form jeff
  #:mode (⊢ I I I I I O)
  #:contract (⊢ p Ξ Δ Γ ee T)
   
  ; Var
  [(side-condition (debug "Var::1"))
   (side-condition (debug (term ("lookup-type" Γ x))))
   (where T (lookup-type Γ x))
   (side-condition (debug "Var::2"))
   ----------------------
   (⊢ p Ξ Δ Γ x T)]

    ; Field
  ; TODO problem with (term (substitute-all U (U T C) ((StateResult < T >) (Unit < >) (DefaultState < T >))))
  [(side-condition (debug "Field::1"))
   (⊢ p Ξ Δ Γ ee_0 T_ee0) ; T_0 = (There < (StateResult < T >) (Unit < >) (DefaultState < T >) >)
   (side-condition (debug "Field::2"))
   (where T_b (bound Δ T_ee0)) ; T_b = (There < (StateResult < T >) (Unit < >) (DefaultState < T >) >)
   (side-condition (debug "Field::3"))
   (where ((T f) ... (T_i f_i) (T_1 f_1) ...) (fields p T_b))
   (side-condition (debug "Field::4"))
   ------------------------------------
   (⊢ p Ξ Δ Γ (ee_0 f_i) T_i)]  ; TODO sure to replace ϕ by ((pure))?

  ; Newgt
  [(side-condition (debug "New::0"))
   (where (class C < (Y_p << N_p) ... > class-args (par ...) implements (N_1 ...) md_1 ...)
          (class-lookup p C))
   (side-condition (debug "New::1"))
   (ok p Δ N)
   (side-condition (debug "New::2"))
   (where ((T f) ...) (fields p N))
   (side-condition (debug "New::3"))
   (⊢ p Ξ Δ Γ ee S) ...
   (side-condition (debug "New::4"))
   (<: p Δ S T) ...
   (side-condition (debug "New::5"))
   ---------------------------------
   (⊢ p Ξ Δ Γ (new (name N (C < T_p ... >)) ee ...) (substitute-all N (Y_p ...) (T_p ...)))]

  ; Call
  ; TODO problem with (term (substitute-all U (U T C) ((StateResult < T >) (Unit < >) (DefaultState < T >))))
  [(side-condition (debug "Call::1"))
   (⊢ p Ξ Δ Γ ee_0 T_ee0) ; T_0 = (There < (StateResult < T >) (Unit < >) (DefaultState < T >) >)
   (side-condition (debug "Call::2"))
   (where T_b (bound Δ T_ee0)) ; T_b = (There < (StateResult < T >) (Unit < >) (DefaultState < T >) >)
   (side-condition (debug "Call::3"))
   (side-condition (debug (term (m T_b))))
   (where (mod ((Y << P) ...) ((U x) ...) T Ξ_m) (mtype p m T_b)) ; (() ((Unit < >) (DefaultState < T >)) (StateResult < (Unit < >) >) ())
   (side-condition (debug "Call::4"))
   (<= p Δ Ξ Ξ_m)
   (side-condition (debug "Call::5"))
   (where (P_s ...) ((substitute-all P (Y ...) (V ...)) ...)) ; ()
   (side-condition (debug "Call::6"))
   (ok p Δ V) ... ; ()
   (side-condition (debug "Call::7"))
   (<: p Δ V P_s) ... ;()
   (side-condition (debug "Call::8"))
   (side-condition (debug (term "args" (ee_1 ...))))
   (⊢ p Ξ Δ Γ ee_1 S) ...
   (side-condition (debug "Call::9"))
   (where (U_s ...) ((substitute-all U (Y ...) (V ...)) ...))
   (side-condition (debug "Call::10"))
   (side-condition (debug (term (("<:" Δ S U_s) ...))))
   (<: p Δ S U_s) ...
   (side-condition (debug "Call::11"))
   (where T_s (substitute-all T (Y ...) (V ...)))
   (side-condition (debug "Call::12"))
   ------------------------------------
   (⊢ p Ξ Δ Γ (ee_0 < V ... > m ee_1 ...) T_s)]  ; TODO sure to replace ϕ by ((pure))?


  ;
  ; OpCall
  [;; DONE T_iface now is (C < T_p ... >) but it should be the interface that contains method m and is at the same time effectful
   ;; TODO search in interfaces is one-level (it does not recurse on parent interfaces)
;   (where ((T_eff0 any_0) ...
;           (T_iface (interface C_effi < tp_effi ... > extends (N_effi1 ...) mh_effi0 ...
;                      (effect header < tp_effj ... > W m ((W_0 x_0) ...)  F_effi)
;                      mh_effi1 ...
;                      ))
;           (T_eff1 any_1) ...)
;          (((C_eff < T_peff ... >) (class-lookup p C_eff)) ...))
   (side-condition (debug "OpCall::0"))
   (where N (C < W ... >))
   (side-condition (debug "OpCall::1"))
   (side-condition (debug (term ("mtype" m N))))
   (where (effect ((Y << P) ...) ((U x) ...) T Ξ_m) (mtype p m N))
   (side-condition (debug "OpCall::2"))
   (<= p Δ Ξ Ξ_m)
   (side-condition (debug "OpCall::3"))
   (<=1 p Δ Ξ N)
   (side-condition (debug "OpCall::4"))
   (where (P_s ...) ((substitute-all P (Y ...) (V ...)) ...))
   (side-condition (debug "OpCall::5"))
   (ok p Δ V) ...
   (side-condition (debug "OpCall::6"))
   (<: p Δ V P_s) ...
   (side-condition (debug "OpCall::7"))
   (⊢ p Ξ Δ Γ ee S) ...
   (side-condition (debug "OpCall::8"))
   (where (U_s ...) ((substitute-all U (Y ...) (V ...)) ...))
   (side-condition (debug "OpCall::9"))
   (side-condition (debug (term (("<:" Δ S U_s) ...))))
   (<: p Δ S U_s) ...
   (side-condition (debug "OpCall::10"))
   (where T_rs (substitute-all T (Y ...) (V ...)))
   (side-condition (debug "OpCall::11"))
   ------------------------------------
   (⊢ p Ξ Δ Γ (op C < W ... > < V ... > m ee ...) T_rs) ;H
                                                                         ]

  ;With
  [(side-condition (debug "With::1"))
   (⊢ p Ξ Δ Γ ee_0 T_0)
   (side-condition (debug "With::2"))
   (where T_b (bound Δ T_0)) 
   (side-condition (debug "With::3"))
   ;(side-condition ,(begin (display (term (Δ Γ (T_eff0 ...)  ee_0 (name T_0 (C_0 < T_p0 ... >))))) (newline) #t))
   (where (mod () ((U_in x_in)) U_out Ξ_return) (mtype p return T_b))
   (side-condition (debug "With::4"))
   ;(where T_out (handler-result-type p T_b))
   (where (N_eff ...) Ξ)
   (side-condition (debug "With::5"))
   (⊢ p (T_b N_eff ...) Δ Γ ee_1 T_1)
   (side-condition (debug "With::6"))
   (<: p Δ T_b (Handler < U_out U_in >))
   (side-condition (debug "With::7"))
   ;(side-condition ,(begin (display (term Δ)) (display "==") (display (term T_e)) (display (term " <: "))  (display (term U_in)) (newline) #t))
   (<: p Δ T_1 U_in)
   (side-condition (debug "With::8"))
   ---------------------------------
   (⊢ p Ξ Δ Γ (with ee_0 ee_1) U_out)]

  ;Let
  [(side-condition (debug "Let::1"))
   (side-condition (debug (term ee_0)))
   (⊢ p Ξ Δ ((x_0 T_0) ...) ee_0 S)
   (side-condition (debug "Let::2"))
   (<: p Δ S T)
   (side-condition (debug "Let::3"))
   (⊢ p Ξ Δ ((x T) (x_0 T_0) ...) ee_body T_body)
   (side-condition (debug "Let::4"))
   ---------------------------------
   (⊢ p Ξ Δ ((x_0 T_0) ...) (val x T ee_0 ee_body) T_body)]

    ; TODO IMPORTANT right semantics is to consider somehow H
  
  )

(define-metafunction jeff
  all-interfaces : p N -> (N ...)
  [(all-interfaces p (C < T_actual ... >)) ; TODO what about the inheritance chain of class extension???
   (N_rest ... N_substituted ...)
   (where (class C < (Y_p << T_p) ... > class-args ((U f) ...) implements ((C_2 < T_p2 ... >) ...) md ...)
          (class-lookup p C))
   (where (N_substituted ...) ((substitute-all (C_2 < T_p2 ... >) (Y_p ...) (T_actual ...)) ...))
   (where ((N_0 ...) ...) ((all-interfaces p N_substituted) ...))
   (where (N_rest ...)  ,(foldl (λ (x acc) (append acc (term ,x)))
                            (list)
                            (term ((N_0 ...) ...))))
   ]
  [(all-interfaces p (C < T_actual ... >)) ; TODO what about the inheritance chain of class extension???
   (N_rest ... N_substituted ...)
   (where (interface C < (Y_p << T_p) ... > extends ((C_2 < T_p2 ... >) ...) (header mod < tp ... > T_0 m_0 ((T x) ...)  Ξ) ...)
          (class-lookup p C))
   (where (N_substituted ...) ((substitute-all (C_2 < T_p2 ... >) (Y_p ...) (T_actual ...)) ...))
   (where ((N_0 ...) ...) ((all-interfaces p N_substituted) ...))
   (where (N_rest ...)  ,(foldl (λ (x acc) (append acc (term ,x)))
                            (list)
                            (term ((N_0 ...) ...))))
   ])


;; Get method names from interfaces
(define-metafunction jeff
  interfaces-methods : p (C ...) -> (m ...)
  [(interfaces-methods p ())
   ()]
  [(interfaces-methods p (C_0 C_1 ...))
   (m_0 ... m_2 ... m_1 ...)
   (where (interface C_0 < tp_0 ... > extends ((C_2 < T_p ... >) ...) (header mod < tp ... > T_0 m_0 ((T x) ...) Ξ) ...)
          (class-lookup p C_0))
   (where (m_1 ...) (interfaces-methods p (C_2 ...)))
   (where (m_2 ...) (interfaces-methods p (C_1 ...)))])

(define-metafunction jeff
  class-methods : p C -> (m ...)
  [(class-methods p C)
   (m_0 ...)
   (where (class C < tp_1 ... > class-args (par_1 ...) implements (N ...)
            (method (header mod < tp_2 ... > T_0 m_0 ((T x) ...)  Ξ_eff) ee) ...)
          (class-lookup p C))])



;; Method override

(define-judgment-form jeff
  #:mode (type-equal I I)
  #:contract (type-equal T T)
  [ ---------------------------------
   (type-equal T T)])

; TODO add effect checking to override
(define-judgment-form jeff
  #:mode (override I I I I I I I)
  #:contract (override p m N ((X N) ...) (T ...) T Ξ)
  [(side-condition (debug "override::1"))
   (side-condition (debug ("override" m N ((Y << P) ...) (T ...) T_0 Ξ)))
   (where (mod ((Z << Q) ...) ((U y) ..._1) U_0 Ξ_0) (mtype p m N)) ;; TODO maybe the _2 restriction can be lifted since we have sub-effecting
   (side-condition (debug "override::2"))
   (where (Q_s ...) ((substitute-all Q (Z ...) (Y ...)) ...))
   (side-condition (debug "override::3"))
   (where (U_s ...) ((substitute-all U (Z ...) (Y ...)) ...))
   (side-condition (debug "override::4"))
   (type-equal P Q_s) ...
   (side-condition (debug "override::5"))
   (type-equal T U_s) ...
   (side-condition (debug "override::6"))
   (where U_0s (substitute-all U_0 (Z ...) (Y ...)))
   (side-condition (debug "override::7"))
   (type-equal T_0 U_0s)
   (side-condition (debug "override::8"))
   (where Δ ((Y P) ... ))
   (side-condition (debug "override::9"))
   (side-condition (debug ("<=" Δ (substitute-all Ξ_0 (Z ...) (Y ...)) Ξ)))
   (<= p Δ (substitute-all Ξ_0 (Z ...) (Y ...)) Ξ)
   (side-condition (debug "override::10"))
   ;  TODO
   ;(where H (substitute-all Ξ_2 (Z ...) (Y ...)))
   ;(/</ p Γ Ξ H)
   ---------------------------------
   (override p m N ((Y P) ...) (T ..._1) T_0 Ξ)]

  [(side-condition (debug "override-trivial::1"))
   (side-condition (debug ("mtype" m N)))
   (where #f (mtype p m N))
   (side-condition (debug "override-trivial::2"))
   ; no implications
   ---------------------------------
  (override p m N ((Y P) ...) (T ..._1) T_0 Ξ)])
  

;; Method typing
(define-judgment-form jeff
  #:mode (method-ok-in I I I I I)
  #:contract (method-ok-in p Γ md C (tp ...))
  [(side-condition (debug "OK00"))
   (method-header-ok-in p mh_i C ((Y << N) ... ))
   (side-condition (debug "OK11"))
   (where Δ ((Y N) ... (Z P) ...))
   (side-condition (debug "OK22"))
   ;(side-condition ,(begin (display (term Δ)) (newline) #t))
   (where (T_out T_in) (handler-types p (C < Y ... >)))
   (side-condition (debug (term (T_out T_in))))
   (side-condition (debug "OK33"))
   ;(where T_out (substitute-all T_result (Y ...) (N ...)))
   
   (side-condition (debug
                    (term (Ξ_m Δ
                           (
                            (this (C < Y ... >))
                            (there (There < T_out T (C < Y ... >) >))
                            (x_1 T_1) ...)
                           ee_0)))
                   )
    (⊢ p Ξ_m Δ
      (
       (this (C < Y ... >))
       (there (Resume < T T_out T_in >))
       (x_1 T_1) ...
;       (x_field T_field) ...
       )
     
      ee_0 S)
    (side-condition (debug (term ("Delta : " Δ))))
    (side-condition (debug (term ("S : " S))))
    (<: p Δ S T_out)
    (side-condition (debug "OK4"))
   
   ; URGENT TODO
   ; TODO override interface methods?
   ---------------------------------
   (method-ok-in p ((x_field T_field) ...) (method (name mh_i (header effect < (Z << P) ... > T m ((T_1 x_1) ...)  Ξ_m)) ee_0) C ((Y << N) ... ))]

  [(side-condition (debug "methodok::1"))
   (side-condition (debug (term (not (eq? mod effect)))))
   (side-condition ,(not (eq? (term mod) (term effect))))
   (side-condition (debug "methodok::2"))
   (side-condition (debug ("method-header-ok-in"  mh_i C ((Y << N) ... ))))
   (method-header-ok-in p mh_i C ((Y << N) ... ))
   (side-condition (debug "methodok::3"))
   (where Δ ((Y N) ... (Z P) ...))
   (side-condition (debug "methodok::4"))
   (side-condition (debug (term ( Δ ((x_1 T_1) ... (this (C < Y ... >))) ee_0))))
   (side-condition (debug (term ("⊢" Ξ_m Δ ((this (C < Y ... >)) (x_1 T_1) ... (x_field T_field) ...)  ee_0))))
   ; (⊢ p Δ Γ ee T)
   (⊢ p Ξ_m Δ ((this (C < Y ... >)) (x_1 T_1) ... (x_field T_field) ...) ee_0 S)
   (side-condition (debug "methodok::5"))
   (side-condition (debug (term ( Δ ((x_1 T_1) ... (this (C < Y ... >))) ee_0 S))))
   (side-condition (debug (term ("Delta : "  Δ))))
   (side-condition (debug (term ("S : "  S  " <: " T))))
   (<: p Δ S T)
   (side-condition (debug "methodok::6"))
   ;(side-condition (debug (term ("/</" Ξ_2 Ξ))))
   ;(/</ p ((this (C < Y ... >)) (x_1 T_1) ... ) Ξ_2 Ξ); TODO is it ok here?
   ---------------------------------
   (method-ok-in p ((x_field T_field) ...) (method (name mh_i (header mod < (Z << P) ... > T m ((T_1 x_1) ...)  Ξ_m)) ee_0) C ((Y << N) ... ))])

(define-judgment-form jeff
  #:mode (method-header-ok-in I I I I)
  #:contract (method-header-ok-in p mh C (tp ...))
  [(side-condition (debug "method-header-ok-iface::0"))
   (side-condition (debug ("class-lookup:" C)))
   (where (interface C < (Y << N) ... > extends (N_1 ...) mh ...)
          (class-lookup p C))
   (side-condition (debug "method-header-ok-iface::1"))
   (where Δ ((Y N) ... (Z P) ...))
   (side-condition (debug "method-header-ok-iface::2"))
   (ok p Δ T_1) ...
   (side-condition (debug "method-header-ok-iface::3"))
   (ok p Δ T)
   (side-condition (debug "method-header-ok-iface::4"))
   (ok p Δ P) ...
   (side-condition (debug "method-header-ok-iface::5"))
   (side-condition (debug (("override" m N_1 ((Z P) ...) (T_1 ...) T Ξ) ...)))
   (override p  m N_1 ((Z P) ...) (T_1 ...) T Ξ) ...
   (side-condition (debug "method-header-ok-iface::6"))
   ; TODO override interface methods?
   ---------------------------------
   (method-header-ok-in p (header mod < (Z << P) ... > T m ((T_1 x_1) ...)  Ξ) C ((Y << N) ... ))]
  
  [(side-condition (debug "method-header-ok-class::0"))
   (where (class C < (Y << N) ... > class-args ((T_par f_par) ...) implements (N_1 ...) md ...)
          (class-lookup p C))
   (side-condition (debug "method-header-ok-class::1"))  
   (where Δ ((Y N) ... (Z P) ...))
   (side-condition (debug "method-header-ok-class::2"))  
   (ok p Δ T_1) ...
   (side-condition (debug "method-header-ok-class::3"))
   (side-condition (debug ("ok" Δ T)))
   (ok p Δ T)
   (side-condition (debug "method-header-ok-class::4"))  
   (ok p Δ P) ...
   (side-condition (debug "method-header-ok-class::5"))
   (side-condition (debug (("override" m N_1 ((Z P) ...) (T_1 ...) T Ξ) ...)))
   (override p m N_1 ((Z P) ...) (T_1 ...) T Ξ) ...
   (side-condition (debug "method-header-ok-class::6"))  
   ---------------------------------
   (method-header-ok-in p (header mod < (Z << P) ... > T m ((T_1 x_1) ...)  Ξ) C ((Y << N) ... ))])
   

;; Class typing
(define-judgment-form jeff
  #:mode (class-ok I I)
  #:contract (class-ok p cd)
  [(ok p ((Y N) ...) N) ...
   (ok p ((Y N) ...) T) ...
   ;(where ((U g) ...) (fields p N_parent))
   (side-condition (debug "class-ok::1"))
   (side-condition (debug (term (("method-ok-in" ((f T) ...) md C ((Y << N) ... )) ...))))
   (method-ok-in p ((f T) ...) md C ((Y << N) ... )) ...
   (side-condition (debug "class-ok::2"))
   ; fulfillment of interface contracts
   (where ((C_int < T_int ... >) ...) (N_1 ...))
   (side-condition (debug "class-ok::3"))   
   (where (m_1 ...) (interfaces-methods p (C_int ...)))
   (side-condition (debug "class-ok::4"))
   (side-condition ,(if (empty? (term (m_1 ...))) #t (set=? (term (m_1 ...)) (term (class-methods p C)))))
   (side-condition (debug "class-ok::5"))
   ---------------------------------
   (class-ok p (class C < (Y << N) ... > class-args ((T f) ...) implements (N_1 ...) md ...))])

(define-judgment-form jeff
  #:mode (interface-ok I I)
  #:contract (interface-ok p id)
  [(ok p ((Y N) ...) N) ...
   (ok p ((Y N) ...) N_1) ...
   (method-header-ok-in p mh C ((Y << N) ... )) ...
   ---------------------------------
   (interface-ok p (interface C < (Y << N) ... > extends (N_1 ...) mh ...))])


(define-metafunction jeff
  handler-types : p N -> any
  [(handler-types p (C < T ... >))
   (T_out T_in)
   (where (N_0 ... (Handler < T_out T_in >) N_2 ...) (all-interfaces p (C < T ... >)))]           
  [(handler-types p N)
   #f])

(define-metafunction jeff
  handler-result-type : p N -> any
  [(handler-result-type p (C < T ... >))
   T_outz
   (where (N_0 ... (Handler < T_in T_out >) N_2 ...) (all-interfaces p (C < T ... >)))]           
  [(handler-result-type p N)
   #f])








