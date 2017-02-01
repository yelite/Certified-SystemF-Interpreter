This is a certified self-interpreter for System F using the shallow representation from paper [Breaking Through the Normalization Barrier: A Self-Interpreter for F-omega](http://web.cs.ucla.edu/~palsberg/paper/popl16-full.pdf).

Three main theorems are proved:
```coq
(* the quoted representation is normalized *)
Theorem quote_nf : forall e e',
    quote e = Some e' ->
    nf e'.
    
(* the quoted representation is typed correctly *)
Theorem quote_type : forall e e' t0,
    no_injection_symbol e ->
    quote e = Some e' ->
    typecheck e = Some t0 ->
    typecheck e' = Some (type_func identity_type t0).
    
(* unquoted representation is equivalent to the original term*)
Theorem unquoted_eq : forall e e' t,
    no_injection_symbol e ->
    quote e = Some e' ->
    typecheck e = Some t ->
    (exp_app (exp_tapp unquote t) e') ~ e.
```
