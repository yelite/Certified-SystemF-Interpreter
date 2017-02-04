Require Import lang.
Require Import lib.
Require Import Ascii.


Definition injection_symbol : ascii := "i".
Definition injection_var : exp := (exp_var "i").


Fixpoint _quote (t_env : type_env) (e : exp) : option exp :=
  match e with
  | exp_func v t_v e =>
    if (ascii_dec v injection_symbol) then None else
      let new_t_env := { v, t_v | t_env } in
      option_map (fun e' => exp_func v t_v e')
                 (_quote new_t_env e)
  | exp_app e1 e2 =>
      match _typecheck t_env e1,
            _quote t_env e1,
            _quote t_env e2 with
      | Some t, Some e1', Some e2' =>
          Some (exp_app (exp_app
                           (exp_tapp injection_var t) e1'
                        ) e2')
      | _, _, _ => None
      end 
  | exp_tfunc v e =>
    if (ascii_dec v injection_symbol) then None else
      option_map (fun e' => exp_tfunc v e')
                 (_quote t_env e)
  | exp_tapp e t =>
      match _typecheck t_env e,
            _quote t_env e with
      | Some t', Some e' =>
          Some (exp_tapp (exp_app
                            (exp_tapp injection_var t') e'
                         ) t)
      | _, _ => None
      end
  | exp_var v => if (ascii_dec v injection_symbol) then None else Some (exp_var v)
  end.

Hint Transparent option_map.

Definition quote (e: exp) : option exp :=
  option_map (fun e' => exp_func injection_symbol identity_type e')
             (_quote empty_mapping e).


Inductive no_injection_symbol : exp -> Prop :=
  | nis_func: forall v t_v e,
      v <> injection_symbol ->
      no_injection_symbol e ->
      no_injection_symbol (exp_func v t_v e)
  | nis_app: forall e1 e2,
      no_injection_symbol e1 ->
      no_injection_symbol e2 ->
      no_injection_symbol (exp_app e1 e2)
  | nis_tfunc: forall v e,
      no_injection_symbol e ->
      no_injection_symbol (exp_tfunc v e)
  | nis_tapp: forall e t,
      no_injection_symbol e ->
      no_injection_symbol (exp_tapp e t)
  | nis_var: forall v,
      v <> injection_symbol ->
      no_injection_symbol (exp_var v).

Hint Constructors no_injection_symbol.


Lemma _quote_nis : forall e e' env,
    _quote env e = Some e' ->
    no_injection_symbol e.
Proof.
  intros e.
  induction e; intros e' env Hq; simpl in Hq;
    destruct_prem; unfold option_map in *; destruct_match; eauto.
Qed.

Hint Resolve _quote_nis.

Lemma quote_nis : forall e e',
    quote e = Some e' ->
    no_injection_symbol e.
Proof.
  intros e e' H.
  unfold quote in H.
  unfold option_map in H.
  destruct_match.
  eauto.
Qed.

Hint Resolve quote_nis.


Definition unquote : exp :=
  let rtype := type_func identity_type (type_var "a") in
  exp_tfunc "a" (exp_func "q" rtype
                          (exp_app (exp_var "q") identity)).


Lemma strong_quote_nf : forall e e' t_env,
    _quote t_env e = Some e' ->
    nf e'.
Proof.
  intros e.
  induction e; intros; simpl in *; try unfold option_map in *;
    destruct_match; repeat constructor; intuition;
      destruct_ex; solve_by_inversion_step eauto.
Qed.

Hint Resolve strong_quote_nf.


Theorem quote_nf : forall e e',
    quote e = Some e' ->
    nf e'.
Proof.
  intros e e' H.
  unfold quote in H.
  unfold option_map in H.
  destruct_match.
  eauto.
Qed.


Lemma typecheck_without_i : forall e env,
    no_injection_symbol e ->
    _typecheck env e = _typecheck {injection_symbol, identity_type | env} e.
Proof.
  intros e.
  induction e; intros env Hi; simpl; inversion Hi;
    auto_cond_rewrite; try rewrite mapping_reorder by auto; eauto.
  (* only the variable case left *)
  unfold mapping_update.
  destruct_prem.
  reflexivity.
Qed.
    

Lemma identity_app_type : forall e env t,
    no_injection_symbol e ->
    _typecheck env e = Some t ->
    _typecheck {injection_symbol, identity_type | env}
               (exp_app (exp_tapp injection_var t) e) = Some t.
Proof.
  intros e env t Hi Ht.
  simpl.
  rewrite <- typecheck_without_i by auto.
  multi_rewrite 1.
  destruct_prem.
  reflexivity.
Qed.

Hint Resolve identity_app_type.

Lemma identity_app_type' : forall e env t,
    no_injection_symbol e ->
    / env |- e : t ->
    / {injection_symbol, identity_type | env} |-
    (exp_app (exp_tapp injection_var t) e) : t.
Proof.
  intros.
  auto.
Qed.

Hint Resolve identity_app_type'.

(* Lemmas for automations *)

Lemma quote_func_type : forall v t_v e0 t0 env,
    v <> injection_symbol ->
    / {injection_symbol, identity_type | {v, t_v | env}} |- e0 : t0 ->
    / {injection_symbol, identity_type | env} |-
    exp_func v t_v e0 : type_func t_v t0.
Proof.
  intros.
  constructor.
  rewrite mapping_reorder by auto.
  assumption.
Qed.

Lemma quote_app_type : forall e1 e2 t0 t1 env env',
    env' = {injection_symbol, identity_type | env} ->
    / env' |- e1 : type_func t0 t1 ->
    / env' |- e2 : t0 ->
    / env' |- exp_app (exp_app (exp_tapp injection_var
                                        (type_func t0 t1)) e1) e2 : t1.
Proof.
  intros e1 e2 t0 t1 env env' He H1 H2.
  rewrite He in *.
  repeat econstructor; auto.
Qed.

Lemma quote_tapp_type : forall e1 t2 v t1 env env',
    env' = {injection_symbol, identity_type | env} ->
    / env' |- e1 : type_forall v t1 ->
    / env' |- exp_tapp (exp_app (exp_tapp injection_var
                                         (type_forall v t1)) e1) t2 :
               subst_type t1 v t2.
Proof.
  intros e1 t2 v t1 env env' He H1.
  rewrite He in *.
  repeat econstructor.
  auto.
Qed.

Lemma quote_var_type: forall v t env,
    v <> injection_symbol ->
    env v = Some t ->
    / {injection_symbol, identity_type | env} |- exp_var v : t.
Proof.
  intros.
  constructor.
  unfold mapping_update.
  destruct_prem.
  assumption.
Qed.

Hint Resolve
     quote_func_type
     quote_app_type
     quote_tapp_type
     quote_var_type.


Ltac rewrite_type_equiv :=
  repeat match goal with
         | [H1 : Some _ = _typecheck ?env ?e, H2 : / ?env |- ?e : _ |- _] =>
           apply typecheck_complete in H2; rewrite H2 in H1; inversion H1
         end.

Lemma strong_quote_type : forall e e' env t0,
    _quote env e = Some e' ->
    _typecheck env e = Some t0 ->
    _typecheck {injection_symbol, identity_type | env} e'
    = Some t0.
Proof.
  intros e e' env t0 He Ht.
  generalize (_quote_nis _ _ _ He).
  intros Hi.
  apply typecheck_sound in Ht.
  apply typecheck_complete.
  generalize dependent e'.
  generalize dependent env.
  generalize dependent t0.
  induction e; intros t0 env Ht e0' He; simpl in He;
    try unfold option_map in He; inversion Ht; subst; inversion Hi;
      destruct_match ; rewrite_type_equiv; remove_option_wrapper; eauto.
Qed.

Hint Resolve strong_quote_type.


Theorem quote_type : forall e e' t0,
    quote e = Some e' ->
    typecheck e = Some t0 ->
    typecheck e' = Some (type_func identity_type t0).
Proof.
  intros e e' t0 H1 H2.
  unfold quote in H1.
  unfold option_map in H1.
  destruct_match.
  apply typecheck_complete.
  eauto.
Qed.


(* don't have a decision procedure for reduction,
   so this proof is quite verbose *)
Lemma unquoted_wrapper : forall t e e',
    exp_subst e injection_symbol identity e' ->
    (exp_app (exp_tapp unquote t)
             (exp_func injection_symbol identity_type e)) ~ e'.
Proof.
  intros t e e' H0.
  assert ((exp_tapp unquote t)
            ~ (exp_func "q" (type_func identity_type t)
                        (exp_app (exp_var "q") identity))) as H.
  {
    repeat constructor.
    unfold identity_type_symbol.
    congruence.
  }
  rewrite H.
  (* needs two steps of reductions here *)
  econstructor 3;
    repeat econstructor; try (intros contra; inversion contra).
  assumption.
Qed.

(*
  it's nice to have these trivial lemmas,
  since using eauto is much easier than rewrite 
 *)
Lemma identity_reduce : forall e t,
    (exp_app (exp_tapp identity t) e) ~ e.
Proof.
  intros e t.
  constructor.
  econstructor 2; repeat constructor.
Qed.

Lemma exp_func_equiv : forall v t_v e1 e2,
    e1 ~ e2 ->
    exp_func v t_v e1 ~ exp_func v t_v e2.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma exp_app_equiv : forall e1 e2 e1' e2',
    e1 ~ e1' ->
    e2 ~ e2' ->
    exp_app e1 e2 ~ exp_app e1' e2'.
Proof.
  intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma exp_tfunc_equiv : forall v e e',
    e ~ e' ->
    exp_tfunc v e ~ exp_tfunc v e'.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma exp_tapp_equiv : forall e e' t,
    e ~ e' ->
    exp_tapp e t ~ exp_tapp e' t.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.


Hint Resolve identity_reduce.
Hint Resolve exp_func_equiv.
Hint Resolve exp_app_equiv.
Hint Resolve exp_tfunc_equiv.
Hint Resolve exp_tapp_equiv.


Lemma unquoted_free_eq : forall t e e' env,
    _typecheck env e = Some t ->
    _quote env e = Some e' ->
    (subst_exp e' injection_symbol identity) ~ e.
Proof.
  intros t e e' env Ht He.
  generalize (_quote_nis _ _ _ He).
  intros Hi.
  generalize dependent t.
  generalize dependent e'.
  generalize dependent env.
  induction e; intros env e' He t0 Ht;
    inversion Hi; inversion He; subst; simpl in *;
      try unfold option_map in *;
      destruct_match; simpl; destruct_prem; eauto.
Qed.

Hint Resolve unquoted_wrapper.
Hint Resolve unquoted_free_eq.


Theorem unquoted_eq : forall e e' t,
    quote e = Some e' ->
    typecheck e = Some t ->
    (exp_app (exp_tapp unquote t) e') ~ e.
Proof.
  intros e e0' t0 Hq Ht.
  unfold quote in Hq.
  unfold option_map in Hq.
  option_match Hq e'.
  constructor 3 with (subst_exp e' injection_symbol identity); eauto.
  apply unquoted_wrapper.
  apply subst_exp_correct.
  auto.
Qed.

