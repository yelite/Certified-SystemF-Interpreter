Require Import lang.
Require Import lib.


Definition injection_symbol : ascii := "i".
Definition injection_var : exp := (exp_var "i").

Fixpoint _quote (t_env: type_env) (e: exp) : option exp :=
  match e with
  | exp_func v t_v e =>
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
  | exp_var v => Some (exp_var v)
  end.

Hint Transparent option_map.

Definition quote (e: exp) : option exp :=
  option_map (fun e' => exp_func injection_symbol identity_type e')
             (_quote empty_mapping e).

Definition unquote : exp :=
  let rtype := type_func identity_type (type_var "a") in
  exp_tfunc "a" (exp_func "q" rtype
                          (exp_app (exp_var "q") identity)).

Lemma strong_quote_nf : forall e e' t_env,
    _quote t_env e = Some e' ->
    nf e'.
Proof.
  intros e.
  induction e; intros e' t_env; simpl; try unfold option_map;
  intros H0.
  - remember ({a, t | t_env}) as t_env'.
    remember (_quote t_env' e) as oe.
    destruct oe as [e0|]; inversion H0.
    eauto.
  - remember (_typecheck t_env e1) as ot1.
    remember (_quote t_env e1) as oe1.
    remember (_quote t_env e2) as oe2.
    destruct ot1 as [t1|]; inversion H0.
    destruct oe1 as [e1'|]; inversion H0.
    destruct oe2 as [e2'|]; inversion H0.
    repeat constructor; eauto.
    + intros [v [e0 contra]].
      inversion contra.
    + intros [v [t_v [e0 contra]]].
      inversion contra.
    + intros [v [t_v [e0 contra]]].
      inversion contra.
  - remember (_quote t_env e) as oe.
    destruct oe as [e0'|]; inversion H0.
    constructor.
    eauto.
  - remember (_typecheck t_env e) as ot.
    remember (_quote t_env e) as oe.
    destruct ot as [t'|]; inversion H0.
    destruct oe as [e0'|]; inversion H0.
    repeat constructor; eauto.
    + intros [v [e0 contra]].
      inversion contra.
    + intros [v [t_v [e0 contra]]].
      inversion contra.
    + intros [v [e0 contra]].
      inversion contra.
  - inversion H0.
    auto.
Qed.


Theorem quote_nf : forall e e',
    quote e = Some e' ->
    nf e'.
Proof.
  intros e e' H.
  unfold quote in H.
  unfold option_map in H.
  remember (_quote empty_mapping e) as oe.
  destruct oe as [e0'|]; inversion H.
  remember (strong_quote_nf e e0' empty_mapping) as H0.
  constructor.
  auto.
Qed.


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


Lemma strong_quote_type : forall e e' env t0,
    no_injection_symbol e ->
    _quote env e = Some e' ->
    _typecheck env e = Some t0 ->
    _typecheck {injection_symbol, identity_type | env} e'
    = Some t0.
Proof.
  intros e e' env t0 Hi He Ht.
  apply typecheck_sound in Ht.
  apply typecheck_complete.
  generalize dependent e'.
  generalize dependent env.
  generalize dependent t0.
  induction e; intros t0 env Ht e0' He; simpl in He;
    try unfold option_map in He;
    inversion Ht; subst; inversion Hi.
  - remember {a, t | env} as new_env.
    remember (_quote new_env e) as oe'.
    destruct oe' as [e'|]; inversion He.
    constructor.
    rewrite (mapping_reorder _ _ _ _ _ H1).
    rewrite <- Heqnew_env.
    auto.
  - remember (_typecheck env e1) as ot1.
    remember (_quote env e1) as oe1'.
    remember (_quote env e2) as oe2'.
    destruct ot1 as [t1|]; inversion He.
    destruct oe1' as [e1'|]; inversion He.
    destruct oe2' as [e2'|]; inversion He.
    subst.
    apply tc_app with t_v;
      try apply tc_app with (type_func t_v t0);
      try apply tc_tapp with
      identity_type_symbol identity_inner_type;
      auto.
    (* i t1 |- t1 -> t1 *)
    apply typecheck_complete in H2.
    rewrite H2 in Heqot1.
    inversion Heqot1.
    auto.
  - remember (_quote env e) as oe'.
    destruct oe' as [e'|]; inversion He.
    auto.
  - remember (_typecheck env e) as ot'.
    remember (_quote env e) as oe'.
    destruct ot' as [t'|]; inversion He.
    destruct oe' as [e'|]; inversion He.
    apply tc_tapp with v t_e; auto.
    apply tc_app with (type_forall v t_e); auto.
    apply tc_tapp with
    identity_type_symbol identity_inner_type; auto.
    apply typecheck_complete in H2.
    rewrite H2 in Heqot'.
    inversion Heqot'.
    auto.
  - inversion He.
    constructor.
    unfold mapping_update.
    destruct (ascii_dec a injection_symbol).
    + contradiction.
    + auto.
Qed.


Theorem quote_type : forall e e' t0,
    no_injection_symbol e ->
    quote e = Some e' ->
    typecheck e = Some t0 ->
    typecheck e' = Some (type_func identity_type t0).
Proof.
  intros e e' t0 H0 H1.
  unfold quote in H1.
  unfold option_map in H1.
  remember (_quote empty_mapping e) as oe'.
  destruct oe'; destruct e'; inversion H1.
  subst. clear H1.
  intros H2.
  apply typecheck_complete.
  constructor.
  apply typecheck_sound.
  eapply strong_quote_type.
  apply H0.
  auto.
  auto.
Qed.


Lemma unquoted_wrapper : forall t e e',
    exp_subst e injection_symbol identity e' ->
    (exp_app (exp_tapp unquote t)
             (exp_func injection_symbol identity_type e)) ~ e'.
Proof.
  intros t e e' H0.
  remember (exp_func "q" (type_func identity_type t)
                     (exp_app (exp_var "q") identity)) as m.
  assert ((exp_tapp unquote t) ~ m).
  {
    apply equiv_base.
    apply bn_base.
    constructor.
    rewrite Heqm.
    apply tse_func.
    auto.
    unfold identity.
    unfold identity_type_var.
    unfold identity_type_symbol.
    eapply tse_app.
    auto.
    eapply tse_tfunc_p.
    congruence.
    auto.
  }
  subst.
  rewrite H.
  econstructor 3.
  repeat econstructor; try (intros contra; inversion contra).
  fold identity.
  repeat constructor.
  auto.
Qed.


Lemma identity_reduce : forall e t,
    (exp_app (exp_tapp identity t) e) ~ e.
Proof.
  intros e t.
  constructor.
  econstructor 2; repeat constructor.
Qed.


Lemma unquoted_free_eq : forall t e e' env,
    no_injection_symbol e ->
    _typecheck env e = Some t ->
    _quote env e = Some e' ->
    (subst_exp e' injection_symbol identity) ~ e.
Proof.
  intros t e e' env Hi Ht He.
  generalize dependent t.
  generalize dependent e'.
  generalize dependent env.
  induction e; intros env e' He t0 Ht;
    inversion Hi; subst; simpl in *.
  + unfold option_map in He.
    remember ({a, t | env}) as env'.
    option_match He e.
    option_match Ht t.
    subst.
    simpl.
    destruct (ascii_dec a injection_symbol); try contradiction.
    symmetry in Heqoe, Heqot.
    rewrite (IHe H3 _ _ Heqoe _ Heqot).
    reflexivity.
  + option_match He t1.
    option_match He e1.
    option_match He e2.
    destruct t1 as [|t10 t11|]; inversion Ht; subst.
    option_match Ht t2.
    clear He H0 H3.
    simpl.
    symmetry in Heqoe1, Heqoe2, Heqot1, Heqot2.
    rewrite (IHe1 H1 _ _ Heqoe1 _ Heqot1).
    rewrite (IHe2 H2 _ _ Heqoe2 _ Heqot2).
    rewrite identity_reduce.
    reflexivity.
  + unfold option_map in He.
    option_match Ht t.
    option_match He e.
    simpl.
    symmetry in Heqoe, Heqot.
    rewrite (IHe H0 _ _ Heqoe _ Heqot).
    reflexivity.
  + option_match He t.
    option_match He e.
    destruct t1; inversion Ht.
    simpl.
    rewrite identity_reduce.
    symmetry in Heqoe, Heqot.
    rewrite (IHe H0 _ _ Heqoe _ Heqot).
    reflexivity.
  + inversion He.
    simpl.
    destruct (ascii_dec a injection_symbol); try contradiction.
    reflexivity.
Qed.

      
Theorem unquoted_eq : forall e e' t,
    no_injection_symbol e ->
    quote e = Some e' ->
    typecheck e = Some t ->
    (exp_app (exp_tapp unquote t) e') ~ e.
Proof.
  intros e e0' t0 Hi Hq Ht.
  unfold quote in Hq.
  unfold option_map in Hq.
  option_match Hq e'.
  constructor 3 with (subst_exp e' injection_symbol identity).
  apply unquoted_wrapper; try (apply subst_exp_correct; auto).
  eapply unquoted_free_eq; eauto.
Qed.

