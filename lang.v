Require Export Ascii.
Require Import lib.
Require Import FunctionalExtensionality.

Inductive type: Type :=
  | type_forall: ascii -> type -> type
  | type_func: type -> type -> type
  | type_var: ascii -> type.

Inductive exp: Type :=
  | exp_func: ascii -> type -> exp -> exp
  | exp_app: exp -> exp -> exp
  | exp_tfunc: ascii -> exp -> exp
  | exp_tapp: exp -> type -> exp
  | exp_var: ascii -> exp.

Definition type_eq_dec: forall t1 t2: type, {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality; apply ascii_dec.
Defined.

Definition mapping (A: Type) := ascii -> option A.

Definition empty_mapping {A: Type} : mapping A :=
  fun _ => None.

Definition mapping_update {A: Type} (m: mapping A)
           (k: ascii) (v: A) : mapping A :=
  fun x => if ascii_dec x k then (Some v) else m x.

Notation "{ k , v | m }" := (mapping_update m k v)
                            (at level 0, v at level 0).

Theorem mapping_reorder {A: Type} :
  forall env, forall k1 k2, forall v1 v2 : A,
    k1 <> k2 ->
    {k1, v1 | {k2, v2 | env}} = {k2, v2 | {k1, v1 | env}}.
Proof.
  intros env k1 k2 v1 v2 H0.
  unfold mapping_update.
  extensionality x.
  destruct (ascii_dec x k1); destruct (ascii_dec x k2);
    try (subst; contradiction);
    try (reflexivity).
Qed.


Definition type_env := mapping type.

Fixpoint subst_type (t: type) (id: ascii) (t': type) : type :=
  match t with
  | type_forall v t1 =>
      if ascii_dec id v
      then type_forall v t1
      else type_forall v (subst_type t1 id t')
  | type_func t1 t2 =>
      type_func (subst_type t1 id t')
                (subst_type t2 id t')
  | type_var v => if ascii_dec id v then t' else t
  end.

Inductive type_subst_in_exp: exp -> ascii -> type -> exp -> Prop :=
  | tse_func: forall v t_v t_v' e1 e1' id t',
      subst_type t_v id t' = t_v' ->
      type_subst_in_exp e1 id t' e1' ->
      type_subst_in_exp (exp_func v t_v e1)
                        id t' (exp_func v t_v' e1')
  | tse_app: forall e1 e1' e2 e2' id t',
      type_subst_in_exp e1 id t' e1' ->
      type_subst_in_exp e2 id t' e2' ->
      type_subst_in_exp (exp_app e1 e2) id t'
                        (exp_app e1' e2')
  | tse_tfunc_p: forall v e1 e1' id t',
      v <> id ->
      type_subst_in_exp e1 id t' e1' ->
      type_subst_in_exp (exp_tfunc v e1) id t'
                        (exp_tfunc v e1')
  | tse_tfunc_n: forall e1 id t',
      type_subst_in_exp (exp_tfunc id e1) id t'
                        (exp_tfunc id e1)
  | tse_tapp: forall e e' t1 t1' id t',
      type_subst_in_exp e id t' e' ->
      subst_type t1 id t' = t1' ->
      type_subst_in_exp (exp_tapp e t1) id t'
                        (exp_tapp e' t1')
  | tse_var: forall v id t',
      type_subst_in_exp (exp_var v) id t' (exp_var v).
Hint Constructors type_subst_in_exp.

Lemma type_subst_in_exp_total: forall e id t,
    exists e', type_subst_in_exp e id t e'.
Proof.
  intros e id t.
  induction e; try destruct IHe as [e' IHe].
  - exists (exp_func a (subst_type t0 id t) e').
    auto.
  - destruct IHe1 as [e1' IHe1].
    destruct IHe2 as [e2' IHe2].
    exists (exp_app e1' e2'). auto.
  - destruct (ascii_dec a id).
    + subst. exists (exp_tfunc id e). auto.
    + exists (exp_tfunc a e'). constructor; auto.
  - exists (exp_tapp e' (subst_type t0 id t)). auto.
  - exists (exp_var a). auto.
Qed.


Inductive exp_subst: exp -> ascii -> exp -> exp -> Prop :=
  | es_func_p: forall v t_v e1 e1' id e',
      v <> id ->
      exp_subst e1 id e' e1' ->
      exp_subst (exp_func v t_v e1) id e'
                (exp_func v t_v e1')
  | es_func_n: forall v t_v e1 e',
      exp_subst (exp_func v t_v e1) v e'
                (exp_func v t_v e1)
  | es_app: forall e1 e1' e2 e2' id e',
      exp_subst e1 id e' e1' ->
      exp_subst e2 id e' e2' ->
      exp_subst (exp_app e1 e2) id e'
                (exp_app e1' e2')
  | es_tfunc: forall v e1 e1' id e',
      exp_subst e1 id e' e1' ->
      exp_subst (exp_tfunc v e1) id e'
                (exp_tfunc v e1')
  | es_tapp: forall e1 e1' t id e',
      exp_subst e1 id e' e1' ->
      exp_subst (exp_tapp e1 t) id e'
                (exp_tapp e1' t)
  | es_var_p: forall id e',
      exp_subst (exp_var id) id e' e'
  | es_var_n: forall id1 id2 e',
      id1 <> id2 ->
      exp_subst (exp_var id1) id2 e' (exp_var id1).
Hint Constructors exp_subst.

Lemma exp_subst_total: forall e id e0,
    exists e', exp_subst e id e0 e'.
Proof.
  intros e id e0.
  induction e; try destruct IHe as [e' IHe].
  - destruct (ascii_dec a id).
    + exists (exp_func a t e). subst. auto.
    + exists (exp_func a t e'). constructor; auto.
  - destruct IHe1 as [e1' IHe1].
    destruct IHe2 as [e2' IHe2].
    exists (exp_app e1' e2'). auto.
  - exists (exp_tfunc a e'). auto.
  - exists (exp_tapp e' t). auto.
  - destruct (ascii_dec a id); subst.
    + exists e0. auto.
    + exists (exp_var a). auto.
Qed.


Reserved Notation "env |- e : t"
         (at level 40, e at level 39).

Inductive type_checked: type_env -> exp -> type -> Prop :=
  | tc_func: forall t_env v t_v e t_e,
      { v, t_v | t_env } |- e : t_e ->
      t_env |- (exp_func v t_v e) : (type_func t_v t_e)
  | tc_app: forall t_env e1 e2 t_v t_e,
      t_env |- e1 : (type_func t_v t_e) ->
      t_env |- e2 : t_v ->
      t_env |- (exp_app e1 e2) : t_e
  | tc_tfunc: forall t_env v e t,
      t_env |- e : t ->
      t_env |- (exp_tfunc v e) : (type_forall v t)
  | tc_tapp: forall t_env e v t_e t t_result,
      t_env |- e : (type_forall v t_e) ->
      subst_type t_e v t = t_result ->
      t_env |- (exp_tapp e t) : t_result
  | tc_var: forall t_env v t,
      (t_env v) = (Some t) ->
      t_env |- (exp_var v) : t
where "env |- e : t" := (type_checked env e t).
Hint Constructors type_checked.

Reserved Notation "e1 |> e2"
         (at level 40).

Inductive beta_reduction: exp -> exp -> Prop :=
  | br_func: forall v t_v e1 e1',
      e1 |> e1' ->
      (exp_func v t_v e1) |> (exp_func v t_v e1')
  | br_app_full: forall v t_v e_f e_f' e2,
      exp_subst e_f v e2 e_f' ->
      (exp_app (exp_func v t_v e_f) e2) |> e_f'
  | br_app_partial1: forall e1 e2 e1',
      e1 |> e1' ->
      (exp_app e1 e2) |> (exp_app e1' e2)
  | br_app_partial2: forall e1 e2 e2',
      e2 |> e2' ->
      (exp_app e1 e2) |> (exp_app e1 e2')
  | br_tfunc: forall v e1 e1',
      e1 |> e1' ->
      (exp_tfunc v e1) |> (exp_tfunc v e1')
  | br_tapp_full: forall v e2 e2' t,
      type_subst_in_exp e2 v t e2' ->
      (exp_tapp (exp_tfunc v e2) t) |> e2'
  | br_tapp_partial: forall e1 e1' t,
      e1 |> e1' ->
      (exp_tapp e1 t) |> (exp_tapp e1' t)
where "e1 |> e2" := (beta_reduction e1 e2).
Hint Constructors beta_reduction.

Reserved Notation "e1 |>* e2"
         (at level 40).

Inductive beta_reductions: exp -> exp -> Prop :=
  | bn_step: forall e1 e2 e3,
      e1 |> e2 ->
      e2 |>* e3 ->
      e1 |>* e3
  | bn_refl: forall e1,
      e1 |>* e1
where "e1 |>* e2" := (beta_reductions e1 e2).
Hint Constructors beta_reductions.

Inductive nf: exp -> Prop :=
  | nf_func: forall v t_v e1,
      nf e1 ->
      nf (exp_func v t_v e1)
  | nf_app: forall e1 e2,
      nf e1 ->
      nf e2 ->
      (~ exists v t_v e', e1 = (exp_func v t_v e')) ->
      nf (exp_app e1 e2)
  | nf_tfunc: forall v e1,
      nf e1 ->
      nf (exp_tfunc v e1)
  | nf_tapp: forall e1 t,
      nf e1 ->
      (~ exists v e', e1 = (exp_tfunc v e')) ->
      nf (exp_tapp e1 t)
  | nf_var: forall v,
      nf (exp_var v).
Hint Constructors nf.

Fact nf_iff_stuck : forall e,
    nf e <-> ~ exists e', beta_reduction e e'.
Proof.
  split.
  - intros H.
    induction e; intros [e' contra]; inversion H; subst;
      try (apply (IHe H1);
           inversion contra; subst;
           exists e1'; auto).
    + inversion contra; subst.
      * apply H4. exists v, t_v, e_f. reflexivity.
      * apply (IHe1 H2). exists e1'. auto.
      * apply (IHe2 H3). exists e2'. auto.
    + inversion contra; subst.
      * apply H3. exists v, e2. reflexivity.
      * apply (IHe H2). exists e1'. auto.
    + inversion contra.
  - intros H0.
    induction e; constructor.
    + apply IHe.
      intros [e' contra].
      apply H0.
      exists (exp_func a t e'). auto.
    + apply IHe1.
      intros [e' contra].
      apply H0.
      exists (exp_app e' e2). auto.
    + apply IHe2.
      intros [e' contra].
      apply H0.
      exists (exp_app e1 e'). auto.
    + intros [v [t_v [e' H]]]. subst.
      apply H0.
      destruct (exp_subst_total e' v e2) as [e H__subst].
      exists e. auto.
    + apply IHe.
      intros [e' contra].
      apply H0.
      exists (exp_tfunc a e'). auto.
    + apply IHe.
      intros [e' contra].
      apply H0.
      exists (exp_tapp e' t). auto.
    + intros [v [e' H]]. subst.
      apply H0.
      destruct (type_subst_in_exp_total e' v t) as [e'' H__subst].
      exists e''. auto.
Qed.


Definition equivalent (e1 e2: exp) : Prop :=
  exists e', (e1 |>* e') /\ (e2 |>* e').

Notation "e1 ~ e2" := (equivalent e1 e2)
                        (at level 20).


Fixpoint _typecheck (t_env: type_env) (e: exp) : option type :=
  match e with
  | exp_func v t_v e =>
      let new_t_env := { v, t_v | t_env } in
      match _typecheck new_t_env e with
      | Some t => Some (type_func t_v t)
      | None => None
      end
  | exp_app e1 e2 =>
      match (_typecheck t_env e1), (_typecheck t_env e2) with
      | Some (type_func t1 t2), Some t3 =>
          if type_eq_dec t1 t3
          then Some t2
          else None
      | _, _ => None
      end
  | exp_tfunc v e =>
      match _typecheck t_env e with
      | Some t => Some (type_forall v t)
      | None => None
      end
  | exp_tapp e1 t2 =>
      match _typecheck t_env e1 with
      | Some (type_forall v t1) =>
          Some (subst_type t1 v t2)
      | _ => None
      end
  | exp_var v => t_env v
  end.

Definition typecheck (e: exp) : option type :=
  _typecheck empty_mapping e.

Definition identity_type_symbol : ascii := "t".
Definition identity_type_var := (type_var identity_type_symbol).

Definition identity : exp :=
  (exp_tfunc identity_type_symbol
             (exp_func "x" identity_type_var (exp_var "x"))).

Definition identity_inner_type :=
  (type_func identity_type_var identity_type_var).

Definition identity_type :=
  type_forall identity_type_symbol identity_inner_type.

Fact identity_typechecked :
  Some identity_type = typecheck identity.
Proof.
  compute. reflexivity.
Qed.

Theorem typecheck_sound : forall env e t,
    _typecheck env e = Some t -> type_checked env e t.
Proof.
  intros env e. generalize dependent env.
  induction e; intros env t' H0; simpl in H0.
  - remember {a, t | env} as env'.
    remember (_typecheck env' e) as ot.
    destruct ot; inversion H0.
    apply tc_func.
    rewrite <- Heqenv'.
    auto.
  - remember (_typecheck env e1) as ot1.
    remember (_typecheck env e2) as ot2.
    destruct ot1 as [t1|];
      try solve by inversion;
      destruct t1 as [|t1 t0|]; try solve by inversion.
    destruct ot2 as [t2|];
      try solve by inversion.
    destruct (type_eq_dec t1 t2); try solve by inversion.
    inversion H0. subst.
    apply tc_app with t2; auto.
  - remember (_typecheck env e) as ot.
    destruct ot as [t|]; try solve by inversion.
    inversion H0. subst.
    apply tc_tfunc. auto.
  - remember (_typecheck env e) as ot.
    destruct ot as [t0|]; try solve by inversion.
    destruct t0; try solve by inversion.
    inversion H0. subst.
    apply tc_tapp with a t0; auto.
  - auto.
Qed.

Theorem typecheck_complete : forall env e t,
    type_checked env e t -> _typecheck env e = Some t.
Proof.
  intros env e t H0.
  induction H0; simpl; try rewrite IHtype_checked; try reflexivity.
  - rewrite IHtype_checked1. rewrite IHtype_checked2.
    destruct (type_eq_dec t_v t_v) as [b|b]; try elim b; reflexivity.
  - subst. reflexivity.
  - auto.
Qed.

Hint Resolve typecheck_sound.
Hint Resolve typecheck_complete.


