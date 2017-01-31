Require Export Ascii.
Require Export SetoidClass.

Require Import Relations.
Require Import Morphisms.
Require Import lib.
Require Import FunctionalExtensionality.

Inductive type : Type :=
  | type_forall: ascii -> type -> type
  | type_func: type -> type -> type
  | type_var: ascii -> type.

Inductive exp : Type :=
  | exp_func: ascii -> type -> exp -> exp
  | exp_app: exp -> exp -> exp
  | exp_tfunc: ascii -> exp -> exp
  | exp_tapp: exp -> type -> exp
  | exp_var: ascii -> exp.

Definition type_eq_dec: forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality; apply ascii_dec.
Defined.

Definition exp_eq_dec: forall e1 e2 : exp, {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality; try apply type_eq_dec; try apply ascii_dec.
Qed.

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
  repeat destruct_prem.
  all: subst; try contradiction; auto.
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

Fixpoint subst_type_in_exp (e : exp) (id : ascii) (t : type) : exp :=
  match e with
  | exp_func v t_v e0 => exp_func v (subst_type t_v id t)
                                 (subst_type_in_exp e0 id t)
  | exp_app e1 e2 => exp_app (subst_type_in_exp e1 id t)
                            (subst_type_in_exp e2 id t)
  | exp_tfunc v e0 =>
    if (ascii_dec v id) then e else exp_tfunc v (subst_type_in_exp e0 id t)
  | exp_tapp e1 t2 => exp_tapp (subst_type_in_exp e1 id t) (subst_type t2 id t)
  | exp_var v => e
  end.


Theorem subst_type_in_exp_correct : forall e id t e',
    subst_type_in_exp e id t = e' <-> type_subst_in_exp e id t e'.
Proof.
  intros e id t.
  split; generalize dependent e'.
  - induction e; intros; simpl in *; subst;
      destruct_prem; solve_by_rewrite; auto.
  - induction e; intros e' H; inversion H; subst; simpl;
    destruct_prem; auto_cond_rewrite; auto.
Qed.
Hint Resolve -> subst_type_in_exp_correct.
Hint Resolve <- subst_type_in_exp_correct.


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

Fixpoint subst_exp (e : exp) (id : ascii) (e0 : exp) : exp :=
  match e with
  | exp_func v t_v e1 =>
    if (ascii_dec v id) then e else exp_func v t_v (subst_exp e1 id e0)
  | exp_app e1 e2 => exp_app (subst_exp e1 id e0) (subst_exp e2 id e0)
  | exp_tfunc v e1 => exp_tfunc v (subst_exp e1 id e0)
  | exp_tapp e1 t => exp_tapp (subst_exp e1 id e0) t
  | exp_var v => if (ascii_dec v id) then e0 else e
  end.

Theorem subst_exp_correct : forall e id e0 e',
    subst_exp e id e0 = e' <-> exp_subst e id e0 e'.
Proof.
  intros e id e0 e'.
  split; generalize dependent e'.
  - induction e; intros; simpl in *; subst;
      destruct_prem; solve_by_rewrite; auto.
  - induction e; intros e' H; inversion H; subst; simpl;
      destruct_prem; auto_cond_rewrite; auto.
Qed.
Hint Resolve -> subst_exp_correct.
Hint Resolve <- subst_exp_correct.


Reserved Notation "/ env |- e : t"
         (at level 40, e at level 39).

Inductive type_checked: type_env -> exp -> type -> Prop :=
  | tc_func: forall t_env v t_v e t_e,
      / { v, t_v | t_env } |- e : t_e ->
      / t_env |- (exp_func v t_v e) : (type_func t_v t_e)
  | tc_app: forall t_env e1 e2 t_v t_e,
      / t_env |- e1 : (type_func t_v t_e) ->
      / t_env |- e2 : t_v ->
      / t_env |- (exp_app e1 e2) : t_e
  | tc_tfunc: forall t_env v e t,
      / t_env |- e : t ->
      / t_env |- (exp_tfunc v e) : (type_forall v t)
  | tc_tapp: forall t_env e v t_e t t_result,
      / t_env |- e : (type_forall v t_e) ->
      subst_type t_e v t = t_result ->
      / t_env |- (exp_tapp e t) : t_result
  | tc_var: forall t_env v t,
      (t_env v) = (Some t) ->
      / t_env |- (exp_var v) : t
where "/ env |- e : t" := (type_checked env e t).
Hint Constructors type_checked.

Reserved Notation "e1 |> e2"
         (at level 40).

(* small step semantics *)
Inductive beta_reduction: relation exp :=
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

(* the reflexive transitive closure of small step *)
Inductive beta_reductions: relation exp :=
  | bn_base: forall e1 e2,
      e1 |> e2 ->
      e1 |>* e2
  | bn_trans: forall e1 e2 e3,
      e1 |>* e2 ->
      e2 |>* e3 ->
      e1 |>* e3
  | bn_refl: forall e1,
      e1 |>* e1
where "e1 |>* e2" := (beta_reductions e1 e2).
Hint Constructors beta_reductions.

(* a convenient definition of normal form *)
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


(* prove this definition is correct *)
Fact nf_iff_stuck : forall e,
    nf e <-> ~ exists e', beta_reduction e e'.
Proof.
  split.
  - intros H.
    induction e; intros [e' contra]; inversion H; subst;
      inversion contra; subst; intuition; eauto.
  - intros H0.
    induction e; constructor;
      first [ solve_double_neg
            | intuition; solve_by_destruct_ex].
Qed.


Reserved Notation "e1 ~ e2" (at level 20).

(* the symmetric transitive closure of reductions *)
Inductive equivalent : relation exp :=
  | equiv_base : forall e1 e2,
      e1 |>* e2 ->
      e1 ~ e2
  | equiv_symmetric : forall e1 e2,
      e1 ~ e2 ->
      e2 ~ e1
  | equiv_transitive : forall e1 e2 e3,
      e1 ~ e2 ->
      e2 ~ e3 ->
      e1 ~ e3
where "e1 ~ e2" := (equivalent e1 e2).
Hint Constructors equivalent.


(* prove Equivalence and Proper for each constructors for rewriting *)
Instance equiv_Equiv : Equivalence equivalent.
Proof.
  split; eauto.
Qed.

Ltac equiv_induction :=
  match goal with
    H1: _ ~ _ |- _ =>
    induction H1; eauto;
    match goal with
      H2: _ |>* _ |- _ => induction H2; eauto
    end
  end.

Instance exp_func_Proper :
  Proper (eq ==> eq ==> equivalent ==> equivalent) exp_func.
Proof.
  intros v1 v2 Hv t1 t2 Ht e1 e2 He.
  subst.
  equiv_induction.
Qed.

Instance exp_app_full_Proper :
  Proper (equivalent ==> equivalent ==> equivalent) exp_app.
Proof.
  intros e1 e1' H1 e2 e2' H2.
  transitivity (exp_app e1 e2'); equiv_induction.
Qed.

Instance exp_tfunc_Proper :
  Proper (eq ==> equivalent ==> equivalent) exp_tfunc.
Proof.
  intros v1 v2 Hv e1 e2 He.
  subst.
  equiv_induction.
Qed.

Instance exp_tapp_Proper :
  Proper (equivalent ==> eq ==> equivalent) exp_tapp.
Proof.
  intros e1 e2 He t1 t2 Ht.
  subst.
  equiv_induction.
Qed.


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
  reflexivity.
Qed.

Theorem typecheck_sound : forall env e t,
    _typecheck env e = Some t -> / env |- e : t.
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
    / env |- e : t -> _typecheck env e = Some t.
Proof.
  intros env e t H0.
  induction H0; simpl; try solve_by_rewrite.
  - rewrite IHtype_checked1. rewrite IHtype_checked2.
    destruct (type_eq_dec t_v t_v) as [b|b]; try elim b; reflexivity.
  - rewrite IHtype_checked. rewrite H. reflexivity.
Qed.

Hint Resolve typecheck_sound.
Hint Resolve typecheck_complete.


