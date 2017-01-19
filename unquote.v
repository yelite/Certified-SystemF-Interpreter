Require Import Ascii.

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

Definition type_env := mapping type.

Inductive type_subst: type -> ascii -> type -> type -> Prop :=
  | ts_var_p: forall t_var t2,
      type_subst (type_var t_var) t_var t2 t2
  | ts_var_n: forall t_var1 t_var2 t2,
      t_var1 <> t_var2 ->
      type_subst (type_var t_var1) t_var2 t2
                 (type_var t_var1)
  | ts_func: forall t1 t2 t1' t2' t_var t3,
      type_subst t1 t_var t3 t1' ->
      type_subst t2 t_var t3 t2' ->
      type_subst (type_func t1 t2) t_var t3 (type_func t1' t2')
  | ts_forall_p: forall t_var1 t1 t1' t_var2 t2,
      t_var1 <> t_var2 ->
      type_subst t1 t_var2 t2 t1' ->
      type_subst (type_forall t_var1 t1)
                 t_var2 t2 (type_forall t_var1 t1')
  | ts_forall_n: forall t_var t1 t2,
      type_subst (type_forall t_var t1)
                 t_var t2 (type_forall t_var t1).
Hint Constructors type_subst.

Inductive type_subst_in_exp: exp -> ascii -> type -> exp -> Prop :=
  | tse_func: forall v t_v t_v' e1 e1' id t',
      type_subst t_v id t' t_v' ->
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
      type_subst t1 id t' t1' ->
      type_subst_in_exp (exp_tapp e t1) id t'
                        (exp_tapp e' t1')
  | tse_var: forall v id t',
      type_subst_in_exp (exp_var v) id t' (exp_var v).
Hint Constructors type_subst_in_exp.

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

Reserved Notation "env / e |- t"
         (at level 40, e at level 39).

Inductive type_checked: type_env -> exp -> type -> Prop :=
  | tc_func: forall t_env v t_v e t_e,
      { v, t_v | t_env } / e |- t_e ->
      t_env / (exp_func v t_v e) |- (type_func t_v t_e)
  | tc_app: forall t_env e1 e2 t_v t_e,
      t_env / e1 |- (type_func t_v t_e) ->
      t_env / e2 |- t_v ->
      t_env / (exp_app e1 e2) |- t_e
  | tc_tfunc: forall t_env v e t,
      t_env / e |- t ->
      t_env / (exp_tfunc v e) |- (type_forall v t)
  | tc_tapp: forall t_env e v t_e t t_result,
      t_env / e |- (type_forall v t_e) ->
      type_subst t_e v t t_result ->
      t_env / (exp_tapp e t) |- t_result
  | tc_var: forall t_env v t,
      (t_env v) = (Some t) ->
      t_env / (exp_var v) |- t
where "env / e |- t" := (type_checked env e t).
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

Definition nf (e: exp) : Prop :=
  ~ exists e', beta_reduction e e'.

Definition equivalent (e1 e2: exp) : Prop :=
  exists e', (e1 |>* e') /\ (e2 |>* e').

Notation "e1 ~ e2" := (equivalent e1 e2)
                        (at level 20).

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

Definition identity : exp :=
  (exp_tfunc "t" (exp_func "x" (type_var "t") (exp_var "x"))).

Definition identity_type :=
  type_forall "t" (type_func (type_var "t") (type_var "t")).

Fact identity_typechecked :
  Some identity_type = typecheck identity.
Proof.
  compute. reflexivity.
Qed.

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
                           (exp_tapp (exp_var "i") t) e1'
                        ) e2')
      | _, _, _ => None
      end 
  | exp_tfunc v e =>
      option_map (fun e' => exp_tfunc v e')
                 (_quote t_env e)
  | exp_tapp e t =>
      match _typecheck t_env e,
            _quote t_env e with
      | Some t, Some e' =>
          Some (exp_tapp (exp_app
                            (exp_tapp (exp_var "i") t) e'
                         ) t)
      | _, _ => None
      end
  | exp_var v => Some (exp_var v)
  end.

Definition quote (e: exp) : option exp :=
  option_map (fun e' => exp_func "i" identity_type e')
             (_quote empty_mapping e).

Definition unquote : exp :=
  let rtype := type_func identity_type (type_var "a") in
  exp_tfunc "a" (exp_func "q" rtype
                          (exp_app (exp_var "q") identity)).

Theorem quote_nf : forall e e',
    quote e = Some e' ->
    nf e'.
Proof.
Admitted.
         
Theorem quote_type : forall e e' t,
    quote e = Some e' ->
    typecheck e = Some t ->
    typecheck e' = Some (type_func identity_type t).
Admitted.

Theorem unquoted_eq : forall e e' t,
    quote e = Some e' ->
    typecheck e = Some t ->
    (exp_app (exp_tapp unquote t) e') ~ e.
Admitted.

      

