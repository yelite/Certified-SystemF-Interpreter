(** Solve by inversion,
    taken from SfLib.v of Software Foundation book *)

Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; t ]
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.


(* to simplify the handling of _quote / _typecheck = Some _ *)
Ltac option_match H n :=
  let OE := fresh "o" n in
  let E := fresh n in
  match type of H with
    (match ?oe with
     | Some _ => _
     | None => None
     end = _ ) =>
    remember oe as OE;
    destruct OE as [E |];
    inversion H
  end.


Ltac auto_cond_rewrite :=
  match goal with
  | [H1 : forall _, _ -> _ = _, H2 : _ |- _] =>
    rewrite (H1 _ H2); auto; clear H1 H2; auto_cond_rewrite
  | _ => idtac
  end.

Ltac multi_rewrite n :=
  match n with
    | S ?n' =>
      match goal with
      | [H : _ = _ |- _] =>
        rewrite H; try multi_rewrite n'
      | _ => idtac
      end
  end.

Ltac destruct_prem :=
  repeat match goal with
         | |- context[if ?P then _ else _] =>
           destruct P; try contradiction
         end.

Ltac destruct_match :=
  repeat match goal with
           H : (match ?x with _ => _ end = _) |- _ =>
           let n := fresh "n" in
           remember x as n; destruct n; inversion H
         end.

Ltac destruct_ex :=
  repeat match goal with
  | [H1 : ex _ |- _] => destruct H1
  end.


Ltac solve_double_neg :=
  match goal with
  | [H1 : ~?P -> ?Q |- ?Q] => apply H1; intros [e' contra]; eauto
  end.

Ltac solve_by_destruct_ex :=
  destruct_ex; subst; solve [eauto].
