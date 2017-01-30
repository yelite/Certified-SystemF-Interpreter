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