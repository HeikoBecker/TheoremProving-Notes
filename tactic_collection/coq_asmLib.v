(* http://coq-club.inria.narkive.com/NlEjZxtG/ltac-and-constr-arguments-with-holes *)

Tactic Notation "lift " tactic(t) :=
  fun H => t H.

Tactic Notation "match_pat" open_constr(pat) tactic(t) :=
  match goal with
  | [H: ?ty |- _ ] => unify pat ty; t H
  end.

Inductive ident (n:nat) : Type :=
|Box: n = 5 -> ident n.

Goal forall n, (ident n) -> ident n.
  intros.
  match_pat (ident _) (fun H => destruct H).
  auto.
  constructor; auto.
Qed.
  match_pat (ident _) (fun H => apply H).
