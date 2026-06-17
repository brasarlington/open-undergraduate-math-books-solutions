From Stdlib Require Import Sets.Ensembles.

Theorem exercise_2_4 : forall (U : Type) (A B : Ensemble U), (A = B) -> (Complement U A) = (Complement U B).
Proof.
  intros U A B HAB.
  rewrite HAB.
  reflexivity.
Qed.
