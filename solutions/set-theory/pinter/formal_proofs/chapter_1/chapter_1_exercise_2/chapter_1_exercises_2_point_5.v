From Stdlib Require Import Sets.Ensembles.

Theorem exercise_2_5 : forall (U : Type) (A B C : Ensemble U), (A = B) -> Included U A C -> Included U B C.
Proof.
  intros U A B C HAB HiAC.
  rewrite <- HAB. apply HiAC.
Qed.
