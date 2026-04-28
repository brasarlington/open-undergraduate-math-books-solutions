From Stdlib Require Import Sets.Ensembles.

Theorem exercise_2_6 : forall (U : Type) (A B C: Ensemble U), Included U A B -> Included U B C -> Included U A C.
Proof.
  unfold Included.
  unfold In.
  intros U A B C HiAB HiBC u HA.
  apply HiAB in HA. apply HiBC in HA. apply HA.
Qed.
