From Stdlib Require Import Sets.Ensembles.

Theorem exercise_2_7_a : forall (U : Type) (A B : Ensemble U),
  Included U A B /\ Included U B A -> B = A.
Proof.
  intros U A B H.
  apply Extensionality_Ensembles.
  unfold Same_set. apply and_comm. apply H.
Qed.

Theorem exercise_2_7_b : forall (U : Type) (A B C: Ensemble U),
  Included U A B -> Included U B C -> Included U A C.
Proof.
  unfold Included.
  unfold In.
  intros U A B C HiAB HiBC u HA.
  apply HiAB in HA. apply HiBC in HA. apply HA.
Qed.
