From Stdlib Require Import Sets.Ensembles.
From OUMBS Require Import Definitions.

Theorem exercise_1_40_ii :
  forall (Index U : Type) (A : Indexed_Family Index U) (B : Ensemble U),
    (forall i : Index, Included U B (Limit A i)) ->
    Included U B (General_Intersection A).
Proof.
  unfold Included, General_Intersection.
  intros Index U A B H u Hu i.
  apply (H i u). apply Hu.
Qed.
