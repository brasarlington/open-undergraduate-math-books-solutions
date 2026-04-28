From Stdlib Require Import Sets.Ensembles.
From OUMBS Require Import chapter_1_exercises_2_point_1.

Theorem exercise_2_3 : forall (U : Type) (A B : Ensemble U), Included U A B -> Included U (Complement U B) (Complement U A).
Proof.
  unfold Included.
  unfold Complement.
  unfold In.
  unfold not.
  intros U A B Hx u Hu.
  intros HA. apply Hx in HA. apply Hu in HA. apply HA.
Qed.
