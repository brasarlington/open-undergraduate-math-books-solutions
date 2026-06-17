From Stdlib Require Import Sets.Ensembles.

Theorem exercise_2_1_a : forall (U : Type) (A B C D: Ensemble U), Included U A B -> Included U C D -> Included U (Union U A C) (Union U B D).
Proof.
  unfold Included.
  intros U A B C D HAB HCD.
  intros u Hiu.
  destruct Hiu.
  * apply HAB in H. apply Union_introl with (C := D) in H. apply H.
  * apply HCD in H. apply Union_intror with (B := B) in H. apply H.
Qed.

Theorem exercise_2_1_b : forall (U : Type) (A B C D: Ensemble U), Included U A B -> Included U C D -> Included U (Intersection U A C) (Intersection U B D).
Proof.
  unfold Included.
  intros U A B C D HAB HCD u Hu. destruct Hu. apply HAB in H. apply HCD in H0. split.
  * apply H.
  * apply H0.
Qed.
