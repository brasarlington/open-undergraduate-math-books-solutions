From Stdlib Require Import Sets.Ensembles.
From OUMBS Require Import chapter_1_exercises_2_point_1.

Theorem exercise_2_2_a : forall (U : Type) (A B C D : Ensemble U), (A = B) -> (C = D) -> (Union U A C) = (Union U B D).
Proof.
  intros U A B C D HAB HCD. rewrite HAB. rewrite HCD. reflexivity.
Qed.

Theorem exercise_2_2_b : forall (U : Type) (A B C D : Ensemble U), (A = B) -> (C = D) -> (Intersection U A C) = (Intersection U B D).
Proof.
  intros U A B C D HAB HCD. rewrite HAB. rewrite HCD. reflexivity.
Qed.
