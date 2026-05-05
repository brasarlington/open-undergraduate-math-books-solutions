From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.

Theorem exercise_5_a : forall (U : Type) (A B C : Ensemble U),
  Union U (Intersection U A B) C = Intersection U (Union U A C) (Union U B C).
Proof.
  intros U A B C.
  apply Extensionality_Ensembles.
  unfold Same_set, Included.
  split.
  * intros u H. destruct H.
    ** constructor.
       *** destruct H. apply Union_introl. apply H.
       *** destruct H. apply Union_introl. apply H0.
    ** constructor.
       *** apply Union_intror. apply H.
       *** apply Union_intror. apply H.
  * intros u H. destruct H. destruct H. destruct H0.
    ** apply Union_introl. constructor.
       *** apply H.
       *** apply H0.
    ** apply Union_intror. apply H0.
    ** apply Union_intror. apply H.
Qed.


Theorem exercise_5_b : forall (U : Type) (A B C : Ensemble U),
  Intersection U (Union U A B) C = Union U (Intersection U A C) (Intersection U B C).
Proof.
  intros U A B C.
  apply Extensionality_Ensembles.
  unfold Same_set, Included.
  split.
  * intros u H. destruct H. destruct H.
    ** apply Union_introl. constructor.
       *** apply H.
       *** apply H0.
    ** apply Union_intror. constructor.
       *** apply H.
       *** apply H0.
  * intros u H. destruct H.
    ** destruct H. constructor.
       *** apply Union_introl. apply H.
       *** apply H0.
    ** destruct H. constructor.
       *** apply Union_intror. apply H.
       *** apply H0.
Qed.
