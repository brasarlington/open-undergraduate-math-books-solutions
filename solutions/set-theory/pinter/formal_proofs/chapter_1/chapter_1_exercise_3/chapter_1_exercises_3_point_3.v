From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.

(**
You can (and there is good arguments for it) use both branches and try to demonstrate it independently but it is exactly the same path and therefore is really unnecessary to split them.
 *)

Theorem exercise_3_ii : forall (U : Type) (A B : Ensemble U),
  Intersection U A B = Intersection U B A.
Proof.
  intros U A B.
  apply Extensionality_Ensembles.
  unfold Same_set. split;
  unfold Included;
  intros u H;
  destruct H;
  constructor;
  try apply H0;
  apply H.
Qed.


Theorem exercise_3_iii : forall (U : Type) (A : Ensemble U),
  Union U A A = A.
Proof.
  intros U A. apply Extensionality_Ensembles. unfold Same_set. split.
  * unfold Included. intros u Hu. destruct Hu; apply H.
  * unfold Included. intros u Ha. apply Union_introl. apply Ha.
Qed.


Theorem exercise_3_iv : forall (U : Type) (A : Ensemble U),
  Intersection U A A = A.
Proof.
  intros U A. apply Extensionality_Ensembles. unfold Same_set. split.
  * unfold Included. intros u Ha. destruct Ha. apply H.
  * unfold Included. intros u Ha. constructor; apply Ha.
Qed.


Theorem exercise_3_vi : forall (U : Type) (A B C : Ensemble U),
  Intersection U A (Intersection U B C) = Intersection U (Intersection U A B) C.
Proof.
  intros U A B C. apply Extensionality_Ensembles. unfold Same_set. split.
  * unfold Included. intros u H. destruct H. destruct H0. constructor. constructor.
    *** apply H.
    *** apply H0.
    *** apply H1.
  * unfold Included. intros u H. destruct H. destruct H. constructor. apply H. constructor. apply H1. apply H0.
Qed.

Theorem exercise_3_viii : forall (U : Type) (A B C : Ensemble U),
  Union U A (Intersection U B C) = Intersection U (Union U A B) (Union U A C).
Proof.
  intros U A B C. apply Extensionality_Ensembles. unfold Same_set. split.
  * unfold Included. intros u H. destruct H.
    ** constructor.
       *** apply Union_introl. apply H.
       *** apply Union_introl. apply H.
    ** destruct H. constructor.
       *** apply Union_intror. apply H.
       *** apply Union_intror. apply H0.
  * unfold Included. intros u H. destruct (classic (In U A u)).
    ** constructor.
       *** apply H0.
    ** apply Union_intror. destruct H. destruct H; destruct H1.
       *** apply H0 in H. destruct H.
       *** apply H0 in H. destruct H.
       *** apply H0 in H1. destruct H1.
       *** constructor.
           **** apply H.
           **** apply H1.
Qed.
