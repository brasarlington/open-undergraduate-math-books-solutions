From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.

Theorem exercise_4_ii : forall (U : Type) (A : Ensemble U),
  Intersection U A (Empty_set U) = (Empty_set U).
Proof.
  intros U A.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros u H. destruct H. apply H0.
  * intros u H. destruct H.
Qed.


Theorem exercise_4_iii : forall (U : Type) (A : Ensemble U),
  Union U A (Full_set U) = Full_set U.
Proof.
  intros U A.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros u H.
    apply Full_intro.
  * intros u H. apply Union_intror. apply H.
Qed.

Theorem exercise_4_iv : forall (U : Type) (A : Ensemble U),
  Intersection U A (Full_set U) = A.
Proof.
  intros U A.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros u H. destruct H. apply H.
  * intros u H. split.
    ** apply H.
    ** apply Full_intro.
Qed.

Theorem exercise_4_v : forall (U : Type),
  Complement U (Full_set U) = Empty_set U.
Proof.
  intros U.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros u H. destruct H. apply Full_intro.
  * intros u H. destruct H.
Qed.

Lemma Complement_Complement_Eq_Set : forall (U : Type) (A : Ensemble U),
  Complement U (Complement U A) = A.
Proof.
  intros U A.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Complement, In. split.
  * intros u H. apply NNPP in H. apply H.
  * unfold not. intros u H H1. apply H1 in H. destruct H.
Qed.

Theorem exercise_4_vi : forall (U : Type),
  Complement U (Empty_set U) = Full_set U.
Proof.
  intros U.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros u H. apply Full_intro.
  * intros u H. rewrite <- exercise_4_v.
    rewrite Complement_Complement_Eq_Set. apply H.
Qed.

Theorem exercise_4_vii : forall (U : Type) (A : Ensemble U),
  Union U A (Complement U A) = Full_set U.
Proof.
  intros U A.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros u H. apply Full_intro.
  * intros u H. destruct (classic (In U A u)).
    ** apply Union_introl. apply H0.
    ** apply Union_intror. apply H0.
Qed.

Theorem exercise_4_viii : forall (U : Type) (A : Ensemble U),
  Intersection U A (Complement U A) = Empty_set U.
Proof.
  intros U A.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros u H. inversion H. unfold Complement, In in *. apply H1 in H0. destruct H0.
  * intros u H. destruct H.
Qed.
