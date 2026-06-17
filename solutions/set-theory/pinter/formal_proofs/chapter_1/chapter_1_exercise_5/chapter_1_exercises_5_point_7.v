From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.
From OUMBS Require Import Graphs.

Theorem exercise_7_a : forall (U : Type) (A B : Ensemble U),
  Inverse (prod A B) = prod B A.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, prod, Inverse, In in *. split.
  * intros [u1 u2] [HA HB]. simpl in *. split. apply HB. apply HA.
  * intros [u1 u2] [HB HA]. simpl in *. split. apply HA. apply HB.
Qed.

Lemma aux_lemma : forall (U : Type) (A : Ensemble U),
  ~ (exists x, In U A x) <-> A = Empty_set U.
Proof.
  intros. split.
  * intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In in *. split.
    ** intros x HA. assert (exists x, A x) by (exists x; apply HA). contradiction.
    ** intros x HE. destruct HE.
  * intros H [x HE]. rewrite H in HE. destruct HE.
Qed.


Lemma non_empty_intersection_implies_existence_of_mutual_element :
  forall (U : Type) (A : Ensemble U),
  A <> Empty_set U <-> exists x, A x.
Proof.
  intros. split.
  * intros. destruct (classic (exists x, In U A x)).
    ** apply H0.
    ** apply aux_lemma in H0. contradiction.
  * intros [x HE] H. rewrite H in HE. destruct HE.
Qed.

Theorem exercise_7_b : forall (U : Type) (A B : Ensemble U),
  Intersection U A B <> Empty_set U ->
  Compose (prod A B) (prod A B) = prod A B.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, prod, Compose, In in *. split.
  * intros [u1 u2] [u3 [[HA1 HB1] [HA2 HB2]]]. simpl in *. split.
    apply HA1. apply HB2.
  * intros [u1 u2] [HA1 HB1]. simpl in *.
    apply non_empty_intersection_implies_existence_of_mutual_element in H. destruct H. destruct H. exists x. split; split.
    ** apply HA1.
    ** apply H0.
    ** apply H.
    ** apply HB1.
Qed.

Theorem exercise_7_c : forall (U : Type) (A B : Ensemble U),
  Disjoint U A B ->
  Compose (prod A B) (prod A B) = Empty_set (U * U).
Proof.
  intros.
  apply Extensionality_Ensembles.
  destruct H.
  unfold Same_set, Included, In, prod, Compose, In in *. split.
  * intros [u1 u2] [u3 [[HA1 HB1] [HA2 HB2]]]. simpl in *.
    assert (contra: Intersection U A B u3) by (split; apply HA2 || apply HB1).
    apply H in contra. destruct contra.
  * intros x H0. destruct H0.
Qed.

Theorem exercise_7_d : forall (U : Type) (A B C: Ensemble U),
  B <> Empty_set U ->
  Compose (prod B C) (prod A B) = prod A C.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, prod, Compose, In in *. split.
  * intros [u1 u2] [u3 [[HA1 HB1] [HA2 HB2]]]. simpl in *. split. apply HA1. apply HB2.
  * intros [u1 u2] [HA HC]. simpl in *. apply non_empty_intersection_implies_existence_of_mutual_element in H as [u HB]. exists u. split; split;
    apply HA || apply HB || apply HC.
Qed.
