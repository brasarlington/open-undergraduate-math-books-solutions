From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.

Lemma theorem_1_25_vii : forall (U : Type) (A B C : Ensemble U),
  Intersection U A (Union U B C) = Union U (Intersection U A B) (Intersection U A C).
Proof.
  intros U A B C.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros u H. destruct H. destruct H0.
    ** apply Union_introl. constructor.
       *** apply H.
       *** apply H0.
    ** apply Union_intror. constructor.
       *** apply H.
       *** apply H0.
  * intros u H. destruct H.
    ** destruct H. constructor.
       *** apply H.
       *** apply Union_introl. apply H0.
    ** destruct H. constructor.
       *** apply H.
       *** apply Union_intror. apply H0.
Qed.

Lemma union_empty_unchange : forall (U : Type) (A: Ensemble U),
  Union U A (Empty_set U) = A.
Proof.
  intros U A.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros u H. destruct H.
    ** apply H.
    ** destruct H.
  * intros u H. apply Union_introl. apply H.
Qed.


Theorem exercise_6_a : forall (U : Type) (A B C: Ensemble U),
  Intersection U A C = Empty_set U ->
  Intersection U A (Union U B C) = Intersection U A B.
Proof.
  intros U A B C H.
  rewrite theorem_1_25_vii.
  rewrite H. apply union_empty_unchange.
Qed.


Theorem exercise_6_b : forall (U : Type) (A B: Ensemble U),
  Intersection U A B = Empty_set U ->
  Setminus U A B = A.
Proof.
  intros U A B H.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros u H1. destruct H1. apply H0.
  * intros u H1. split.
    ** apply H1.
    ** intros HinB. assert (Haux: In U (Intersection U A B) u). {
       constructor.
       apply H1.
       apply HinB.
    } rewrite H in Haux. destruct Haux.
Qed.

Theorem exercise_6_c : forall (U : Type) (A B C : Ensemble U),
  Intersection U A B = Empty_set U ->
  Union U A B = C ->
  A = Setminus U C B.
Proof.
  intros U A B C H1 H2.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros u H. split.
    ** apply Union_introl with (C := B) in H. rewrite H2 in H. apply H.
    ** intros Hb. assert (Haux: In U (Intersection U A B) u). {
       constructor.
       apply H.
       apply Hb.
    } rewrite H1 in Haux. destruct Haux.
  * intros u [H3 H4]. rewrite <- H2 in H3. destruct H3.
    ** apply H.
    ** apply H4 in H. destruct H.
Qed.
