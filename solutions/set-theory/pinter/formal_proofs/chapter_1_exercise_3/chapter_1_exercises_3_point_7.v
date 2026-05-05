From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.

Theorem exercise_7_a : forall (U : Type) (A B C : Ensemble U),
  Intersection U A (Setminus U B C) = Setminus U (Intersection U A B) C.
Proof.
  intros U A B C.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros u H. destruct H. destruct H0. split.
    ** constructor.
       *** apply H.
       *** apply H0.
    ** apply H1.
  * intros u H. destruct H. destruct H. constructor.
    ** apply H.
    ** constructor.
       *** apply H1.
       *** apply H0.
Qed.

Theorem exercise_7_b : forall (U : Type) (A B C: Ensemble U),
  Setminus U (Union U A B) C = Union U (Setminus U A C) (Setminus U B C).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros u H. destruct H. destruct H.
    ** apply Union_introl. constructor.
       *** apply H.
       *** apply H0.
    ** apply Union_intror. constructor.
       *** apply H.
       *** apply H0.
  * intros u H. destruct H. destruct H.
    ** constructor.
       *** apply Union_introl. apply H.
       *** apply H0.
    ** destruct H. constructor.
       *** apply Union_intror. apply H.
       *** apply H0.
Qed.

Theorem exercise_7_c : forall (U : Type) (A B C: Ensemble U),
  Setminus U A (Union U B C) = Intersection U (Setminus U A B) (Setminus U A C).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros. destruct H. split.
    ** split.
       *** apply H.
       *** intros HB. apply Union_introl with (C := C) in HB. apply H0 in HB. apply HB.
    ** split.
       *** apply H.
       *** intros HC. apply Union_intror with (B := B) in HC. apply H0 in HC. apply HC.
  * intros. destruct H. destruct H. destruct H0. split.
    ** apply H.
    ** intros HU. destruct HU.
       *** apply H1 in H3. apply H3.
       *** apply H2 in H3. apply H3.
Qed.

Theorem exercise_7_d : forall (U : Type) (A B C: Ensemble U),
  Setminus U A (Intersection U B C) = Union U (Setminus U A B) (Setminus U A C).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros u H. destruct (classic (In U B u)).
    ** destruct H. apply Union_intror. split.
       *** apply H.
       *** intros HC. assert (Haux: In U (Intersection U B C) u). {
           apply Intersection_intro.
           apply H0.
           apply HC.
       }
       apply H1 in Haux. apply Haux.
    ** destruct H. apply Union_introl. split.
       *** apply H.
       *** apply H0.
  * intros u H. split.
    ** destruct H. destruct H.
       *** apply H.
       *** destruct H. apply H.
    ** destruct H. destruct H.
       *** intros HIBC. destruct HIBC. apply H0 in H1. apply H1.
       *** intros HIBC. destruct H. destruct HIBC. apply H0 in H2. apply H2.
Qed.
