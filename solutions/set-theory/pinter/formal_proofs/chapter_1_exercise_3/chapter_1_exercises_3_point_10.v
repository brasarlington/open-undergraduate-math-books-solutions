From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.
From OUMBS Require Import chapter_1_exercises_3_point_8.

Theorem exercise_10_a : forall (U : Type) (A B C : Ensemble U),
  Union U A C = Union U B C <-> Included U (Setplus A B) C.
Proof.
  intros. split; intros;
  try apply Extensionality_Ensembles;
  unfold Same_set, Included, Setplus; try split.
  * intros. destruct H0.
    ** destruct H0. apply Union_introl with (C := C) in H0. rewrite H in H0. destruct H0. apply H1 in H0. destruct H0. apply H0.
    ** destruct H0. apply Union_introl with (C := C) in H0. rewrite <- H in H0. destruct H0. apply H1 in H0. destruct H0. apply H0.
  * intros. destruct H0.
    ** destruct (classic (In U B x)).
       *** apply Union_introl. apply H1.
       *** assert (Haux: In U (Setminus U A B) x). {
           split. apply H0. apply H1.
       } apply Union_introl with (C := Setminus U B A) in Haux. fold (Setplus A B) in Haux. apply H in Haux. apply Union_intror with (B := B) in Haux. apply Haux.
    ** apply Union_intror. apply H0.
  * intros. destruct H0.
    ** destruct (classic (In U A x)).
       *** apply Union_introl. apply H1.
       *** assert (Haux: In U (Setminus U B A) x). {
           split. apply H0. apply H1.
       } apply Union_intror with (B := Setminus U A B) in Haux. fold (Setplus A B) in Haux. apply H in Haux. apply Union_intror with (B := A) in Haux. apply Haux.
    ** apply Union_intror. apply H0.
Qed.

Theorem exercise_10_b : forall (U : Type) (A B C : Ensemble U),
  Setplus (Union U A C) (Union U B C) = Setminus U (Setplus A B) C.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros. destruct H.
    ** destruct H. destruct H.
       *** split.
           **** unfold Setplus. apply Union_introl. split.
                ***** apply H.
                ***** intros HB. apply Union_introl with (C := C) in HB. apply H0 in HB. destruct HB.
           **** intros HB. apply Union_intror with (B := B) in HB. apply H0 in HB. destruct HB.
       *** apply Union_intror with (B := B) in H. apply H0 in H. destruct H.
    ** destruct H. destruct H.
       *** split.
           **** apply Union_intror. split.
                ***** apply H.
                ***** intros HA. apply Union_introl with (C := C) in HA. apply H0 in HA. destruct HA.
           **** intros HC. apply Union_intror with (B := A) in HC. apply H0 in HC. destruct HC.
       *** apply Union_intror with (B := A) in H. apply H0 in H. destruct H.
  * intros. destruct H. destruct H.
    ** destruct H. apply Union_introl. split.
       *** apply Union_introl. apply H.
       *** intros HBC. destruct HBC.
           **** apply H1. apply H2.
           **** apply H0. apply H2.
    ** destruct H. apply Union_intror. split.
       *** apply Union_introl. apply H.
       *** intros HAC. destruct HAC.
           **** apply H1. apply H2.
           **** apply H0. apply H2.
Qed.

