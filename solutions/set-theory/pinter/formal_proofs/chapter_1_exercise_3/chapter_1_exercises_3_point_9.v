From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.
From OUMBS Require Import chapter_1_exercises_3_point_8.

Definition Setplus {U: Type} (A B : Ensemble U) : Ensemble U
  := Union U (Setminus U A B) (Setminus U B A).

Theorem exercise_9_a : forall (U : Type) (A B : Ensemble U),
  Union U A B = Empty_set U -> A = Empty_set U /\ B = Empty_set U.
Proof.
  intros. split;
  apply Extensionality_Ensembles;
  unfold Same_set, Included; split.
  * intros. apply Union_introl with (C := B) in H0. rewrite H in H0. destruct H0.
  * intros. destruct H0.
  * intros. apply Union_intror with (B := A) in H0. rewrite H in H0. destruct H0.
  * intros. destruct H0.
Qed.

Theorem exercise_9_b : forall (U : Type) (A B : Ensemble U),
  Intersection U A (Complement U B) = Empty_set U <-> Included U A B.
Proof.
  intros. split.
  * intros. unfold Included. intros. destruct (classic (In U B x)).
    ** apply H1.
    ** assert (Haux : In U (Intersection U A (Complement U B)) x). {
       split. apply H0. apply H1.
    }
    rewrite H in Haux. destruct Haux.
  * intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
    ** intros. destruct H0. unfold Included in H. apply H in H0. apply H1 in H0. destruct H0.
    ** intros. destruct H0.
Qed.

Theorem exercise_9_c : forall (U : Type) (A B : Ensemble U),
  Setplus A B = Empty_set U <-> A = B.
Proof.
  intros. split; intros;
  apply Extensionality_Ensembles;
  unfold Same_set, Included; split.
  * intros. destruct (classic (In U B x)).
    ** apply H1.
    ** assert (Haux: In U (Setminus U A B) x). {
       split. apply H0. apply H1.
    }
    apply Union_introl with (C := Setminus U B A) in Haux. unfold Setplus in H.
    rewrite H in Haux. destruct Haux.
  * intros. destruct (classic (In U A x)).
    ** apply H1.
    ** assert (Haux: In U (Setminus U B A) x). {
       split. apply H0. apply H1.
    }
    apply Union_intror with (B := Setminus U A B) in Haux. unfold Setplus in H.
    rewrite H in Haux. destruct Haux.
  * intros. rewrite H in H0. rewrite exercise_8_d in H0. destruct H0.
  * intros. destruct H0.
Qed.
