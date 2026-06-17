From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.

Definition Setplus {U: Type} (A B : Ensemble U) : Ensemble U
  := Union U (Setminus U A B) (Setminus U B A).

Lemma Union_conm : forall (U: Type) (A B : Ensemble U),
  Union U A B = Union U B A.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros u H. destruct (classic (In U A u)).
    ** apply Union_intror. apply H0.
    ** destruct (classic (In U B u)).
       *** apply Union_introl. apply H1.
       *** inversion H.
           **** apply H0 in H2. destruct H2.
           **** apply H1 in H2. destruct H2.
  * intros u H. destruct (classic (In U A u)).
    ** apply Union_introl. apply H0.
    ** destruct (classic (In U B u)).
       *** apply Union_intror. apply H1.
       *** inversion H.
           **** apply H1 in H2. destruct H2.
           **** apply H0 in H2. destruct H2.
Qed.


Theorem exercise_8_a : forall (U : Type) (A B : Ensemble U),
  Setplus A B = Setplus B A.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split;
  intros u H;
  unfold Setplus in *;
  rewrite Union_conm in H;
  apply H.
Qed.

Theorem exercise_8_b : forall (U : Type) (A B C : Ensemble U),
  Setplus A (Setplus B C) = Setplus (Setplus A B) C.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Setplus. split.
  * intros u H. destruct H.
    ** destruct H. destruct (classic (In U C x)).
       *** apply Union_intror. split.
           **** apply H1.
           **** intros HUAB. destruct HUAB.
                ***** destruct H2. assert (Haux: In U (Setminus U C B) x). {
                      split. apply H1. apply H3.
                }
                apply Union_intror with (B := (Setminus U B C)) in Haux. apply H0 in Haux. apply Haux.
                ***** destruct H2. apply H3 in H. apply H.
       *** apply Union_introl. split.
           **** destruct (classic (In U B x)).
                ***** assert (Haux: In U (Setminus U B C) x). {
                      split. apply H2. apply H1.
                }
                apply Union_introl with (C := (Setminus U C B)) in Haux. apply H0 in Haux. destruct Haux.
                ***** apply Union_introl. split. apply H. apply H2.
           **** apply H1.
    ** destruct H. destruct H.
       *** destruct H. apply Union_introl. split.
           **** apply Union_intror. split.
                ***** apply H.
                ***** apply H0.
           ****  apply H1.
       *** destruct H. apply Union_intror. split.
           **** apply H.
           **** intros HSAB. destruct HSAB.
                ***** destruct H2. apply H0 in H2. apply H2.
                ***** destruct H2. apply H1 in H2. apply H2.
  * intros u H. destruct H.
    ** destruct H. destruct H.
       *** destruct H. apply Union_introl. split.
           **** apply H.
           **** intros HBC. destruct HBC.
                ***** destruct H2. apply H1 in H2. apply H2.
                ***** destruct H2. apply H0 in H2. apply H2.
       *** destruct H. apply Union_intror. split.
           **** apply Union_introl. split. apply H. apply H0.
           **** apply H1.
    ** destruct H. destruct (classic (In U A x)).
       *** apply Union_introl. split.
           **** apply H1.
           **** intros HBC. destruct HBC.
                ***** destruct H2. apply H3 in H. apply H.
                ***** destruct H2. assert (Haux: In U (Setminus U A B) x). {
                      split. apply H1. apply H3.
                }
                apply Union_introl with (C := (Setminus U B A)) in Haux. apply H0 in Haux. apply Haux.
       *** apply Union_intror. split.
           **** apply Union_intror. split.
                ***** apply H.
                ***** intros HB. assert (Haux: In U (Setminus U B A) x). {
                      split. apply HB. apply H1.
                }
                apply Union_intror with (B := (Setminus U A B)) in Haux. apply H0 in Haux. apply Haux.
           **** apply H1.
Qed.

Theorem exercise_8_c : forall (U : Type) (A B C: Ensemble U),
  Intersection U A (Setplus B C) = Setplus (Intersection U A B) (Intersection U A C).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Setplus. split.
  * intros u H. destruct H. destruct H0.
    ** destruct H0. apply Union_introl. split.
       *** split. apply H. apply H0.
       *** intros HAC. destruct HAC. apply H1 in H3. apply H3.
    ** destruct H0. apply Union_intror. split.
       *** split. apply H. apply H0.
       *** intros HAB. destruct HAB. apply H1 in H3. apply H3.
  * intros u H. destruct H.
    ** destruct H. destruct H. split.
       *** apply H.
       *** apply Union_introl. split.
           **** apply H1.
           **** intros HC. assert (Haux: In U (Intersection U A C) x). {
                split. apply H. apply HC.
           }
           apply H0 in Haux. apply Haux.
    ** destruct H. destruct H. split.
       *** apply H.
       *** apply Union_intror. split.
           **** apply H1.
           **** intros HB. assert (Haux: In U (Intersection U A B) x). {
                split. apply H. apply HB.
           }
           apply H0 in Haux. apply Haux.
Qed.

Theorem exercise_8_d : forall (U : Type) (A : Ensemble U),
  Setplus A A = Empty_set U.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Setplus. split.
  * intros u H. destruct H; destruct H; apply H0 in H; destruct H.
  * intros u H. destruct H.
Qed.

Theorem exercise_8_e : forall (U : Type) (A : Ensemble U),
  Setplus A (Empty_set U) = A.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Setplus. split.
  * intros u H. destruct H.
    ** destruct H. apply H.
    ** destruct H. destruct H.
  * intros u H. apply Union_introl. split.
    apply H. intros HES. destruct HES.
Qed.
