From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.

Theorem exercise_11_a : forall (U : Type) (b : U) (A : Ensemble U),
  A = Singleton U b ->
  In U A b.
Proof.
  intros. rewrite H. apply In_singleton.
Qed.

Theorem exercise_11_b : forall (U : Type) (x y : U),
  x = y <-> Singleton U x = Singleton U y.
Proof.
  intros. split.
  * intros. rewrite H. reflexivity.
  * intros.
    apply exercise_11_a in H as Hx.
    unfold In in Hx.
    inversion Hx.
    reflexivity.
Qed.

Theorem exercise_11_c : forall (U : Type) (x : U) (A : Ensemble U),
  In U A x <-> Included U (Singleton U x) A.
Proof.
  intros.
  split.
  * intros. unfold Included. intros. inversion H0. rewrite <- H1.  apply H.
  * intros. unfold Included in *. 
    assert (Hx : In U (Singleton U x) x). { apply In_singleton. }
    apply H in Hx. exact Hx.
Qed.

Theorem exercise_11_d : forall (U : Type) (a b : U),
  a = b <-> Couple U a b = Singleton U a.
Proof.
  intros. split.
  * intros H.
    apply Extensionality_Ensembles. unfold Same_set, Included, In. split.
    ** intros x H0. inversion H0.
       *** apply In_singleton.
       *** rewrite H, H1. apply In_singleton.
    ** intros x H0. inversion H. inversion H0. rewrite <- H1. rewrite H2. apply Couple_l.
  * intros H.
    assert (In U (Couple U a b) b) as Hb.
    { apply Couple_r. }
    rewrite H in Hb.
    inversion Hb. reflexivity.
Qed.
