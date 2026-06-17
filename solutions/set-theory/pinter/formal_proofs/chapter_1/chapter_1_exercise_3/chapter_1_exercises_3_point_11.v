From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.

Theorem exercise_11 : forall (U : Type) (A B C : Ensemble U),
  Included U A B -> C = Setminus U B A -> A = Setminus U B C.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included. split.
  * intros. split.
    ** apply H in H1. apply H1. 
    ** intros HC. rewrite H0 in HC. destruct HC. contradiction.
  * intros. destruct H1. destruct (classic (In U A x)). apply H3.
    ** assert (Haux: In U (Setminus U B A) x). {
       split. apply H1. apply H3.
    } rewrite <- H0 in Haux. contradiction.
Qed.
