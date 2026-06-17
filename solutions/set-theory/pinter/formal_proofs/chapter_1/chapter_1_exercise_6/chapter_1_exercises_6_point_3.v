From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.
From OUMBS Require Import Definitions.
From Stdlib Require Import Logic.Classical_Pred_Type.

Theorem exercise_1_42_ii :
  forall (I J U : Type) (A : Indexed_Family I U) (B : Indexed_Family J U),
    Union U (General_Intersection A) (General_Intersection B) =
    General_Intersection (Product_Family A B).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, General_Intersection, Product_Family, In in *. split.
  - intros. simpl in *. destruct i. destruct H.
    ** left. apply H.
    ** right. apply H.
  - intros. destruct (classic (forall i : I, A (i, x))).
    ** apply Union_introl. unfold In. apply H0.
    ** destruct (classic (forall i : J, B (i, x))).
      *** apply Union_intror. unfold In. apply H1.
      *** assert (contra: ~(forall i : I * J, let (i0, j) := i in A (i0, x) \/ B (j, x))). {
      apply not_all_ex_not in H0, H1. apply ex_not_not_all. destruct H0. destruct H1. exists (x0, x1).
      apply and_not_or. split. apply H0. apply H1.
      } contradiction.
Qed.
