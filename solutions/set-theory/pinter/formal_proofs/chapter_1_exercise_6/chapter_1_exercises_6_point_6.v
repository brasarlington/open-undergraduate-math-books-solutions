From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Logic.Classical_Pred_Type.
From OUMBS Require Import Definitions.
From OUMBS Require Import Graphs.

Theorem exercise_6_a : forall {I J U V : Type} (A : Indexed_Family I U) (B : Indexed_Family J V),
  inhabited I ->
  inhabited J ->
  prod (General_Intersection A) (General_Intersection B)
  = General_Intersection (Product_Family_Complete A B).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, prod, General_Intersection, Product_Family_Complete, In in *. split.
  - intros. destruct i. destruct x. simpl in *. destruct H. split. apply H1. apply H1.
  - intros. destruct x. simpl in *. split.
    ** intros. destruct H0. apply (H1 (i, X)).
    ** intros. destruct H. apply (H1 (X, i)).
Qed.

Theorem exercise_6_b : forall {I J U V : Type} (A : Indexed_Family I U) (B : Indexed_Family J V),
  prod (General_Union A) (General_Union B)
  = General_Union (Product_Family_Complete A B).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, prod, General_Union, Product_Family_Complete, In in *. split.
  * intros. simpl in *. destruct H. destruct H. destruct H0. exists (x0, x1). destruct x. simpl in *. split. apply H. apply H0.
  * intros. destruct H. destruct x0. destruct x. simpl in *. split.
    ** exists i. apply H.
    ** exists j. apply H.
Qed.
