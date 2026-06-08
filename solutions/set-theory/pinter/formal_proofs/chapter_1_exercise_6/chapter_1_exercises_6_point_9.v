From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Logic.Classical_Pred_Type.
From OUMBS Require Import Definitions.
From OUMBS Require Import Graphs.

Theorem exercise_9  : forall (I J U : Type) (A : Ensemble U) (B : Indexed_Family I U) (C : Indexed_Family J U),
  Covering A B ->
  Covering A C ->
  Covering A (Product_Family_Intersection B C).
Proof.
  intros.
  unfold Covering, Product_Family_Intersection, General_Union, Included, In in *.
  intros. apply H in H1 as H1A. apply H0 in H1 as H0A. destruct H1A. destruct H0A. exists (x0, x1). split. apply H2. apply H3.
Qed.
