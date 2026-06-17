From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Logic.Classical_Pred_Type.
From OUMBS Require Import Definitions.
From OUMBS Require Import Graphs.

Theorem exercise_1_43 {I U V : Type} (G : Indexed_Family I (U*V)) :
  ran (General_Union G) = General_Union (Indexed_Range G).
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, dom, ran, Restriction, In, General_Union in *. split.
  - intros. destruct H. destruct H. exists x1. simpl. unfold Indexed_Range, In. exists x0. simpl. apply H.
  - intros. destruct H. unfold Indexed_Range, In in *. simpl in *. destruct H. exists x1. exists x0. apply H.
Qed.
