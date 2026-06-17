From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Logic.Classical_Pred_Type.
From OUMBS Require Import Definitions.
From OUMBS Require Import Graphs.

Theorem exercise_11 :
  forall (I J U : Type) (A : Indexed_Family I U) (B : Indexed_Family J U),
    General_Intersection (Union_Family A B) =
    Intersection U (General_Intersection A) (General_Intersection B).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, General_Union, General_Intersection, Union_Family, In in *.
  split.
  - intros. split.
    ** unfold In. intros. apply H with (i := inl i).
    ** unfold In. intros. apply H with (i := inr i).
  - intros. destruct i.
    ** destruct H. apply (H i).
    ** destruct H. apply (H0 j).
Qed.
