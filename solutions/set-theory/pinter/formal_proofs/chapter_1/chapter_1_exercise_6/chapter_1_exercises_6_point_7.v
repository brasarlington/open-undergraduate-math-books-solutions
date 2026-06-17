From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Logic.Classical_Pred_Type.
From OUMBS Require Import Definitions.
From OUMBS Require Import Graphs.

Theorem exercise_7 : forall {I J U : Type}  (A : Indexed_Family I U) (B : Indexed_Family J U),
  (forall (i : I), exists (j : J), Included U (Limit B j) (Limit A i)) ->
  Included U (General_Intersection B) (General_Intersection A).
Proof.
  unfold Included, General_Intersection, Limit, In. simpl.
  intros. specialize H with i. destruct H.
  specialize H0 with x0. apply H in H0. apply H0.
Qed.
