From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Logic.Classical_Pred_Type.
From OUMBS Require Import Definitions.

Theorem exercise_5_a : forall {I U : Type} (A B : Indexed_Family I U),
  (forall i : I, Included U (Limit A i) (Limit B i)) ->
  Included U (General_Union A) (General_Union B).
Proof.
  unfold Included, General_Union, Limit, In.
  simpl. intros. destruct H0. apply H in H0. exists x0. apply H0.
Qed.

Theorem exercise_5_b : forall {I U : Type} (A B : Indexed_Family I U),
  (forall i : I, Included U (Limit A i) (Limit B i)) ->
  Included U (General_Intersection A) (General_Intersection B).
Proof.
  unfold Included, General_Intersection, Limit, In.
  simpl. intros. apply H. apply H0.
Qed.
