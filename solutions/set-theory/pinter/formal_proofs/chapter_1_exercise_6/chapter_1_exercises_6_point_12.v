From Stdlib Require Import Sets.Ensembles.

Definition General_Union
  { U : Type } (A : Ensemble (Ensemble U)) : Ensemble U
  := fun (p : U) => exists (B : Ensemble U), In (Ensemble U) A B /\ In U B p.

Definition General_Intersection
  { U : Type } (A : Ensemble (Ensemble U)) : Ensemble U
  := fun (p : U) => forall (B : Ensemble U), In (Ensemble U) A B -> In U B p.

Definition Indexed_Family (U: Type) : Type := Ensemble (Ensemble U).

Theorem exercise_12_a : forall {U : Type}
  (A : Ensemble U) (B : Indexed_Family U),
  In (Ensemble U) B A ->
  Included U A (General_Union B) /\ Included U (General_Intersection B) A.
Proof.
  intros.
  split.
  * unfold Included, In, General_Union in *. intros. exists A. split.
    ** apply H.
    ** apply H0.
  * unfold Included, In, General_Intersection in *. intros. apply (H0 A) in H.
    apply H.
Qed.

Theorem exercise_12_b : forall {U : Type}
  (A B : Indexed_Family U),
  Included (Ensemble U) A B -> Included U (General_Union A) (General_Union B).
Proof.
  intros.
  unfold Included, General_Union, In in *. intros.
  destruct H0. destruct H0. exists x0. split.
    * apply H. apply H0.
    * apply H1.
Qed.

Theorem exercise_12_c : forall {U : Type}
  (A : Indexed_Family U),
  In (Ensemble U) A (Empty_set U) ->
  General_Intersection A = Empty_set U.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, General_Intersection, In in *. split.
  * intros. apply (H0 (Empty_set U)) in H. destruct H.
  * intros. destruct H0.
Qed.
