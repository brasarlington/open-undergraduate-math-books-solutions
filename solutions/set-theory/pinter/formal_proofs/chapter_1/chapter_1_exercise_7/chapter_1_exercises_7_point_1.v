From OUMBS Require Import Definitions.

Theorem exercise_1_a : forall (A B : Class),
  is_set A ->
  is_set B -> 
  is_set (Diff A B).
Proof.
  intros.
  assert (Haux: subclass (Diff A B) A). {
    unfold subclass. intros. apply diff_def in H2.
      ** apply H2.
      ** apply H1.
  }
  apply A3_subclass_set in Haux.
    ** apply Haux.
    ** apply H.
Qed.

Theorem exercise_1_b : forall (A B : Class),
  is_set A ->
  is_set B -> 
  is_set (Plus A B).
Proof.
  intros.
  apply (A3_subclass_set (Union A B) (Plus A B)).
  * apply union_is_set. apply H. apply H0.
  * apply Plus_subclass_union.
Qed.
