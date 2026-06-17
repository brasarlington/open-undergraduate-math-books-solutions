From OUMBS Require Import Definitions.

Theorem exercise_2 : forall (A B : Class),
  proper_class A ->
  subclass A B ->
  proper_class B.
Proof.
  unfold proper_class.
  intros A B HnSA HAIB HB. apply HnSA.
  apply (A3_subclass_set B A). apply HB. apply HAIB.
Qed.
