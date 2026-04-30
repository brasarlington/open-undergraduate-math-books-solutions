From Stdlib Require Import Sets.Ensembles.

Theorem exercise_3_1 : forall (U : Type) (A B : Ensemble U),
  Included U A B <-> Intersection U A B = A.
Proof.
