From Stdlib Require Import Sets.Ensembles.

Definition prod {T1 T2 : Type }
(X : Ensemble T1)
(Y : Ensemble T2) : Ensemble (T1 * T2) :=
  fun p => In T1 X (fst p) /\ In T2 Y (snd p).

Theorem exercise_4_1 : forall (X Y : Type)
  (A C: Ensemble X)
  (B D: Ensemble Y),
  Intersection (X * Y) (prod A B) (prod C D)
  = Intersection (X * Y) (prod A D) (prod C B).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, prod, In. split;
  intros [u v] [[x y] [H1 H4] [H3 H2]]; 
  simpl in *; split; split; simpl;
  apply H1 || apply H2 || apply H3 || apply H4.
Qed.
