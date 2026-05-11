From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.

Definition prod {T1 T2 : Type }
(X : Ensemble T1)
(Y : Ensemble T2) : Ensemble (T1 * T2) :=
  fun p => In T1 X (fst p) /\ In T2 Y (snd p).

Theorem exercise_9_a : forall
  (X Y : Type)
  (A : Ensemble X)
  (B C : Ensemble Y),
  Disjoint (X * Y) (prod A B) (prod (Complement X A) C).
Proof.
  constructor. intros _ [[x y] H1  H2]. unfold In, prod, Complement, In in *. simpl in *. destruct H1, H2. contradiction.
Qed.

Theorem exercise_9_b : forall
  (X Y : Type)
  (B C : Ensemble X)
  (A : Ensemble Y),
  Disjoint (X * Y) (prod B A) (prod C (Complement Y A)).
Proof.
  constructor. intros _ [[x y] H1  H2]. unfold In, prod, Complement, In in *. simpl in *. destruct H1, H2. contradiction.
Qed.
