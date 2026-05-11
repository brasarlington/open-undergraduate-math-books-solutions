From Stdlib Require Import Sets.Ensembles.

Definition prod {T1 T2 : Type }
(X : Ensemble T1)
(Y : Ensemble T2) : Ensemble (T1 * T2) :=
  fun p => In T1 X (fst p) /\ In T2 Y (snd p).

Theorem exercise_3_1 : forall (X Y : Type)
  (A : Ensemble X)
  (B C : Ensemble Y),
  prod A (Setminus Y B C) = Setminus (X * Y) (prod A B) (prod A C).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, prod, In. split.
  * intros [u v] H. simpl in *. destruct H. destruct H0. split.
    ** unfold In in *. simpl. split. apply H. apply H0.
    ** intros Hv. unfold In in *. simpl in Hv. destruct Hv. apply H1 in H3. apply H3.
  * intros [u v] H. destruct H. unfold In in *. simpl in *. destruct H. split.
    ** apply H.
    ** split. apply H1. intros HC. unfold In in *. assert (Haux: A u /\ C v). { split. apply H. apply HC. } apply H0 in Haux. apply Haux.
Qed.
