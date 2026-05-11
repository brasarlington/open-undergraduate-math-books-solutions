From Stdlib Require Import Sets.Ensembles.

Definition prod {T1 T2 : Type }
(X : Ensemble T1)
(Y : Ensemble T2) : Ensemble (T1 * T2) :=
  fun p => In T1 X (fst p) /\ In T2 Y (snd p).

Theorem exercise_2_1 : forall (X Y : Type)
  (A : Ensemble X)
  (B C : Ensemble Y),
  prod A (Union Y B C) = Union (X * Y) (prod A B) (prod A C).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, prod, In. split.
  * intros [x y] [HA HBC]. simpl in *. inversion HBC.
    ** apply Union_introl. unfold In. split. apply HA. apply H.
    ** apply Union_intror. unfold In. split. apply HA. apply H.
  * intros [x y] H; destruct H; destruct x0; unfold In in *; simpl in *; destruct H.
    ** apply Union_introl with (C := C) in H0.
       unfold In in *. split. apply H. apply H0.
    ** apply Union_intror with (B := B) in H0.
       unfold In in *. split. apply H. apply H0.
Qed.
