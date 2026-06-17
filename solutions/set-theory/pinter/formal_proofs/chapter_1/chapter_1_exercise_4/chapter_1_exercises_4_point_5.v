From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.

Definition prod {T1 T2 : Type }
(X : Ensemble T1)
(Y : Ensemble T2) : Ensemble (T1 * T2) :=
  fun p => In T1 X (fst p) /\ In T2 Y (snd p).

Theorem exercise_5_a : forall (X : Type)
  (A B C: Ensemble X),
  Intersection (X * X) (prod A A) (prod B C) = prod (Intersection X A B) (Intersection X A C).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, prod, In. split.
  * intros _ [[x1 x2] [H1 H4] [H3 H2]]. split; split; unfold In; simpl in *.
    apply H1. apply H3. apply H4. apply H2.
  * simpl. intros [x1a x2a] H. destruct H. simpl in *. inversion H. inversion H0.
    split; split; unfold In in *; simpl in *.
    apply H1. apply H4. apply H2. apply H5.
Qed.

Theorem exercise_5_b : forall (X : Type)
  (A B C: Ensemble X),
  Setminus (X * X) (prod A B) (prod C C) = Union (X * X) (prod (Setminus X A C) B) (prod A (Setminus X B C)).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, prod, In. split.
  * intros [u v] [H1 H2]. unfold In in *. simpl in *.  destruct (classic (C v)) as [HCv | HnotCv].
    ** apply Union_introl. unfold In in *. simpl in *. split.
       *** split.
           **** apply H1.
           **** intros HCu. assert (Haux: C u /\ C v). { split. apply HCu. apply HCv. } apply H2 in Haux. apply Haux.
       *** apply H1.
    ** apply Union_intror. unfold In in *. simpl in *. split.
       *** apply H1.
       *** split.
           **** apply H1.
           **** intros HCv. contradiction.
  * intros _ [[x1 x2] H |[x1 x2] H].
    ** split; unfold In in *; simpl in *.
       *** destruct H as [[Ha HnC] HB]. split. apply Ha. apply HB.
       *** destruct H as [[Ha HnC] HB]. intros [HC _]. contradiction.
    ** split; unfold In in *; simpl in *.
       *** destruct H as [Ha [HB HnC]]. split. apply Ha. apply HB.
       *** destruct H as [Ha [HB HnC]].  intros [_ HC]. contradiction.
Qed.

Theorem exercise_5_c : forall (X : Type)
  (A B C: Ensemble X),
  Setminus (X * X) (prod A A) (prod B C) = Union (X * X) (prod (Setminus X A B) A) (prod A (Setminus X A C)).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, prod, In. split.
  * intros [x1 x2] [H1 H2]. unfold In in *. simpl in *.  destruct (classic (C x2)).
    ** apply Union_introl. unfold In in *. simpl in *. split.
       *** split. apply H1. intros HB. assert (Haux: B x1 /\ C x2). { split. apply HB. apply H.  } contradiction.
       *** apply H1.
    ** apply Union_intror. unfold In in *. simpl in *. split.
       *** apply H1.
       *** split.
           **** apply H1.
           **** intros HC. contradiction.
  * intros [u v] [[x1 x2] H |[x1 x2] H].
    ** split.
       *** destruct H as [[H1 H2] H3]. unfold In in *. simpl in *. split. apply H1. apply H3.
       *** destruct H as [[H1 H2] H3]. unfold In in *. simpl in *. intros [HB _]. contradiction.
    ** split.
       *** destruct H as [H1 [H2 H3]]. unfold In in *. simpl in *. split. apply H1. apply H2.
       *** destruct H as [H1 [H2 H3]]. unfold In in *. simpl in *. intros [_ HC]. contradiction.
Qed.
