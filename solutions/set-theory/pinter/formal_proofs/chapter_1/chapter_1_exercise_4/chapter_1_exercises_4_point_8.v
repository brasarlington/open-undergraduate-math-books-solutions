From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.

Definition prod {T1 T2 : Type }
(X : Ensemble T1)
(Y : Ensemble T2) : Ensemble (T1 * T2) :=
  fun p => In T1 X (fst p) /\ In T2 Y (snd p).

Lemma empty_is_empty : forall (U : Type) (C : Ensemble U), (exists x, In U C x) <-> C <> Empty_set U.
Proof.
  intros. split.
  - intros [x H]. intros HC. rewrite HC in H. destruct H.
  - intros Hne.
    apply NNPP. intro Hnex.
    apply Hne.
    apply Extensionality_Ensembles.
    split.
    + intros x Hx. destruct (Hnex (ex_intro (fun x => In U C x) x Hx)).
    + intros x Hx. destruct Hx.
Qed.

Theorem exercise_7_1 : forall (X : Type) (A B C D: Ensemble X),
  A <> Empty_set X ->
  B <> Empty_set X ->
  C <> Empty_set X ->
  D <> Empty_set X ->
  (prod A B = prod C D <-> A = C /\ B = D).
Proof.
  intros. split.
  + intros. split.
    ++ apply Extensionality_Ensembles. unfold Same_set, Included, In. split.
      +++ intros x1 Ha. apply empty_is_empty in H0 as [x2 H0].
      assert (Haux: In (X * X) (prod A B) (x1, x2)).
      { split. apply Ha. apply H0. }
      rewrite H3 in Haux. destruct Haux. apply H4.
      +++ intros x1 Ha. apply empty_is_empty in H2 as [x2 H2].
      assert (Haux: In (X * X) (prod C D) (x1, x2)).
      { split. apply Ha. apply H2. }
      rewrite <- H3 in Haux. destruct Haux. apply H4.
    ++ apply Extensionality_Ensembles. unfold Same_set, Included, In. split.
      +++ intros x2 Hb. apply empty_is_empty in H as [x1 H].
      assert (Haux: In (X * X) (prod A B) (x1, x2)).
      { split. apply H. apply Hb. }
      rewrite H3 in Haux. destruct Haux. apply H5.
      +++ intros x2 Hd. apply empty_is_empty in H1 as [x1 H1].
      assert (Haux: In (X * X) (prod C D) (x1, x2)).
      { split. apply H1. apply Hd. }
      rewrite <- H3 in Haux. destruct Haux. apply H5.
  + intros [HAC HBD]. rewrite HAC. rewrite HBD. reflexivity.
Qed.
