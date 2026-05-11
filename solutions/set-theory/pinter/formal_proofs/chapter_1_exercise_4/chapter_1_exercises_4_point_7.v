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
  C <> Empty_set X ->
  (Included X A B /\ Included X C D <-> Included (X * X) (prod A C) (prod B D)).
Proof.
  intros. split.
  + intros [H1 H2]. unfold Included in *. intros [u v] H3. unfold In in *. destruct H3. split.
    ++ apply H1 in H3. apply H3.
    ++ apply H2 in H4. apply H4.
  + unfold Included. intros. split.
    ++ intros x1 H2. apply empty_is_empty in H0 as [x2 H0].
    assert (Haux: In (X * X) (prod A C) (x1, x2)).
    { split. apply H2. apply H0. }
    apply H1 in Haux. destruct Haux. apply H3.
    ++ intros x2 H2. apply empty_is_empty in H as [x1 H].
    assert (Haux: In (X * X) (prod A C) (x1, x2)).
    { split. apply H. apply H2. }
    apply H1 in Haux. destruct Haux. apply H4.
Qed.
