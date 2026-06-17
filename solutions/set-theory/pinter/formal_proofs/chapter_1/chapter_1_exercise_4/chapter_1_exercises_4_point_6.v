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

Theorem exercise_6_1 : forall (X : Type) (A B C: Ensemble X),
  C <> Empty_set X ->
  (Disjoint X A B <-> Disjoint (X * X) (prod A C) (prod B C)).
Proof.
  intros.
  split.
  - intros HADB. destruct HADB. constructor. intros [u v] H1. inversion H1. unfold In, prod in H2, H3. simpl in *. destruct H2, H3. assert (Haux: In X (Intersection X A B) u). { split. apply H2. apply H3. } apply H0 in Haux. apply Haux.
  - intros HADB. destruct HADB. constructor. intros x HA. destruct HA.
    apply empty_is_empty in H. destruct H as [x2 H].
    assert (Haux: In (X * X) (Intersection (X * X) (prod A C) (prod B C)) (x, x2)). {
      split; split; unfold In; simpl. apply H1. apply H. apply H2. apply H.
    }
    apply H0 in Haux. apply Haux.
Qed.
