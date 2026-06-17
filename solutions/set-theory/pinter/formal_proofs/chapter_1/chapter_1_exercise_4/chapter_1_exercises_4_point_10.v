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

Lemma prod_with_empty_is_empty : forall (X Y : Type) (A : Ensemble X),
  prod A (Empty_set Y) = Empty_set (X * Y) /\
  prod (Empty_set Y) A = Empty_set (Y * X).
Proof.
  intros.
  split.
  * apply Extensionality_Ensembles. unfold Same_set, Included, In. split.
    ** intros x H. destruct H. destruct H0.
    ** intros x H. destruct H.
  * apply Extensionality_Ensembles. unfold Same_set, Included, In. split.
    ** intros x H. destruct H. destruct H.
    ** intros x H. destruct H.
Qed.

Theorem exercise_10_1 : forall
  (X Y : Type)
  (A : Ensemble X)
  (B : Ensemble Y),
  prod A B = Empty_set (X * Y) <-> A = Empty_set X \/ B = Empty_set Y.
Proof.
  split.
  * intros. destruct (classic (exists x1, In X A x1)).
    ** destruct (classic (exists x2, In Y B x2)).
       *** destruct H0 as [x1 H0]. destruct H1 as [x2 H1].
           assert (Haux: In (X * Y) (prod A B) (x1, x2)).
           { split. apply H0. apply H1. }
           rewrite H in Haux. destruct Haux.
       *** right. apply NNPP. intros H2. apply empty_is_empty in H2. apply H1 in H2. apply H2.
    ** left. apply NNPP. intros H2. apply empty_is_empty in H2. apply H0 in H2. apply H2.
  * intros [HAE | HBE].
    ** rewrite HAE. apply prod_with_empty_is_empty.
    ** rewrite HBE. apply prod_with_empty_is_empty.
Qed.
