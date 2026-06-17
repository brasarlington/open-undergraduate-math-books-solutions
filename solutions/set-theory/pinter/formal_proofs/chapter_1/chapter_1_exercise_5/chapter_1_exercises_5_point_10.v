From Stdlib Require Import Sets.Ensembles.
From OUMBS Require Import Graphs.

Theorem exercise_10_a : forall (U V : Type)
  (G : Graph U V)
  (B : Ensemble U),
  Restriction G B = Intersection (U * V) G (prod B (ran G)).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, dom, ran, Restriction, In in *. split.
  - intros [u v] [H1 H2]. split.
    ** apply H1.
    ** split. apply H2. exists u. apply H1.
  - intros [u v] H. remember (u, v). destruct H. subst. destruct H0. destruct H1. simpl in *. split. apply H.  apply H0.
Qed.

Theorem exercise_10_b : forall (U V : Type)
  (G : Graph U V)
  (B C : Ensemble U),
  Restriction G (Union U B C) = Union (U * V) (Restriction G B) (Restriction G C).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, dom, ran, Restriction, In in *. split.
  - intros [u v] H. remember u. destruct H. destruct H0; subst.
    ** apply Union_introl. split. apply H. apply H0.
    ** apply Union_intror. split. apply H. apply H0.
  - intros [u v] H. remember (u, v). destruct H; subst; split.
    **  destruct H. apply H.
    **  destruct H. apply Union_introl. apply H0.
    **  destruct H. apply H.
    **  destruct H. apply Union_intror. apply H0.
Qed.

Theorem exercise_10_c : forall (U V : Type)
  (G : Graph U V)
  (B C : Ensemble U),
  Restriction G (Intersection U B C) = Intersection (U * V) (Restriction G B) (Restriction G C).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, dom, ran, Restriction, In in *. split.
  - intros [u v] H. remember u. destruct H. subst. split.
    ** split. apply H. destruct H0. apply H0.
    ** split. apply H. destruct H0. apply H1.
  - intros [u v] H. remember (u, v). destruct H. subst. split.
    ** destruct H0. apply H0.
    ** split; destruct H0; destruct H. apply H2. apply H1.
Qed.

Theorem exercise_10_d : forall (U V W: Type)
  (G : Ensemble (U * V)) (H : Ensemble (W * U))
  (B : Ensemble W),
  Restriction (Compose G H) B = Compose G (Restriction H B).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, dom, ran, Compose, Restriction, In in *. split.
  - intros [w v] [[u [HH HG]] HB]. exists u. split.
    ** split. apply HH. apply HB.
    ** apply HG.
  - intros [w v] [u [[HH HB] HG]]. split. exists u. split.
    ** apply HH.
    ** apply HG.
    ** apply HB.
Qed.
