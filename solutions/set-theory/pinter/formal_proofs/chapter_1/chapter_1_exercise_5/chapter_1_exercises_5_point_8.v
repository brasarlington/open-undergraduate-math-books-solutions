From Stdlib Require Import Sets.Ensembles.
From OUMBS Require Import Graphs.

Theorem exercise_8_a : forall (U V : Type)
  (G : Graph U V) (A : Ensemble U) (B : Ensemble V),
  Included (U * V) G (prod A B) ->
  Included (V * U) (Inverse G) (prod B A).
Proof.
  intros.
  unfold Included, In, Inverse, Compose, In in *.
  * intros [v u] H0. simpl in *. apply H in H0. destruct H0. split.
    ** apply H1.
    ** apply H0.
Qed.

Theorem exercise_8_b : forall (U V W: Type)
  (G : Graph V U) (A : Ensemble V) (B : Ensemble U)
  (H : Graph U W) (C : Ensemble W),
  Included (V * U) G (prod A B) ->
  Included (U * W) H (prod B C) ->
  Included (V * W) (Compose H G) (prod A C).
Proof.
  intros.
  unfold Included, In, Compose, prod, In in *.
  * intros [v w] [u [HG HH]]. simpl in *. apply H0 in HG as [HA _].
    apply H1 in HH as [_ HC]. split. apply HA. apply HC.
Qed.
