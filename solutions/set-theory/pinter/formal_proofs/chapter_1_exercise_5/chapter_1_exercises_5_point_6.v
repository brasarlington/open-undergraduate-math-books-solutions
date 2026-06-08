From Stdlib Require Import Sets.Ensembles.
From OUMBS Require Import Graphs.

Theorem exercise_6_a : forall (U V W: Type)
  (G H : Graph U V)
  (J K : Graph W U),
  Included (U * V) G H ->
  Included (W * U) J K ->
  Included (W * V) (Compose G J) (Compose H K).
Proof.
  intros.
  unfold Included, In, Compose in *.
  intros [w v] [u [HJ HG]].
  exists u. split.
  ** apply H1 in HJ. apply HJ.
  ** apply H0 in HG. apply HG.
Qed.

Theorem exercise_6_b : forall (U V : Type)
  (G H : Graph U V),
  Included (U * V) G H <-> Included (V * U) (Inverse G) (Inverse H).
Proof.
  intros.
  unfold Included, In, Inverse in *.
  split.
  * intros H0 [v u] H1. simpl in *. apply H0 in H1. apply H1.
  * intros H0 [v u] H1. specialize H0 with (x := (u, v)). simpl in *. apply H0 in H1. apply H1.
Qed.
