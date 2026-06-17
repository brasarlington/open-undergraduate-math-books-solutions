From Stdlib Require Import Sets.Ensembles.
From OUMBS Require Import Graphs.

Theorem exercise_2_ii : forall (U V : Type) (G : Graph U V),
  dom G = ran (Inverse G).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Inverse, Compose, In, dom, ran in *.
  split;
  intros x [x0 H]; exists x0; unfold In; simpl; apply H.
Qed.

Theorem exercise_2_iv : forall (U : Type) (G H : Graph U U),
  Included U (ran (Compose G H)) (ran G).
Proof.
  intros U G H.
  unfold Included, ran, Compose.
  intros z [x [y [_ Gyz]]].
  exists y.
  exact Gyz.
Qed.
