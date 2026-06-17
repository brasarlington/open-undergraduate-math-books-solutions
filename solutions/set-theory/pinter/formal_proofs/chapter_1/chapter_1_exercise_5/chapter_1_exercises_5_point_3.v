From Stdlib Require Import Sets.Ensembles.
From OUMBS Require Import Graphs.

Theorem exercise_3_1 : forall (U V W: Type) (G : Graph U V) (H : Graph W U),
  Included U (ran H) (dom G) ->
  dom (Compose G H) = dom H.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, dom, ran, Compose, In in *. split.
  - intros x [y [y0 [H1 H2]]]. exists y0. apply H1.
  - intros x [y H1]. specialize H0 with (x := y).
  assert (Haux: exists x0 : W, H(x0, y)). { exists x. apply H1. }
  apply H0 in Haux as [y0 H2]. exists y0, y. split.
    ** apply H1.
    ** apply H2.
Qed.
