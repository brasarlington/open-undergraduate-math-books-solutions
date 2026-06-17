From Stdlib Require Import Sets.Ensembles.
From OUMBS Require Import Graphs.

Theorem exercise_5_a : forall (U V : Type) (G H : Graph U V),
  Inverse (Intersection (U * V) G H)
  = Intersection (V * U) (Inverse G) (Inverse H).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, Inverse, In in *. split.
  * intros [w v] H0. simpl in *. remember (v, w) as p. destruct H0. subst.
    split.
    ** apply H0.
    ** apply H1.
  * intros [v w] H0. simpl in *. remember (v, w) as p. destruct H0. subst.
    split.
    ** apply H0.
    ** apply H1.
Qed.


Theorem exercise_5_b : forall (U V : Type) (G H : Graph U V),
  Inverse (Union (U * V) G H)
  = Union (V * U) (Inverse G) (Inverse H).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, Inverse, In in *. split.
  * intros [v w] H0. simpl in *. remember (w, v) as p. destruct H0; subst.
    apply Union_introl. apply H0. apply Union_intror. apply H0.
  * intros [v w] H0. simpl in *. remember (v, w) as p. destruct H0; subst.
    ** apply Union_introl. apply H0.
    ** apply Union_intror. apply H0.
Qed.
