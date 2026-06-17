From Stdlib Require Import Sets.Ensembles.
From OUMBS Require Import Graphs.

Theorem exercise_9_a : forall (U V : Type) (G H : Graph U V),
  dom (Union (U * V) G H) = Union U (dom G) (dom H).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, dom, ran, Compose, In in *. split.
  * intros u [v H0]. remember (u, v) as p. destruct H0; subst.
    ** apply Union_introl. exists v. apply H0.
    ** apply Union_intror. exists v. apply H0.
  * intros u H0. remember u. destruct H0; subst.
    ** destruct H0. exists x. apply Union_introl. apply H0.
    ** destruct H0. exists x. apply Union_intror. apply H0.
Qed.

Theorem exercise_9_b : forall (U V : Type) (G H : Graph U V),
  ran (Union (U * V) G H) = Union V (ran G) (ran H).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, dom, ran, Compose, In in *. split.
  * intros v [u H0]. remember (u, v). destruct H0; subst.
    ** apply Union_introl. exists u. apply H0.
    ** apply Union_intror. exists u. apply H0.
  * intros v H0. remember v. destruct H0; subst.
    ** destruct H0. exists x. apply Union_introl. apply H0.
    ** destruct H0. exists x. apply Union_intror. apply H0.
Qed.

Theorem exercise_9_c : forall (U V : Type) (G H : Graph U V),
  Included U (Setminus U (dom G) (dom H)) (dom (Setminus (U * V) G H)).
Proof.
  intros.
  unfold Same_set, Included, In, dom, ran, Compose, In in *.
  intros u [H0 H1]. destruct H0. exists x. split.
  * apply H0.
  * intros HH.
    assert (contra: In U (fun p : U => exists y : V, H (p, y)) u) by
    (exists x; apply HH).
    contradiction.
Qed.

Theorem exercise_9_d : forall (U V : Type) (G H : Graph U V),
  Included V (Setminus V (ran G) (ran H)) (ran (Setminus (U * V) G H)).
Proof.
  intros.
  unfold Same_set, Included, In, dom, ran, Compose, In in *.
  intros u [H0 H1]. destruct H0. exists x. split.
  * apply H0.
  * intros HH.
    assert (contra: In V (fun p : V => exists x : U, H (x, p)) u) by
    (exists x; apply HH).
    contradiction.
Qed.
