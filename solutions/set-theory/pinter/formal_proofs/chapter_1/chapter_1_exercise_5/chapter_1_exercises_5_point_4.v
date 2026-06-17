From Stdlib Require Import Sets.Ensembles.
From OUMBS Require Import Graphs.

Theorem exercise_4_a : forall (U V W : Type) (H J : Graph U V) (G : Graph W U),
  Compose (Union (U * V) H J) G = Union (W * V) (Compose H G) (Compose J G).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, dom, ran, Compose, In in *. split.
  * intros [w v] [u [H1 H2]]. remember (u, v) as x. destruct H2; subst.
    ** apply Union_introl. unfold In in *. exists u. split. apply H1. apply H0.
    ** apply Union_intror. unfold In in *. exists u. split. apply H1. apply H0.
  * intros [w v] H1. remember (w, v) as x. destruct H1; subst.
    ** unfold In in *. destruct H0 as [u [H1 H2]]. exists u. split. apply H1. apply Union_introl. apply H2.
    ** unfold In in *. destruct H0 as [u [H1 H2]]. exists u. split. apply H1. apply Union_intror. apply H2.
Qed.


Theorem exercise_4_b : forall (U V : Type) (H G : Graph U V),
  Inverse (Setminus (U * V) G H) = Setminus (V * U) (Inverse G) (Inverse H).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, Setminus, Inverse, In in *. split;
  intros [v u] H0; destruct H0; unfold In in *; simpl in *; split;
    apply H0 || apply H1.
Qed.

Theorem exercise_4_c : forall (U V W : Type)
  (G : Graph U V)
  ( H J : Graph W U ),
  Included (W * V)
  (Compose G (Intersection (W * U) H J))
  (Intersection (W * V) (Compose G H) (Compose G J)).
Proof.
  intros.
  unfold Included, Compose, In.
  intros [w v] H0. destruct H0 as [y [H1 H2]]. remember (w, y) as x. destruct H1. subst. split.
  * unfold In. exists y. split. apply H0. apply H2.
  * unfold In. exists y. split. apply H1. apply H2.
Qed.

Theorem exercise_4_d : forall (U V W : Type)
  (G : Graph U V)
  ( H J : Graph W U ),
  Included (W * V)
  (Setminus (W * V) (Compose G H) (Compose G J))
  (Compose G (Setminus (W * U) H J)).
Proof.
  intros.
  unfold Included, Compose, In, Setminus, In.
  intros [w v] H0. destruct H0 as [[y [H1 H2]] H3]. exists y. split.
  ** split.
     *** apply H1.
     *** intros HJ.
         assert (contra: exists y : U, J (w, y) /\ G (y, v)). { exists y. split. apply HJ. apply H2.  }
         contradiction.
  ** apply H2.
Qed.
