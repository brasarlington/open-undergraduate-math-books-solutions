From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.
From OUMBS Require Import Definitions.

Lemma test_empty : forall (Index U : Type) (u: U) (S : Indexed_Family Index U),
  ~(exists (x : Index), ~ In (Index * U) S (x, u)) ->
  forall (x : Index), In (Index * U) S (x, u).
Proof.
  intros.
  destruct (classic (In (Index * U) S (x, u))).
  * apply H0.
  * assert (exists x : Index, ~ In (Index * U) S (x, u)). {
    exists x. apply H0.
  }
  contradiction.
Qed.

Theorem exercise_1_41_ii :
  forall (Index U : Type) (A : Indexed_Family Index U),
  Complement U (General_Intersection A) 
  = General_Union (Complement (Index * U) A).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, General_Intersection, General_Union, Complement, In in *. split.
  * intros u H.
    destruct (classic (exists j : Index, ~ In (Index * U) A (j, u))).
    ** destruct H0. exists x. apply H0.
    ** pose proof (test_empty Index U u A H0) as H1. contradiction.
  * intros x [j Hjx] Hix. apply Hjx in Hix. apply Hix.
Qed.
