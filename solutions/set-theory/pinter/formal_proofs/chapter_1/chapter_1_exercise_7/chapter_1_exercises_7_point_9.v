From OUMBS Require Import Definitions.

Theorem exercise_9_a : forall (A : Class),
  is_set A ->
  GenUnion (PowerSet A) = A.
Proof.
  intros. apply A1_extent. intros. split.
  * intros. apply gen_union_def in H1. destruct H1 as [n [H1 [H2 H3]]].
    apply power_def in H2. apply H2 in H3. apply H3.
    apply H0. apply H1. apply H0.
  * intros. apply gen_union_def. apply H0. exists A. split. apply H.
    split. apply all_in_power. apply H. apply H1.
Qed.

Theorem exercise_9_b : forall (A : Class),
  is_set A ->
  GenInter (PowerSet A) = Empty.
Proof.
  intros. apply A1_extent. intros. split.
  * intros. eapply (gen_inter_def (PowerSet A) x H0) in H1. apply H1.
    apply A4_empty_set. apply Empty_in_Power.
  * intros. apply empty_def in H0. contradiction.
Qed.

Theorem exercise_9_c : forall (A B : Class),
  is_set A ->
  is_set B ->
  In (PowerSet A) (PowerSet B) ->
  In A B.
Proof.
  intros.
  apply power_def in H1.
  - unfold subclass in H1. apply H1. apply H. apply all_in_power. apply H.
  - apply A7_power_set. apply H.
Qed.
