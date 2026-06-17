From OUMBS Require Import Definitions.

Theorem dom_subclass_u_u_g : forall (G : Class),
  subclass (Dom G) (GenUnion (GenUnion G)).
Proof.
  unfold subclass.
  intros.
  destruct (dom_def G x H).
  apply H1 in H0. destruct H0.
  assert (H3: exists y : Class, is_set y /\ In (OPair x y) G)
    by (exists x0; apply H0).
  apply H2 in H3.

  assert (Hpx : is_set (Pair x x)) by (apply A5_pair_set; apply H; apply H).
  assert (Hpxx0 : is_set (OPair x x0)) by (unfold is_set; exists G; apply H0).

  apply gen_union_def. apply H. exists (Pair x x). split; try split.
  * apply Hpx.
  * apply gen_union_def. apply Hpx.
  exists (OPair x x0). split.
    ** apply Hpxx0.
    ** split; try split.
      *** apply H0.
      *** unfold OPair. apply pair_def. apply Hpx. left. reflexivity.
  * apply pair_def. apply H. left. reflexivity.
Qed.

Theorem ran_subclass_u_u_g : forall (G : Class),
  subclass (Ran G) (GenUnion (GenUnion G)).
Proof.
  unfold subclass.
  intros.
  destruct (ran_def G x H).
  apply H1 in H0. destruct H0.
  assert (H3: exists y : Class, is_set y /\ In (OPair y x) G)
    by (exists x0; apply H0).
  apply H2 in H3.

  assert (Hpx : is_set (Pair x0 x0)) by (apply A5_pair_set; apply H0).
  assert (Hpxx: is_set (Pair x0 x)) by (apply A5_pair_set; apply H0 || apply H).
  assert (Hpxx0 : is_set (OPair x0 x)) by (unfold is_set; exists G; apply H0).

  apply gen_union_def. apply H. exists (Pair x0 x). split; try split.
  * apply Hpxx.
  * apply gen_union_def. apply Hpxx.
  exists (OPair x0 x). split.
    ** apply Hpxx0.
    ** split; try split.
      *** apply H0.
      *** unfold OPair. apply pair_def. apply Hpxx. right. reflexivity.
  * apply pair_def. apply H. right. reflexivity.
Qed.

Theorem exercise_5_a : forall (G : Class),
  is_set G ->
  is_set (Dom G).
Proof.
  intros.
  apply (A3_subclass_set (GenUnion (GenUnion G)) (Dom G)).
  * apply A6_gen_union_set. apply A6_gen_union_set. apply H.
  * apply dom_subclass_u_u_g.
Qed.

Theorem exercise_5_b : forall (G : Class),
  is_set G ->
  is_set (Ran G).
Proof.
  intros.
  apply (A3_subclass_set (GenUnion (GenUnion G)) (Ran G)).
  * apply A6_gen_union_set. apply A6_gen_union_set. apply H.
  * apply ran_subclass_u_u_g.
Qed.
