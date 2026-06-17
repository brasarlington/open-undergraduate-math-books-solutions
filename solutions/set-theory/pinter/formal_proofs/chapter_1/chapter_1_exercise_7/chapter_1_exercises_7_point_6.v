From OUMBS Require Import Definitions.
From OUMBS Require Import chapter_1_exercises_7_point_5.

Theorem inv_is_set : forall (G : Class),
  is_set G -> is_set (Inv G).
Proof.
  intros.
  apply (A3_subclass_set (CartProd (Ran G) (Dom G)) (Inv G)).
  - apply cart_prod_is_set. apply exercise_5_b. apply H.
    apply exercise_5_a. apply H.
  - unfold subclass. intros. apply inv_def in H1.
    ** destruct H1 as [n1 [n2 [H1 [H2 [H3 H4]]]]].
    apply cart_prod_def. apply H0. exists n2, n1.
    split. apply H2. split. apply H1. split. apply H3.
    split.
      *** apply ran_def. apply H2. exists n1. split. apply H1. apply H4.
      *** apply dom_def. apply H1. exists n2. split. apply H2. apply H4.
    ** apply H0.
Qed.


Theorem comp_is_set : forall (G H : Class),
  is_set G -> is_set H -> is_set (Comp G H).
Proof.
  intros.
  apply (A3_subclass_set (CartProd (Dom H) (Ran G)) (Comp G H)).
  - apply cart_prod_is_set. apply exercise_5_a. apply H1.
    apply exercise_5_b. apply H0.
  - unfold subclass. intros. apply comp_def in H3.
    ** destruct H3 as [n1 [n2 [n3 [H3 [H4 [H5 [H6 [H7 H8]]]]]]]].
      apply cart_prod_def. apply H2. exists n1, n3. split. apply H3. split.
      apply H5. split. apply H6. split.
      *** apply dom_def. apply H3. exists n2. split. apply H4. apply H7.
      *** apply ran_def. apply H5. exists n2. split. apply H4. apply H8.
    ** apply H2.
Qed.
