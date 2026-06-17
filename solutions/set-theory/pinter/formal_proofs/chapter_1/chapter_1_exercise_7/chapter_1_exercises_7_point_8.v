From OUMBS Require Import Definitions.

Theorem exercise_8_a : forall (A B : Class),
  subclass A B <-> subclass (PowerSet A) (PowerSet B).
Proof.
  intros. unfold subclass. split.
  * intros. apply power_def. apply H0. apply power_def in H1.
    ** unfold subclass in *. intros. apply (H x0 H2 (H1 x0 H2 H3)).
    ** apply H0.
  * intros. apply element_means_pair_in_power in H1 as Haux.
    apply (H (Pair x x)) in Haux. apply pair_in_m in Haux. apply Haux. apply H0.
    apply A5_pair_set; apply H0.
Qed.

Theorem exercise_8_b : forall (A B : Class),
  A = B <-> PowerSet A = PowerSet B.
Proof.
  intros. split.
  - intros. rewrite H. reflexivity.
  - intros. apply A1_extent. intros. split.
    ** intros. apply element_means_pair_in_power in H1. rewrite H in H1. apply pair_in_m in H1. apply H1. apply H0.
    ** intros. apply element_means_pair_in_power in H1. rewrite <- H in H1. apply pair_in_m in H1. apply H1. apply H0.
Qed.

Theorem exercise_8_c : forall (A B : Class),
  Intersection (PowerSet A) (PowerSet B) = PowerSet (Intersection A B).
Proof.
  intros. apply A1_extent. intros. split.
  * intros. apply inter_def in H0 as [HPA HPB].
    ** apply power_def. apply H. unfold subclass. intros.
       apply power_def in HPA, HPB. apply HPA in H1 as HA. apply HPB in H1 as HB.
       apply inter_def. apply H0. split. apply HA. apply HB.
       apply H0. apply H0. apply H. apply H.
    ** apply H.
  * intros. apply power_def in H0.
    ** apply inter_def. apply H. split.
       *** apply power_def. apply H. unfold subclass. intros. apply H0 in H2 as HI. apply inter_def in HI. apply HI. apply H1. apply H1.
       *** apply power_def. apply H. unfold subclass. intros. apply H0 in H2 as HI. apply inter_def in HI. apply HI. apply H1. apply H1.
    ** apply H.
Qed.

Theorem exercise_8_d : forall (A B : Class),
  subclass (Union (PowerSet A) (PowerSet B)) (PowerSet (Union A B)).
Proof.
  unfold subclass. intros. apply union_def in H0. destruct H0.
    * apply power_def in H0.
       ** apply power_def. apply H. unfold subclass. intros. apply H0 in H2.
           *** apply union_def. apply H1. left. apply H2.
           *** apply H1.
       ** apply H.
    * apply power_def. apply H. apply power_def in H0.
       ** unfold subclass. intros. apply union_def. apply H1. apply H0 in H2.
           *** right. apply H2.
           *** apply H1.
       ** apply H.
    * apply H.
Qed.

Lemma PowerSet_Empty : PowerSet Empty = Pair Empty Empty.
Proof.
  apply A1_extent. intros. split.
  - intros. apply PowerSet_Empty_eq in H0. rewrite H0.
    apply pair_def. apply A4_empty_set. left. reflexivity.
    apply H.
  - intros. apply pair_def in H0. destruct H0; rewrite H0. apply Empty_in_Power.
  apply Empty_in_Power. apply H.
Qed.

Theorem exercise_8_e : forall (A B : Class),
  Intersection A B = Empty <-> Intersection (PowerSet A) (PowerSet B) = (Pair Empty Empty).
Proof.
  intros. split.
  * intros. apply A1_extent. intros. split.
    ** intros. rewrite exercise_8_c in H1.
       rewrite H in H1. apply PowerSet_Empty_eq in H1. apply pair_def. apply H0.
       left. apply H1. apply H0.
    ** intros. apply pair_def in H1. destruct H1.
       *** apply inter_def. apply H0. split; rewrite H1; apply Empty_in_Power.
       *** apply inter_def. apply H0. split; rewrite H1; apply Empty_in_Power.
       *** apply H0.
  * intros. rewrite exercise_8_c in H. rewrite <- PowerSet_Empty in H. apply exercise_8_b in H. apply H.
Qed.
