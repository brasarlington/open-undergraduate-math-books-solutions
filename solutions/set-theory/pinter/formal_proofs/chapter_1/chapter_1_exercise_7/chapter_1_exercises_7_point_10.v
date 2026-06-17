From OUMBS Require Import Definitions.
From Stdlib Require Import Logic.Classical.

Definition P_o_expected := Singleton Empty.

Lemma P_o : P_o_expected = PowerSet Empty.
Proof.
  apply A1_extent. intros. split.
  - intros. unfold P_o_expected in H0. apply singleton_def in H0.
    rewrite H0. apply Empty_in_Power. apply H.
  - intros. apply PowerSet_Empty_eq in H0.
    ** rewrite H0. unfold P_o_expected. apply singleton_def. apply A4_empty_set.
       reflexivity.
    ** apply H.
Qed.

Definition P_P_o_expected := Pair Empty (Singleton Empty).

Theorem P_P_o : P_P_o_expected = PowerSet (PowerSet Empty).
Proof.
  apply A1_extent. intros. split.
  - intros. unfold P_P_o_expected in H0. apply pair_def in H0. destruct H0.
    ** rewrite H0. apply Empty_in_Power.
    ** apply power_def. apply H. unfold subclass. intros.
    rewrite H0 in H2. apply singleton_def in H2.
    rewrite H2. apply Empty_in_Power. apply H1.
    ** apply H.
  - intros. apply power_def in H0. unfold P_P_o_expected; apply pair_def.
    apply H. destruct (classic (exists z, In z x)).
    ** destruct H1. apply H0 in H1 as H2. apply PowerSet_Empty_eq in H2 as H2. right.
       *** apply A1_extent. intros. split.
           **** intros. apply H0 in H4. apply PowerSet_Empty_eq in H4. apply singleton_def. apply H3. apply H4. apply H3. apply H3.
           **** intros. apply singleton_def in H4.
                rewrite H4. rewrite H2 in H1. apply H1. apply H3.
       *** exists x. apply H1.
       *** exists x. apply H1.
    ** left. apply A1_extent. intros. split.
       *** intros. assert (exists z : Class, In z x) by (exists x0; apply H3).
           contradiction.
       *** intros. apply empty_def in H2. contradiction.
    ** apply H.
Qed.

Definition P_P_P_o_expected :=
  Union
      (Pair Empty (Singleton Empty))
      (Pair (Singleton (Singleton Empty)) (Pair Empty (Singleton Empty))).

Lemma empty_is_not_S_empty : Empty <> Singleton Empty.
Proof.
  intros HESE. assert (exists z, is_set z /\ In z Empty). {
    rewrite HESE. exists Empty. split. apply A4_empty_set. apply singleton_def. apply A4_empty_set. reflexivity.
  }
  destruct H as [z [Hs HsE]]. apply empty_def in Hs. contradiction.
Qed.

Theorem P_P_P_o : P_P_P_o_expected = PowerSet (PowerSet (PowerSet Empty)).
Proof.
  apply A1_extent. intros. split.
  - intros. unfold P_P_P_o_expected in H0. apply union_def in H0. destruct H0.
    ** apply pair_def in H0. destruct H0.
      *** rewrite H0. apply Empty_in_Power.
      *** apply power_def. apply H. unfold subclass. intros. rewrite H0 in H2. apply singleton_def in H2. rewrite H2. apply Empty_in_Power. apply H1.
      *** apply H.
    ** apply pair_def in H0. destruct H0.
      *** apply power_def. apply H. unfold subclass. intros. rewrite H0 in H2.
      apply singleton_def in H2.
        **** apply power_def. apply H1. unfold subclass. intros. rewrite H2 in H4. apply singleton_def in H4. rewrite H4. apply Empty_in_Power. apply H3.
        **** apply H1.
      *** rewrite <- P_P_o. assert (Haux: P_P_o_expected = Pair Empty (Singleton Empty)) by reflexivity. rewrite <- Haux in H0. rewrite H0. apply all_in_power. rewrite H0 in H. apply H.
      *** apply H.
    ** apply H.
  - intros. unfold P_P_P_o_expected. apply union_def.
    apply H. rewrite !pair_def.
    apply power_def in H0. destruct (classic (exists z, In z x)).
    destruct H1. apply H0 in H1 as H2. rewrite <- P_P_o in H2. apply pair_def in H2. destruct H2. destruct (classic (exists z, z <> Empty /\ In z x)). destruct H3 as [x1 [H3 H4]]. apply H0 in H4 as HSE. rewrite <- P_P_o in HSE. apply pair_def in HSE. destruct HSE. contradiction.
    ** right. right. apply A1_extent. intros. split.
      *** intros. apply pair_def. apply H6. apply H0 in H7. rewrite <- P_P_o in H7. apply pair_def in H7. destruct H7. left. apply H7. right. apply H7. apply H6. apply H6.
      *** intros. apply pair_def in H7. destruct H7. rewrite H7. rewrite H2 in H1. apply H1. rewrite H7. rewrite H5 in H4. apply H4. apply H6.
    ** exists x. apply H4.
    ** exists x. apply H4.
    ** left. right. apply A1_extent. intros. split.
      *** intros. apply H0 in H5 as H6. rewrite <- P_P_o in H6. apply pair_def in H6. destruct H6. apply singleton_def. apply H4. apply H6. assert (exists z : Class, z <> Empty /\ In z x). { exists x1. split. intros Hx1_empty. rewrite Hx1_empty in H6. apply empty_is_not_S_empty in H6. apply H6. apply H5. } contradiction. apply H4. apply H4.
      *** intros. apply singleton_def in H5. rewrite H5. rewrite <- H2. apply H1. apply H4.
    ** destruct (classic (exists z : Class, z <> Singleton Empty /\ In z x)).
      *** destruct H3 as [x1 [H3 H4]]. apply H0 in H4 as H5. rewrite <- P_P_o in H5. apply pair_def in H5. destruct H5. right. right. apply A1_extent. intros. split. intros. apply H0 in H7. rewrite <- P_P_o in H7. apply pair_def in H7. destruct H7. apply pair_def. apply H6. left. apply H7. apply pair_def. apply H6. right. apply H7. apply H6. apply H6. intros. apply pair_def in H7. destruct H7. rewrite H7. rewrite <- H5. apply H4.  rewrite H7. rewrite <- H2.  apply H1. apply H6. contradiction. exists x. apply H4. exists x. apply H4.
      *** right. left. apply A1_extent. intros. split.
        **** intros. apply singleton_def. apply H4. apply H0 in H5 as H6. rewrite <- P_P_o in H6. apply pair_def in H6. destruct H6. assert (exists z : Class, z <> Singleton Empty /\ In z x). { exists x1. split. rewrite H6. apply empty_is_not_S_empty. apply H5. } contradiction. apply H6. apply H4. apply H4.
        **** intros. apply singleton_def in H5. rewrite H5. rewrite <- H2. apply H1. apply H4.
    ** exists x. apply H1.
    ** exists x. apply H1.
    ** left. left. apply A1_extent. intros. split.
      *** intros. assert (exists z : Class, In z x). { exists x0. apply H3. } contradiction.
      *** intros. apply empty_def in H2. contradiction.
    ** apply H.
    ** apply H.
    ** apply H.
Qed.
