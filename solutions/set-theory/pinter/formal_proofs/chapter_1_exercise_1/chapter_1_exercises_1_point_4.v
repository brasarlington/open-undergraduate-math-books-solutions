From OUMBS Require Import chapter_1_exercises_1_point_2.

Theorem exercise_1_4_a : forall (P Q: Prop), (P -> Q) <-> (~Q -> ~P).
Proof.
  intros P Q. split.
  * intros HPQ. unfold not. intros HNQ. intros HP. apply HPQ in HP. apply HNQ in HP. apply HP.
  * unfold not. intros HNPNQ. intros HP. destruct (invalid_middle Q).
    ** apply H.
    ** apply HNPNQ in H. destruct H. apply HP.
Qed.

Theorem exercise_1_4_b : forall (P Q: Prop), (P -> Q) <-> (~P \/ Q).
Proof.
  intros P Q. split.
  * intros HPQ. destruct (invalid_middle P). apply HPQ in H. right. apply H.
    left. apply H.
  * unfold not. intros [HNP | HQ].
    ** intros HP. apply HNP in HP. destruct HP.
    ** intros HP. apply HQ.
Qed.

Theorem exercise_1_4_c : forall (P Q: Prop), (P -> Q) <-> ~(P /\ ~Q).
Proof.
  intros P Q. split.
  * intros HPQ. unfold not. intros [HP HNQ]. apply HPQ in HP. apply HNQ in HP. apply HP.
  * unfold not. intros HNPNQ HP. destruct (invalid_middle Q).
    ** apply H.
    ** assert (H1: P /\ ~Q). { split. apply HP. apply H. } apply HNPNQ in H1. destruct H1.
Qed.

Theorem exercise_1_4_d : forall (P Q: Prop), (P /\ (P -> Q)) -> Q.
Proof.
  intros P Q [HP HPQ].
  apply HPQ in HP. apply HP.
Qed.

Theorem exercise_1_4_e : forall (P Q: Prop), ((P \/ Q) /\ ~P) -> Q.
Proof.
  intros P Q [[HP | HQ] HNP].
  * apply HNP in HP. destruct HP.
  * apply HQ.
Qed.
