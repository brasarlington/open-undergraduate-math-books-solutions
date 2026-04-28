From OUMBS Require Import chapter_1_exercises_1_point_1.

Theorem exercise_1_2_a : forall (P Q: Prop), ~(P \/ Q) <-> (~ P) /\ (~ Q).
Proof.
  intros P Q.
  unfold not. split.
  * intros HPQ. split.
    ** intros HP. apply or_introl with (B := Q) in HP. apply HPQ in HP. apply HP.
    ** intros HQ. apply or_introl with (B := P) in HQ. apply theorem_1_8_i in HQ. apply HPQ in HQ. apply HQ.
  * intros [HNP HNQ]. intros [HP | HQ]. apply HNP in HP. apply HP. apply HNQ in HQ. apply HQ.
Qed.

Axiom invalid_middle : forall (P : Prop), P \/ ~P.

Theorem exercise_1_2_b : forall (P Q: Prop), ~(P /\ Q) <-> (~ P) \/ (~ Q).
Proof.
  intros P Q.
  unfold not. split.
  * intros HNPQ. destruct (invalid_middle P) as [HP | HNP].
    ** right. intros HQ. assert (H: P /\ Q). { split. apply HP. apply HQ. }
       apply HNPQ in H. apply H.
    ** left. apply HNP.
  * intros [HNP | HNQ].
    ** intros HPQ. apply proj1 in HPQ. apply HNP in HPQ. apply HPQ.
    ** intros HPQ. apply proj2 in HPQ. apply HNQ in HPQ. apply HPQ.
Qed.
