From OUMBS Require Import chapter_1_exercises_1_point_2.

Theorem exercise_1_3_a : forall (P: Prop), ~~P <-> P.
Proof. split.
unfold not.
* intros H. destruct (invalid_middle P) as [HP | HNP]. apply HP. apply H in HNP. destruct HNP.
* intros HP. unfold not. intros HNP. apply HNP in HP. apply HP.
Qed.
