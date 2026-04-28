From OUMBS Require Import chapter_1_exercises_1_point_1.

Theorem exercise_1_5_a : forall (P Q R : Prop), ((P -> Q) /\  (Q -> R)) -> (P -> R).
Proof.
  intros P Q R [HPQ HQR] H.
  apply HPQ in H. apply HQR in H. apply H.
Qed.

Theorem exercise_1_5_b : forall (P Q R : Prop), ((P -> Q) /\  (R -> Q)) <-> ((P \/ R) -> Q).
Proof.
  intros P Q R. split.
  * intros [HPQ HQR] [HP | HR].
    ** apply HPQ in HP. apply HP.
    ** apply HQR in HR. apply HR.
  * intros HPRQ. split.
    ** intros HP. apply or_introl with (B := R) in HP. apply HPRQ. apply HP.
    ** intros HR. apply or_introl with (B := P) in HR. apply theorem_1_8_i in HR. apply HPRQ. apply HR.
Qed.

Theorem exercise_1_5_c : forall (P Q R : Prop), ((P -> Q) /\  (P -> R)) <-> (P -> (Q /\ R)).
Proof.
  intros P Q R. split.
  * intros [HPQ HPR] HP. split.
    ** apply HPQ. apply HP.
    ** apply HPR. apply HP.
  * intros HPQR. split; intros HP; apply HPQR; apply HP.
Qed.
