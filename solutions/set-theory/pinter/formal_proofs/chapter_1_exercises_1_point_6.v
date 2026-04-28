Theorem exercise_1_6_a : forall (P Q R : Prop), (Q <-> R) -> (P \/ Q <-> P \/ R).
Proof.
  intros P Q R HQR. split.
  * intros [HP | HQ].
    ** left. apply HP.
    ** right. apply HQR. apply HQ.
  * intros [HP | HR].
    ** left. apply HP.
    ** right. apply HQR. apply HR.
Qed.

Theorem exercise_1_6_b : forall (P Q R : Prop), (Q <-> R) -> (P /\ Q <-> P /\ R).
Proof.
  intros P Q R HQR. split.
  * intros [HP HQ]. split.
    ** apply HP.
    ** apply HQR. apply HQ.
  * intros [HP HR]. split.
    ** apply HP.
    ** apply HQR. apply HR.
Qed.

Theorem exercise_1_6_c : forall (P Q R : Prop), (Q <-> R) -> ((P -> Q) <-> (P -> R)).
Proof.
  intros P Q R HQR. split.
  * intros HPQ HP. apply HQR. apply HPQ. apply HP.
  * intros HPR HP. apply HQR. apply HPR. apply HP.
Qed.
