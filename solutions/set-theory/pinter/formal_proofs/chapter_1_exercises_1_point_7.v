Theorem exercise_1_7_a : forall (P Q R S : Prop), (P -> Q) -> (R -> S) -> (P \/ R -> Q \/ S).
Proof.
  intros P Q R S HPQ HRS [HP | HR].
  * apply HPQ in HP. left. apply HP.
  * apply HRS in HR. right. apply HR.
Qed.

Theorem exercise_1_7_b : forall (P Q R S : Prop), (P -> Q) -> (R -> S) -> (P /\ R -> Q /\ S).
Proof.
  intros P Q R S HPQ HRS [HP HR]. split.
  * apply HPQ. apply HP.
  * apply HRS. apply HR.
Qed.
