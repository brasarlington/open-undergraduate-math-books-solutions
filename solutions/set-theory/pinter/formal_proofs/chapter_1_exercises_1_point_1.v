Theorem theorem_1_8_i : forall (P Q: Prop), P \/ Q <-> Q \/ P.
Proof.
  intros P Q. split; intros [H1 | H2].
    ** right. apply H1.
    ** left. apply H2.
    ** right. apply H1.
    ** left. apply H2.
Qed.

Theorem theorem_1_8_ii : forall (P Q R : Prop), P \/  (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  * intros [HP | [HQ | HR]].
    ** left. left. apply HP.
    ** left. right. apply HQ.
    ** right. apply HR.
  * intros [[HP | HQ] | HR].
    ** left. apply HP.
    ** right. left. apply HQ.
    ** right. right. apply HR.
Qed.

Theorem theorem_1_8_iii : forall (P Q R : Prop), P /\  (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
  intros P Q R. split.
  * intros [HP [HQ | HR]].
    ** left. split. apply HP. apply HQ.
    ** right. split. apply HP.  apply HR.
  * intros[[HP HQ] | [HP HR]].
    ** split. apply HP. left. apply HQ.
    ** split. apply HP. right. apply HR.
Qed.

Theorem theorem_1_8_iv : forall (P : Prop), P \/ P <-> P.
Proof.
  intros P. split.
  * intros [HP | HP]; apply HP.
  * intros HP; left; apply HP.
Qed.

Theorem theorem_1_8_i' : forall (P Q: Prop), P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  * intros [HP HQ]. split. apply HQ. apply HP.
  * intros [HQ HP]. split. apply HP. apply HQ.
Qed.

Theorem theorem_1_8_ii' : forall (P Q R : Prop), P /\  (Q /\ R) <-> (P /\ Q) /\ R.
Proof.
  intros P Q R. split.
  * intros [HP [HQ HR]]. split. split. apply HP. apply HQ. apply HR.
  * intros [[HP HQ] HR]. split. apply HP. split. apply HQ. apply HR.
Qed.

Theorem theorem_1_8_iii' : forall (P Q R : Prop), P \/  (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  * intros [HP | [HQ HR]].
    ** split; left; apply HP.
    ** split; right. apply HQ. apply HR.
  * intros [[HP1 | HQ] [HP2 | HR]].
    ** left. apply HP1.
    ** left. apply HP1.
    ** left. apply HP2.
    ** right. split. apply HQ. apply HR.
Qed.


Theorem theorem_1_8_iv' : forall (P : Prop), P /\ P <-> P.
Proof.
  intros P. split.
  * intros [HP _].
    apply HP.
  * intros HP. split; apply HP.
Qed.
