(** printing  *token* $...LATEX math...$ #...html...# *)
(**
This is basically checking for every possibility. It simply splits the directions and the options and then applies them one by one.
*)
Theorem theorem_1_8_i : forall (P Q: Prop), P \/ Q <-> Q \/ P.
Proof.
  intros P Q. split; intros [H1 | H2].
    ** right. apply H1.
    ** left. apply H2.
    ** right. apply H1.
    ** left. apply H2.
Qed.

(**
Similar to the last point, it splits the possibilities and applies them as needed.
*)

Theorem theorem_1_8_ii : forall (P Q R : Prop),
  P \/  (Q \/ R) <-> (P \/ Q) \/ R.
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

(**
You will become accustomed to the way it works. Simply splitting the possibilities and applying them is basically what is done here.
*)

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

(**
One important note in this exercise (one that I strongly recommend looking into) is the use of %;% in this proof. When you use it after opening different branches, it applies the command in both branches (really cool for solving many problems at the same time).
*)

Theorem theorem_1_8_iv : forall (P : Prop), P \/ P <-> P.
Proof.
  intros P. split.
  * intros [HP | HP]; apply HP.
  * intros HP; left; apply HP.
Qed.

(**
As before, it is simply applying every option. Note that it is simply reversing the order of application.
*)

Theorem theorem_1_8_i' : forall (P Q: Prop), P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  * intros [HP HQ]. split. apply HQ. apply HP.
  * intros [HQ HP]. split. apply HP. apply HQ.
Qed.

(**
You can (and I actually did) try to simplify this proof with %;% and %try%, however it is uglier and more convoluted that way.
*)

Theorem theorem_1_8_ii' : forall (P Q R : Prop), P /\  (Q /\ R) <-> (P /\ Q) /\ R.
Proof.
  intros P Q R. split.
  * intros [HP [HQ HR]]. split. split. apply HP. apply HQ. apply HR.
  * intros [[HP HQ] HR]. split. apply HP. split. apply HQ. apply HR.
Qed.

(**
It is in the same direction as every other proof in this first exercise. Simply working every possibility.
*)

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

(**
We are ignoring one of the hypotheses because it doesn't add anything to have two hypotheses which both simply state that P is true.
*)

Theorem theorem_1_8_iv' : forall (P : Prop), P /\ P <-> P.
Proof.
  intros P. split.
  * intros [HP _].
    apply HP.
  * intros HP. split; apply HP.
Qed.
