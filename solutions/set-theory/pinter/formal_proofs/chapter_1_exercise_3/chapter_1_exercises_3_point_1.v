From Stdlib Require Import Sets.Ensembles.

Theorem exercise_3_1 : forall (U : Type) (A B : Ensemble U),
  Included U A B <-> Intersection U A B = A.
Proof.
  intros U A B. split.
  * unfold Included. intros H.
    apply Extensionality_Ensembles. unfold Same_set. split.
    ** unfold Included. intros u Hi. destruct Hi. apply H0.
    ** unfold Included. intros u Hi. apply H in Hi as Hi2. split.
       *** apply Hi.
       *** apply Hi2.
  * intros H. unfold Included. intros u Hi. rewrite <- H in Hi. destruct Hi. apply H1.
Qed.
