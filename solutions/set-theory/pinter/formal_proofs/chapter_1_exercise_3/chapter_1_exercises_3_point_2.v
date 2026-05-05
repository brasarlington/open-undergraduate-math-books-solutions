From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.

(**
classic is simply the excluded middle principle and is used where because we would like to not use Axioms freely (even thou we know they don't break Rocq's Universe) because the possibility of breaking the correctness is considerable.
 *)

Theorem exercise_3_2 : forall (U : Type) (A B : Ensemble U),
  Complement U (Intersection U A B) = Union U (Complement U A) (Complement U B).
Proof.
  intros U A B.
  apply Extensionality_Ensembles.
  unfold Same_set, Included.
  split.
  * unfold In, Complement. intros u H. destruct (classic (In U A u)).
    ** destruct (classic (In U B u)).
       *** exfalso. apply H. constructor. apply H0. apply H1.
       *** apply Union_intror. apply H1.
    ** apply Union_introl. apply H0.
  * unfold In, Complement. intros u H H_in. inversion H_in. destruct H.
    ** destruct H. apply H0.
    ** destruct H. apply H1.
Qed.
