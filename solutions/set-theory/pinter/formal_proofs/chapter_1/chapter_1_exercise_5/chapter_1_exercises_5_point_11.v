From Stdlib Require Import Sets.Ensembles.
From OUMBS Require Import Graphs.

Theorem exercise_11_a : forall (U V : Type) (G : Graph U V) (B : Ensemble U),
  Restriction_ran G B = ran (Restriction G B).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, dom, ran, Restriction_ran, In in *. split.
  - intros v [u [HG HB]]. exists u. split. apply HG. apply HB.
  - intros v [u [HG HB]]. exists u. split. apply HG. apply HB.
Qed.

Theorem exercise_11_b : forall (U V : Type) (G : Graph U V) (B C : Ensemble U),
  Restriction_ran G (Union U B C) = Union V (Restriction_ran G B) (Restriction_ran G C).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, In, dom, ran, Restriction_ran, In in *. split.
  - intros v [u [HG HUBC]]. remember u. destruct HUBC; subst.
    ** apply Union_introl. exists u. split. apply HG. apply H.
    ** apply Union_intror. exists u. split. apply HG. apply H.
  - intros v H. remember v. destruct H; destruct H; subst.
    ** exists x0. split. apply H. apply Union_introl. apply H.
    ** exists x0. split. apply H. apply Union_intror. apply H.
Qed.

(**
There is no way to demonstrate the book assertion because it is false. Because in general every image can have many domain_points pointing at them the result would not hold that if a point is in the intersection of images then it must be in the image of the intersection of points. One small counterexample would be

G := {(b, a), (c, a)}
B := {b}
C := {c}
G(B \cap C) = G(\empty) = \empty
G(B) \cap G(C) = {a: \exists b \in B; (b, a) \in G} \cap {a: \exists c \in C; (c, a) \in G} = {a}

There is no equality in this case. Therefore working as a counterexample. One direction is valid thou and therefore we will correct it to only consider one.
 *)

Lemma exercise_11_c_false :
  ~ (forall (U V : Type) (G : Graph U V) (B C : Ensemble U),
       Restriction_ran G (Intersection U B C) =
       Intersection V (Restriction_ran G B) (Restriction_ran G C)).
Proof.
  intros H.
  (* The same counterexample as above but with the already defined types in Rocq *)
  pose (B := fun x : bool => x = true).
  pose (C := fun x : bool => x = false).
  pose (G := fun p : bool * unit => (fst p = true \/ fst p = false) /\ snd p = tt).
  specialize (H bool unit G B C).
  assert (In unit (Restriction_ran G (Intersection bool B C)) tt) as Hempty.
  {
    rewrite H.
    split; [exists true | exists false];
        unfold In, B, C, G; simpl; auto.
  } 
  destruct Hempty. destruct H0. unfold B, C, In in *. destruct H1. inversion H1. inversion H2. subst. inversion H4.
Qed.


Theorem exercise_11_c_Corrected : forall (U V : Type) (G : Graph U V) (B C : Ensemble U),
  Included V (Restriction_ran G (Intersection U B C)) (Intersection V (Restriction_ran G B) (Restriction_ran G C)).
Proof.
  intros.
  unfold Same_set, Included, In, dom, ran, Restriction_ran, In in *.
  - intros v [u [HG HC]]. destruct HC. split.
    ** exists x. split. apply HG. apply H.
    ** exists x. split. apply HG. apply H0.
Qed.

Theorem exercise_11_d : forall (U V : Type) (G : Graph U V) (B C : Ensemble U),
  Included U B C ->
  Included V (Restriction_ran G B) (Restriction_ran G C).
Proof.
  intros.
  unfold Included, Restriction_ran, In in *.
  intros v H0. destruct H0 as [u [HG HB]]. apply H in HB. exists u. split. apply HG. apply HB.
Qed.
