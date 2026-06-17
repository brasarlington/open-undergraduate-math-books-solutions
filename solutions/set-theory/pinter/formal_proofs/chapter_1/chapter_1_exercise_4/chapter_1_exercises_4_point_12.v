From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Logic.Classical.

Lemma in_couple_means_in_singleton : forall (U : Type) (a b c : U),
  In U (Couple U a b) c <-> In U (Singleton U a) c \/ In U (Singleton U b) c.
Proof.
  intros. split.
  * intros. inversion H. 
    ** left. apply In_singleton.
    ** right. apply In_singleton.
  * intros [H | H].
    ** inversion H. apply Couple_l.
    ** inversion H. apply Couple_r.
Qed.

Lemma eq_couple:
  forall (U : Type) (a b c d : U),
    Couple U a b = Couple U c d <->
    (a = c /\ b = d) \/ (a = d /\ b = c).
Proof.
  intros. split.
  * intros.
    assert (Haux: In U (Couple U c d) a). { rewrite <- H. apply Couple_l. }
    assert (Haux2: In U (Couple U c d) b). { rewrite <- H. apply Couple_r. }
    assert (Haux3: In U (Couple U a b) c). { rewrite H. apply Couple_l. }
    assert (Haux4: In U (Couple U a b) d). { rewrite H. apply Couple_r. }
    inversion Haux; inversion Haux2; inversion Haux3; inversion Haux4;
    try subst;
    try (left; split; reflexivity); try (right; split; reflexivity).
  * intros [[H1 H2] | [H1 H2]].
    ** subst. reflexivity.
    ** apply Extensionality_Ensembles.
       unfold Same_set, Included in *. split;
       intros x Hx; inversion Hx; subst.
       all: apply Couple_r || apply Couple_l.
Qed.

(**
There is no easy way to implement the strict definition recommended from the book in Rocq.

Because it doesn't respect the same type principle. You can in theory create an inductive
type for representing the type itself or a ensemble of the type but the reality is that in simple terms it doesn't work. Something similar (or something along those ways as solicited in the exercise) can be found in the previous exercise but as you can see because the type needs to consider every posibility it is impossible to reduce it in this definition to the one expected.
 *)
Definition ordered_pair {U : Type} (empty : U) (a b: U) : Ensemble (Ensemble U)
  := Couple (Ensemble U) (Couple U a empty) (Couple U empty b).
