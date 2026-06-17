From Stdlib Require Import Sets.Ensembles.

Inductive U : Set :=
  | a | b | c | d
  | one | two | three
  | x | y | z.

Definition A : Ensemble U := fun p => match p with
                                      | a | b | c | d => True
                                      | _ => False
                                      end.

Definition B : Ensemble U := fun p => match p with
                                      | one | two | three => True
                                      | _ => False
                                      end.

Definition C : Ensemble U := fun p => match p with
                                      | x | y | z => True
                                      | _ => False
                                      end.

Definition prod {T1 T2 : Type } (X : Ensemble T1) (Y : Ensemble T2) : Ensemble (T1 * T2) :=
  fun p => In T1 X (fst p) /\ In T2 Y (snd p).

Definition AxB_expected : Ensemble (U * U) := 
  fun p => match p with
           | (a, one) | (a, two) | (a, three) => True
           | (b, one) | (b, two) | (b, three) => True
           | (c, one) | (c, two) | (c, three) => True
           | (d, one) | (d, two) | (d, three) => True
           | _ => False
           end.

Theorem AxB : AxB_expected = prod A B.
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, prod, AxB_expected. split.
  * intros [u v] H. unfold In, A, B.
    destruct u,v; simpl; try contradiction; split; exact I.
  * intros [u v] [HA HB]. unfold In, A, B in *.
    destruct u,v; simpl; try contradiction; split; exact I.
Qed.

Definition BxA_expected : Ensemble (U * U) := 
  fun p => match p with
           | (one, a) | (two, a) | (three, a) => True
           | (one, b) | (two, b) | (three, b) => True
           | (one, c) | (two, c) | (three, c) => True
           | (one, d) | (two, d) | (three, d) => True
           | _ => False
           end.

Theorem BxA : BxA_expected = prod B A.
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, prod, BxA_expected. split.
  * intros [u v] H. unfold In, A, B in *.
    destruct u,v; simpl; try contradiction; split; exact I.
  * intros [u v] [HA HB]. unfold In, A, B in *.
    destruct u,v; simpl; try contradiction; split; exact I.
Qed.

Definition Cx_BxA_expected : Ensemble (U * (U * U)) := 
  fun p => match p with
           | (x, ba) => BxA_expected ba
           | (y, ba) => BxA_expected ba
           | (z, ba) => BxA_expected ba
           | _ => False
           end.

Theorem Cx_BxA : Cx_BxA_expected = prod C (prod B A).
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, prod, Cx_BxA_expected, BxA_expected. split.
  * intros [u [v1 v2]] H. unfold In, A, B in *.
    destruct u,v1,v2; simpl; try contradiction; split; split; exact I.
  * intros [u [v1 v2]] [HA [HB1 HB2]]. unfold In, A, B in *.
    destruct u,v1,v2; simpl; try contradiction; exact I.
Qed.

Definition AuBxC_expected : Ensemble (U * U) := 
  fun p => match p with
           | (a, x) | (a, y) | (a, z) => True
           | (b, x) | (b, y) | (b, z) => True
           | (c, x) | (c, y) | (c, z) => True
           | (d, x) | (d, y) | (d, z) => True
           | (one, x) | (one, y) | (one, z) => True
           | (two, x) | (two, y) | (two, z) => True
           | (three, x) | (three, y) | (three, z) => True
           | _ => False
           end.

Theorem AuBxC : AuBxC_expected = prod (Union U A B) C.
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, prod, AuBxC_expected. split.
  * intros [u v] H. unfold In, A, B in *.
    destruct u,v; simpl; try contradiction; destruct H; split; try reflexivity.
    all: (apply Union_introl; reflexivity)||(apply Union_intror; reflexivity).
  * intros [u v] H. unfold In, A, B in *. destruct H. simpl in H. destruct H;
    destruct x0,v; simpl; try contradiction; exact I.
Qed.

Definition AxCuBxC_expected : Ensemble (U * U) :=
  fun p => match p with
           | (a, x) | (a, y) | (a, z) => True
           | (b, x) | (b, y) | (b, z) => True
           | (c, x) | (c, y) | (c, z) => True
           | (d, x) | (d, y) | (d, z) => True
           | (one, x) | (one, y) | (one, z) => True
           | (two, x) | (two, y) | (two, z) => True
           | (three, x) | (three, y) | (three, z) => True
           | _ => False
           end.

Theorem AxCuBXC : AxCuBxC_expected = Union (U * U) (prod A C) (prod B C).
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, prod, AxCuBxC_expected. split.
  * intros [u v] H. unfold In, A, B, C in *.
  destruct u,v; simpl; try contradiction; destruct H; try reflexivity.
  all: (apply Union_introl; unfold In; simpl; split; reflexivity) || (apply Union_intror; unfold In; simpl; split; reflexivity).
  * intros [u v] H. unfold In, A, B, C in *; destruct u,v; simpl in H; inversion H; subst; try contradiction; destruct H0; simpl in *; try contradiction; try reflexivity.
Qed.

Definition AuBxBuC_expected : Ensemble (U * U) :=
  fun p => match p with
           | (a, one) | (a, two) | (a, three) => True
           | (b, one) | (b, two) | (b, three) => True
           | (c, one) | (c, two) | (c, three) => True
           | (d, one) | (d, two) | (d, three) => True
           | (a, x) | (a, y) | (a, z) => True
           | (b, x) | (b, y) | (b, z) => True
           | (c, x) | (c, y) | (c, z) => True
           | (d, x) | (d, y) | (d, z) => True
           | (one, one) | (one, two) | (one, three) => True
           | (two, one) | (two, two) | (two, three) => True
           | (three, one) | (three, two) | (three, three) => True
           | (one, x) | (one, y) | (one, z) => True
           | (two, x) | (two, y) | (two, z) => True
           | (three, x) | (three, y) | (three, z) => True
           | _ => False
           end.

Theorem AuBxBuC : AuBxBuC_expected = prod (Union U A B) (Union U B C).
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, prod, AuBxBuC_expected. split.
  * intros [u v] H. unfold In, A, B, C in *.
    destruct u,v; simpl; try contradiction; destruct H; split; try reflexivity.
    all: (apply Union_introl; reflexivity)||(apply Union_intror; reflexivity).
  * intros [u v] [H1 H2]. unfold In, A, B, C in *; destruct u,v; simpl in *; inversion H1; inversion H2; subst; try contradiction; try reflexivity.
Qed.
