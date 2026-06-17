From Stdlib Require Import Sets.Ensembles.

Inductive Element := u | v | w | x | y.

Definition A : Ensemble Element :=
  fun e : Element => match e with
  | u | v | w => True
  | _ => False
  end.

Definition B : Ensemble Element :=
  fun e : Element => match e with
  | w | x => True
  | _ => False
  end.

Definition C : Ensemble Element :=
  fun e : Element => match e with
  | w | y => True
  | _ => False
  end.

Definition R : Ensemble (Ensemble Element) :=
  fun p : (Ensemble Element) => p = A \/ p = B.

Definition S : Ensemble (Ensemble Element) :=
  fun p : (Ensemble Element) => p = B \/ p = C.

Definition P : Ensemble (Ensemble (Ensemble Element)) :=
  fun p : (Ensemble (Ensemble Element)) => p = R \/ p = S.

Theorem A_neq_B : A <> B.
Proof.
  intros HAB.
  assert (H: In Element A x) by (rewrite HAB; reflexivity).
  unfold A, In in H. apply H.
Qed.

Theorem A_neq_C : A <> C.
Proof.
  intros HAB.
  assert (H: In Element A y) by (rewrite HAB; reflexivity).
  unfold A, In in H. apply H.
Qed.

Theorem B_neq_C : B <> C.
Proof.
  intros HAB.
  assert (H: In Element B y) by (rewrite HAB; reflexivity).
  unfold B, In in H. apply H.
Qed.

(* Operation Definitions *)

Definition General_Union
  { U : Type } (A : Ensemble (Ensemble U)) : Ensemble U
  := fun (p : U) => exists (B : Ensemble U), In (Ensemble U) A B /\ In U B p.

Definition General_Intersection
  { U : Type } (A : Ensemble (Ensemble U)) : Ensemble U
  := fun (p : U) => forall (B : Ensemble U), In (Ensemble U) A B -> In U B p.

(* Exercise *)
Definition U_U_P_Expected : Ensemble Element :=
  fun e : Element => match e with
  | u | v | w | x | y => True
  end.

Theorem U_U_P : U_U_P_Expected = General_Union (General_Union P).
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, General_Union, In, P in *. split.
  - intros. destruct x0.
    ** exists A. split.
      *** exists R. split. left. reflexivity. unfold R. left. reflexivity.
      *** reflexivity.
    ** exists A. split.
      *** exists R. split. left. reflexivity. unfold R. left. reflexivity.
      *** reflexivity.
    ** exists A. split.
      *** exists R. split. left. reflexivity. unfold R. left. reflexivity.
      *** reflexivity.
    ** exists B. split.
      *** exists R. split. left. reflexivity. unfold R. right. reflexivity.
      *** reflexivity.
    ** exists C. split.
      *** exists S. split. right. reflexivity. unfold S. right. reflexivity.
      *** reflexivity.
  - intros. destruct x0; try reflexivity.
Qed.

Definition n_n_P_Expected : Ensemble Element :=
  fun e : Element => match e with
  | w | x => True
  | _ => False
  end.

Theorem n_n_P : n_n_P_Expected = General_Intersection (General_Intersection P).
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, General_Intersection, In, P in *. split.
  - intros. destruct x0; simpl in H; try destruct H;
    assert (HRB0: In (Ensemble Element) R B0)
      by (apply H0; left; reflexivity);
    assert (HSB0: In (Ensemble Element) S B0)
      by (apply H0; right; reflexivity);
    destruct HRB0; destruct HSB0; subst B0;
    try (apply A_neq_B; try discriminate; apply H1);
    try (apply A_neq_C; try discriminate; apply H1);
    simpl; try reflexivity.
  - intros. specialize H with B.
    assert (Haux: B x0). {
      apply H. intros. destruct H0.
        ** rewrite H0. unfold R. right. reflexivity.
        ** rewrite H0. unfold S. left. reflexivity.
  } destruct x0; simpl in *; try destruct Haux; try reflexivity.
Qed.

Definition u_n_P_Expected : Ensemble Element :=
  fun e : Element => match e with
  | w | x => True
  | _ => False
  end.

Theorem u_n_P : u_n_P_Expected = General_Union (General_Intersection P).
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, General_Union, General_Intersection, In, P, R, S in *.
  split.
  - intros. exists B. split.
    ** intros. destruct H0.
      *** rewrite H0. right. reflexivity.
      *** rewrite H0. left. reflexivity.
    ** destruct x0; try (simpl in *; destruct H; reflexivity).
  - intros e He. destruct He as [B0 [HB0 HeB0]].
    assert (HRB0 : In (Ensemble Element) R B0).
    { apply HB0. left. reflexivity. }
    assert (HSB0 : In (Ensemble Element) S B0).
    { apply HB0. right. reflexivity. }
    unfold R, S, In in *. destruct HRB0; destruct HSB0.
      ** rewrite H0 in HeB0. destruct e;
        try simpl in HeB0; try destruct HeB0; try simpl; try reflexivity.
      **  rewrite H in H0. apply A_neq_C in H0. destruct H0.
      ** rewrite H0 in HeB0. destruct e;
        try simpl in HeB0; try destruct HeB0; try simpl; try reflexivity.
      ** rewrite H in H0. apply B_neq_C in H0. destruct H0.
Qed.

Theorem A_in_U_P : In (Ensemble Element) (General_Union P) A.
Proof.
  exists R; split; [left; reflexivity | left; reflexivity].
Qed.

Theorem B_in_U_P : In (Ensemble Element) (General_Union P) B.
Proof.
    exists R; split; [left; reflexivity | right; reflexivity].
Qed.

Definition n_u_P_Expected : Ensemble Element :=
  fun e : Element => match e with
  | w => True
  | _ => False
  end.

Theorem n_u_P : n_u_P_Expected = General_Intersection (General_Union P).
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, General_Union, General_Intersection, In, P, R, S in *.
  split.
  - intros.
    destruct x0; simpl in H; destruct H. destruct H0. destruct H; destruct H;
      rewrite H in H0; destruct H0; rewrite H0; simpl; reflexivity.
  - intros.
    assert (HA: In (Ensemble Element) (General_Union P) A) by (apply A_in_U_P).
    assert (HB: In (Ensemble Element) (General_Union P) B) by (apply B_in_U_P).
    destruct x0; simpl; auto.
    **
      apply H in HB. unfold B, In in HB. destruct HB.
    **
      apply H in HB. unfold B, In in HB. destruct HB.
    **
      apply H in HA; unfold A, In in HA; simpl in HA; apply HA.
    **
      apply H in HA; unfold A, In in HA; simpl in HA; apply HA.
Qed.
