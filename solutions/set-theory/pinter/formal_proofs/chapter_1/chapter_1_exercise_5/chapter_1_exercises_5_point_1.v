From Stdlib Require Import Sets.Ensembles.
From OUMBS Require Import Graphs.

Inductive Element := a | b | c | d.

Definition G : Graph Element Element := fun p =>
  match p with
  | (b, b) => True
  | (b, c) => True
  | (c, c) => True
  | _ => False
  end.

Definition H : Graph Element Element := fun p =>
  match p with
  | (b, a) => True
  | (c, b) => True
  | (d, c) => True
  | _ => False
  end.

Definition Inv_G_expected : Graph Element Element := fun p =>
  match p with
  | (b, b) => True
  | (c, b) => True
  | (c, c) => True
  | _ => False
  end.

Theorem Inv_G : Inv_G_expected = Inverse G.
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Inverse, Inv_G_expected, In in *. split;
  intros [x1 x2] H; destruct x1, x2; try contradiction;
    try simpl; try reflexivity.
Qed.

Definition Inv_H_expected : Graph Element Element := fun p =>
  match p with
  | (a, b) => True
  | (b, c) => True
  | (c, d) => True
  | _ => False
  end.

Theorem Inv_H : Inv_H_expected = Inverse H.
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Inverse, Inv_H_expected, In in *. split;
  intros [x1 x2] H; destruct x1, x2; try contradiction;
    try simpl; try reflexivity.
Qed.

Definition Compose {U V W : Type} (R : Graph U V) (S : Graph V W) : Graph U W :=
  fun p => match p with (x, z) => exists y, R (x, y) /\ S (y, z) end.

Definition G_comp_H_expected : Graph Element Element := fun p =>
  match p with
  | (b, a) => True
  | (b, b) => True
  | (c, b) => True
  | _      => False
  end.

Theorem G_comp_H : G_comp_H_expected = Compose G H.
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Inverse, Compose, In in *.
  split.
  * intros [x1 x2] H. destruct x1, x2; try contradiction;
   try (exists a; simpl; split; reflexivity);
   try (exists b; simpl; split; reflexivity);
   try (exists c; simpl; split; reflexivity);
   try (exists d; simpl; split; reflexivity).
  * intros [x1 x2] [z [H1 H2]]. destruct x1, x2, z;
    simpl in *;
    try contradiction;
    try reflexivity.
Qed.

Definition H_comp_G_expected : Graph Element Element := fun p =>
  match p with
  | (c, b) => True
  | (c, c) => True
  | (d, c) => True
  | _      => False
  end.

Theorem H_comp_G : H_comp_G_expected = Compose H G.
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Inverse, Compose, In in *.
  split.
  * intros [x1 x2] H. destruct x1, x2; try contradiction;
    try (exists a; simpl in *; split; reflexivity);
    try (exists c; simpl in *; split; reflexivity);
    try (exists b; simpl in *; split; reflexivity);
    try (exists d; simpl in *; split; reflexivity).
  * intros [x1 x2] [z [H1 H2]]. destruct x1, x2, z;
    try contradiction;
    try reflexivity.
Qed.

Definition Inv_G_comp_H_expected : Graph Element Element := fun p =>
  match p with
  | (a, b) => True
  | (b, b) => True
  | (b, c) => True
  | _      => False
  end.

Theorem Inv_G_comp_H : Inv_G_comp_H_expected = Inverse (Compose G H).
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Inverse, G_comp_H_expected, Compose, In in *.
  split.
  * intros [x1 x2] H. destruct x1, x2; try contradiction;
    try (exists a; simpl in *; split; reflexivity);
    try (exists c; simpl in *; split; reflexivity);
    try (exists b; simpl in *; split; reflexivity);
    try (exists d; simpl in *; split; reflexivity).
  * intros [x1 x2] [z [H1 H2]]. destruct x1, x2, z;
    try contradiction;
    try reflexivity.
Qed.

Definition Inv_G_Union_H_expected : Graph Element Element := fun p =>
  match p with
  | (b, b) => True
  | (c, b) => True
  | (c, c) => True
  | (a, b) => True
  | (b, c) => True
  | (c, d) => True
  | _      => False
  end.

Theorem Inv_G_union_H :
  Inv_G_Union_H_expected = Inverse (Union (Element * Element) G H).
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Inverse, G_comp_H_expected, Compose, In in *.
  split.
  * intros [x1 x2] H. destruct x1, x2; try contradiction;
    try simpl;
    try (apply Union_intror; unfold In; simpl; reflexivity);
    try (apply Union_introl; unfold In; simpl; reflexivity).
  * intros [x1 x2]. simpl. intro H_union.
    remember (x2, x1) as p.
    destruct H_union as [H_G | H_H]; subst.
    ** destruct x1, x2; unfold In in *; simpl in *; try contradiction; try reflexivity.
    ** destruct x1, x2; unfold In in *; simpl in *; try contradiction; try reflexivity.
Qed.

Definition Inv_H__comp_G_expected : Graph Element Element := fun p =>
  match p with
  | (a, b) => True
  | (a, c) => True
  | (b, c) => True
  | _      => False
  end.

Theorem Inv_H__comp_G : Inv_H__comp_G_expected = Compose (Inverse H) G.
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Inverse, G_comp_H_expected, Compose, In in *.
  split.
  * intros [x1 x2] H. destruct x1, x2; try contradiction;
    try (exists a; simpl in *; split; reflexivity);
    try (exists c; simpl in *; split; reflexivity);
    try (exists d; simpl in *; split; reflexivity);
    try (exists b; simpl in *; split; reflexivity).
  * intros [x1 x2] [z [H1 H2]]. destruct x1, x2, z;
    try contradiction; try reflexivity.
Qed.
