From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Logic.Classical_Pred_Type.
From OUMBS Require Import Definitions.
From OUMBS Require Import Graphs.

(* POR HACER, NO SE NI COMO COÑO ESCRIBIRLO *)
Theorem exercise_8_a : forall {I J U : Type} (A : Indexed_Family I U) (B : Indexed_Family J U),
  inhabited J ->
  Setminus U (General_Union A) (General_Union B) =
  General_Union
  (fun (p : I * U) =>
  let (i, x) := p in
  General_Intersection
  (fun (q : J * U) =>
  let (j, y) := q in
  In U (Setminus U (Limit A i) (Limit B j)) y) x).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Setminus, General_Union, General_Intersection, Limit, In in *. split.
  * intros. simpl in *. destruct H. destruct H0. destruct H. exists x0. intros j. split.
    ** apply H.
    ** intros HB. assert (contra: exists j : J, B (j, x)) by (exists j; apply HB). contradiction.
  * intros. destruct H. split. 
    ** destruct H0. exists x0. apply H. apply X.
    ** intros HB. destruct HB. destruct H0. specialize H0 with (i := x0). destruct H0. contradiction.
Qed.

Theorem exercise_8_b : forall {I J U : Type} (A : Indexed_Family I U) (B : Indexed_Family J U),
  inhabited I ->
  Setminus U (General_Intersection A) (General_Intersection B) =
  General_Intersection
  (fun (p : I * U) =>
  let (i, x) := p in
  General_Union
  (fun (q : J * U) =>
  let (j, y) := q in
  In U (Setminus U (Limit A i) (Limit B j)) y) x).
Proof.
  intros I J U A B HI.
  apply Extensionality_Ensembles.
  unfold Same_set, Included, Setminus, General_Union, General_Intersection, Limit, In in *. split.
  - intros. destruct H. apply not_all_ex_not in H0. destruct H0. exists x0. split.
    ** apply H.
    ** intros HB. contradiction.
  -  intros. split.
    ** intros i. specialize H with i. destruct H. apply H.
    ** intros HB. destruct HI. specialize H with X. destruct H. destruct H. specialize HB with x0. contradiction.
Qed.
