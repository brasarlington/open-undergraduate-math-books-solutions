From OUMBS Require Import Definitions.

Theorem exercise_4 : forall (A B : Class),
  is_set A ->
  is_set B ->
  In B A ->
  is_set (GenInter A).
Proof.
  intros.
  apply (A3_subclass_set B (GenInter A)).
  * apply H0.
  * unfold subclass. intros. eapply (gen_inter_def A x H2) in H3 as H4.
    ** apply H4.
    ** apply H0.
    ** apply H1.
Qed.
