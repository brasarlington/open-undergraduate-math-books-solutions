From OUMBS Require Import Definitions.

Theorem exercise_3 : proper_class Russell.
Proof.
  unfold proper_class.
  intros HR.
  apply russell_def in HR as contra.
  tauto.
Qed.
