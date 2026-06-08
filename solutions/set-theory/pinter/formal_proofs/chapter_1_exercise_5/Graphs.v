From Stdlib Require Import Sets.Ensembles.

Definition Graph (U V : Type) : Type := Ensemble (U * V).

Definition Inverse {U V : Type} (G : Ensemble (U * V)) : Graph V U :=
  fun p => G (snd p, fst p).

Definition Compose {U V W : Type} (R : Ensemble (U * V)) (S : Ensemble (W * U)) : Graph W V :=
  fun p => match p with (x, z) => exists (y : U) , S (x, y) /\ R (y, z) end.

Definition dom {U V : Type} (G : Graph U V)  : Ensemble U :=
  fun (p : U) => match p with x => exists (y : V), In (U * V) G (x, y) end.

Definition ran {U V : Type} (G : Graph U V)  : Ensemble V :=
  fun (p : V) => match p with y => exists (x : U), In (U * V) G (x, y) end.

Definition prod {T1 T2 : Type } (X : Ensemble T1) (Y : Ensemble T2) : Ensemble (T1 * T2) :=
  fun p => In T1 X (fst p) /\ In T2 Y (snd p).

Definition Restriction {U V : Type} (G : Graph U V) (B : Ensemble U)
  := fun p => match p with (x, y) => In (U * V) G (x, y) /\ In U B x end.

Definition Restriction_ran {U V : Type} (G : Graph U V) (B : Ensemble U)
  := fun p => match p with y => exists x : U, In (U * V) G (x, y) /\ In U B x end.
