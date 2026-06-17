From Stdlib Require Import Sets.Ensembles.

Definition Indexed_Family (Index A : Type) : Type := Ensemble (Index * A).

Definition General_Union {Index A : Type} (G : Indexed_Family Index A)
  : Ensemble A :=
  fun (p : A) => exists (j : Index), In (Index * A) G (j, p).

Definition General_Intersection {Index A : Type} (G : Indexed_Family Index A) : Ensemble A :=
  fun (p : A) => forall (i : Index), In (Index * A) G (i, p).

Definition Limit {Index A : Type} (G : Indexed_Family Index A) (i : Index) : Ensemble A :=
  fun (p : A) => In (Index * A) G (i, p).

Definition Indexed_Range {I U V : Type} (G : Indexed_Family I (U*V)) : Indexed_Family I V :=
  fun (p : I * V) => exists (x : U), G (fst p, (x, snd p)).

Definition Product_Family {I J U : Type} (A : Indexed_Family I U) (B : Indexed_Family J U) : Indexed_Family (I * J) U :=
  fun (p : (I * J) * U) =>
    match p with
    | ((i, j), u) => In (I * U) A (i, u) \/ In (J * U) B (j, u)
    end.

Definition Product_Family_Intersection {I J U : Type} (A : Indexed_Family I U) (B : Indexed_Family J U) : Indexed_Family (I * J) U :=
  fun (p : (I * J) * U) =>
    match p with
    | ((i, j), u) => In (I * U) A (i, u) /\ In (J * U) B (j, u)
    end.

Definition Product_Family_Complete {I J U V : Type} (A : Indexed_Family I U) (B : Indexed_Family J V) : Indexed_Family (I * J) (U * V) :=
  fun (p : (I * J) * (U * V)) =>
    match p with
    | ((i, j), (u, v)) => In (I * U) A (i, u) /\ In (J * V) B (j, v)
    end.

Definition Union_Family {I J U : Type}
  (A : Indexed_Family I U) (B : Indexed_Family J U) : Indexed_Family (I + J) U :=
  fun (p : (I+J) * U) =>
    match p with
    | (inl i, u) => In (I*U) A (i, u)
    | (inr j, u) => In (J*U) B (j, u)
    end.

Definition Covering {I U : Type} (A : Ensemble U) (B : Indexed_Family I U) : Prop :=
  Included U A (General_Union B).
