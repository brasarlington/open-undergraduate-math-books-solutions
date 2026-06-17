From OUMBS Require Import Definitions.

Parameter a b c : Class.
Axiom a_set : is_set a.
Axiom b_set : is_set b.
Axiom c_set : is_set c.

Definition r := Pair a b.
Definition s := Pair b c.
Definition p := Pair r s.

Definition P_r := PowerSet r.
Definition P_P_r := PowerSet (PowerSet r).
Definition P_u_r := PowerSet (GenUnion p).
