(* 
This exercise is basically imposible in Coq. It actually fails with Universe Inconsistency from the beggining protecting the Russel paradox.
*)

From Stdlib Require Import Sets.Ensembles.

Fail Definition Russell_Set := 
  let U := Type in
  let S : Ensemble U := fun (x : U) => ~ In U x x in
  S.
