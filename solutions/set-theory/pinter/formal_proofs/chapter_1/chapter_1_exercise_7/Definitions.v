Parameter Class : Type.

Parameter In : Class -> Class -> Prop.

Definition is_set (X : Class) : Prop := exists Y : Class, In X Y.

Definition proper_class (X : Class) : Prop := ~ is_set X.

Definition subclass (A B : Class) : Prop := forall x, is_set x -> In x A -> In x B.

Axiom A1_extent : forall A B, 
  (forall x, is_set x -> (In x A <-> In x B)) -> A = B.

Parameter Intersection: Class -> Class -> Class.
Axiom inter_def : forall A B x, is_set x -> (In x (Intersection A B) <-> In x A /\ In x B).

Parameter Union: Class -> Class -> Class.
Axiom union_def : forall A B x, is_set x -> (In x (Union A B) <-> In x A \/ In x B).

Parameter Diff: Class -> Class -> Class.
Axiom diff_def : forall A B x, is_set x -> (In x (Diff A B) <-> In x A /\ ~(In x B)).

Axiom A3_subclass_set : forall A B, is_set A -> subclass B A -> is_set B.
Parameter Plus: Class -> Class -> Class. Axiom plus_def : forall A B x, is_set x -> 
  (In x (Plus A B) <-> In x (Union (Diff A B) (Diff B A))).

Parameter Empty : Class.
Axiom empty_def : forall x, is_set x -> ~(In x Empty).
Axiom A4_empty_set : is_set Empty.

Parameter Singleton : Class -> Class.
Axiom singleton_def : forall a x, is_set x -> In x (Singleton a) <-> x = a.

Parameter Pair : Class -> Class -> Class.
Axiom pair_def : forall a b x, is_set x -> (In x (Pair a b) <-> x = a \/ x = b).
Axiom A5_pair_set : forall a b, is_set a -> is_set b -> is_set (Pair a b).

Parameter GenUnion : Class -> Class.
Axiom gen_union_def : forall A x, is_set x -> 
  (In x (GenUnion A) <-> exists Y, is_set Y /\ In Y A /\ In x Y).
Axiom A6_gen_union_set : forall A, is_set A -> is_set (GenUnion A).

Parameter GenInter : Class -> Class.
Axiom gen_inter_def : forall A x, is_set x ->
  (In x (GenInter A) <-> (forall Y, is_set Y -> In Y A -> In x Y)).

Parameter PowerSet : Class -> Class.
Axiom power_def : forall A x, is_set x -> (In x (PowerSet A) <-> subclass x A).
Axiom A7_power_set : forall A, is_set A -> is_set (PowerSet A).

Axiom A8_foundation : forall A, is_set A -> A <> Empty -> 
  exists a, In a A /\ (Intersection a A = Empty).

Parameter Universal : Class.
Axiom universal_def : forall x, is_set x -> (In x Universal <-> True).

Parameter Russell : Class.
Axiom russell_def : forall x, is_set x -> (In x Russell <-> ~(In x x)).

Definition OPair (a b : Class) : Class := Pair (Pair a a) (Pair a b).

Parameter Inv : Class -> Class.
Axiom inv_def : forall G w, is_set w ->
  (In w (Inv G) <-> exists x y, 
      is_set x /\ 
      is_set y /\ 
      w = OPair y x /\ 
      In (OPair x y) G).

Parameter Comp : Class -> Class -> Class.
Axiom comp_def : forall G H w, is_set w ->
  (In w (Comp G H) <-> exists x y z, 
      is_set x /\ 
      is_set y /\ 
      is_set z /\ 
      w = OPair x z /\ 
      In (OPair x y) H /\ 
      In (OPair y z) G).

Parameter Dom : Class -> Class.
Axiom dom_def : forall R x, is_set x ->
  (In x (Dom R) <-> exists y, is_set y /\ In (OPair x y) R).

Parameter Ran : Class -> Class.
Axiom ran_def : forall R y, is_set y ->
  (In y (Ran R) <-> exists x, is_set x /\ In (OPair x y) R).

Parameter CartProd : Class -> Class -> Class.
Axiom cart_prod_def : forall A B w, is_set w ->
  (In w (CartProd A B) <-> exists x y, 
      is_set x /\ 
      is_set y /\ 
      w = OPair x y /\ 
      In x A /\ 
      In y B).

(* Theorems for all *)
Theorem diff_is_subclass : forall (A B : Class), subclass (Diff A B) A.
Proof.
  unfold subclass. intros. apply diff_def in H0.
  ** apply H0.
  ** apply H.
Qed.

Theorem union_subclass_genunion : forall (A B : Class),
  is_set A ->
  is_set B ->
  subclass (Union A B) (GenUnion (Pair A B)).
Proof.
  unfold subclass. intros. apply union_def in H2.
  * apply gen_union_def.
    ** apply H1.
    ** destruct H2.
       *** exists A. split; try split.
           **** apply H.
           **** apply pair_def. apply H. left. reflexivity.
           **** apply H2.
       *** exists B. split; try split.
           **** apply H0.
           **** apply pair_def. apply H0. right. reflexivity.
           **** apply H2.
  * apply H1.
Qed.

Theorem Plus_subclass_union : forall (A B : Class),
  subclass (Plus A B) (Union A B).
Proof.
  unfold subclass. intros.
  apply plus_def in H0.
  * apply union_def in H0.
    ** apply union_def. apply H. destruct H0.
       *** apply diff_def in H0. left. apply H0. apply H.
       *** apply diff_def in H0. right. apply H0. apply H.
    ** apply H.
  * apply H.
Qed.

Theorem union_is_set : forall (A B : Class),
  is_set A ->
  is_set B ->
  is_set (Union A B).
Proof.
  intros.
  apply (A3_subclass_set (GenUnion (Pair A B)) (Union A B)).
  ** apply A6_gen_union_set.
     apply A5_pair_set. apply H. apply H0.
  ** apply union_subclass_genunion. apply H. apply H0.
Qed.

Theorem opair_is_set : forall (A B : Class),
  is_set A ->
  is_set B ->
  is_set (OPair A B).
Proof.
  intros. unfold OPair.
  apply A5_pair_set.
  * apply A5_pair_set; apply H.
  * apply A5_pair_set. apply H. apply H0.
Qed.

Theorem subclass_cartprod_power_power : forall (A B : Class),
  subclass (CartProd A B) (PowerSet (PowerSet (Union A B))).
Proof.
  intros.
  unfold subclass. intros. apply cart_prod_def in H0.
  - destruct H0 as [n1 [n2 [H1 [H2 [H3 [H4 H5]]]]]]. rewrite H3.
    unfold OPair. apply power_def.
    ** apply A5_pair_set; apply A5_pair_set; try apply H1; apply H2. 
    ** unfold subclass. intros. apply pair_def in H6.
      *** destruct H6 as [H6 | H6].
        **** apply power_def. apply H0. rewrite H6. unfold subclass. intros.
            apply pair_def in H8. apply union_def. apply H7. destruct H8. left.
            rewrite H8. apply H4. left. rewrite H8. apply H4. apply H7.
        **** apply power_def. apply H0. unfold subclass. intros. rewrite H6 in H8. apply pair_def in H8. destruct H8.
            ***** apply union_def. apply H7. left. rewrite H8. apply H4.
            ***** apply union_def. apply H7. right. rewrite H8. apply H5.
            ***** apply H7.
      *** apply H0.
  - apply H.
Qed.

Theorem cart_prod_is_set : forall (A B : Class),
  is_set A ->
  is_set B ->
  is_set (CartProd A B).
Proof.
  intros.
  apply (A3_subclass_set (PowerSet (PowerSet (Union A B))) (CartProd A B)).
  - apply A7_power_set. apply A7_power_set.
    apply union_is_set. apply H. apply H0.
  - apply subclass_cartprod_power_power.
Qed.

Lemma element_means_pair_in_power : forall (x A : Class),
  In x A ->
  In (Pair x x) (PowerSet A).
Proof.
  intros.
  assert (H0: is_set x) by (exists A; apply H).
  apply power_def.
  apply A5_pair_set; apply H0.
  unfold subclass. intros. apply pair_def in H2.
  destruct H2; rewrite H2; apply H. apply H1.
Qed.

Theorem pair_in_m : forall (x A : Class),
  is_set x ->
  In (Pair x x) (PowerSet A) ->
  In x A.
Proof.
  intros. apply power_def in H0. unfold subclass in H0.
  assert (Haux: In x (Pair x x)). {
    apply pair_def. apply H. left. reflexivity.
  }
  apply (H0 x H Haux).
  apply A5_pair_set; apply H.
Qed.

Theorem pair_in_power : forall (x A : Class),
  is_set x ->
  In x (Pair A A) ->
  In x (PowerSet A).
Proof.
  intros. apply pair_def in H0. destruct H0.
  * apply power_def. apply H. rewrite H0. unfold subclass. intros. apply H2.
  * apply power_def. apply H. rewrite H0. unfold subclass. intros. apply H2.
  * apply H.
Qed.

Lemma PowerSet_Empty_eq : forall x, is_set x -> In x (PowerSet Empty) -> x = Empty.
Proof.
  intros.
  apply A1_extent. intros. split.
  - intros. apply power_def in H0. apply H0 in H2. apply H2. apply H1. apply H.
  - intros. apply empty_def in H1. contradiction.
Qed.

Lemma Empty_in_Power : forall A, In Empty (PowerSet A).
Proof.
  intros. apply power_def. apply A4_empty_set. unfold subclass. intros.
  apply empty_def in H. contradiction.
Qed.

Lemma all_in_power : forall A, is_set A -> In A (PowerSet A).
Proof.
  intros. apply power_def. apply H. unfold subclass. intros. apply H1.
Qed.
