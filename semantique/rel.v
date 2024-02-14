Axiom extensionality : forall A B (f g: A -> B), (forall a: A, f a = g a) -> f = g.

Axiom indistinguishability : forall P Q: Prop, P = Q <-> (P <-> Q).

Require Setoid.

Definition relation (A B : Type) :=  A -> B -> Prop.

Definition flip (A B : Type) (R : (relation A B)) := fun x y => R y x.

Lemma flip_involution : forall (A B : Type) (R : (relation A B)) (x : A) (y : B),
    R x y <-> (flip B A (flip A B R)) x y.
Proof.
    intros A B R x y.
    split;intro;assumption.
Qed.

Definition before (A B C: Type) (R : (relation A B)) (Q : (relation B C)) (x : A) (z : C) :=
  exists y : B, R x y /\ Q y z.

Definition ID (A : Type) (x y : A) := x = y.

Definition Empty (A B : Type) (x : A) (y : B) := False.
Definition Full (A B : Type) (x : A) (y : B) := True.

Notation "R /> Q" := (before _ _ _ R Q) (at level 80, right associativity).
Notation "^ R" := (flip _ _ R) (at level 79, right associativity).

Lemma before_assoc : forall A B C D (R : (relation A B)) (P : relation B C) (Q : relation C D),
  (R /> P /> Q) = ((R /> P) /> Q).
Proof.
  intros.
  apply extensionality.
  intro.
  apply extensionality.
  intro d.
  rewrite indistinguishability.
  split.
  intros [b [H0 [c [H1 H2]]]].
  exists c.
  split.
  exists b.
  split;
  assumption.
  assumption.
  intros [c [[b [H0 H1]]]].
  exists b.
  split.
  assumption.
  exists c.
  split; assumption.
Qed.

Lemma before_unit_l : forall A B (R : relation A B), ((ID A) /> R) = R.
Proof.
  intros.
  apply extensionality.
  intro.
  apply extensionality.
  intro b.
  rewrite indistinguishability.
  split.
  intros [x [H0 H1]].
  rewrite <- H0 in H1.
  assumption.
  intro H.
  exists a.
  split.
  reflexivity.
  assumption.
Qed.


Lemma before_unit_r : forall A B (R : relation A B), (R /> (ID B)) = R.
Proof.
  intros.
  apply extensionality.
  intro.
  apply extensionality.
  intro b.
  rewrite indistinguishability.
  split.
  intros [x [H0 H1]].
  rewrite H1 in H0.
  assumption.
  intro.
  exists b.
  split.
  assumption.
  reflexivity.
Qed.

Lemma flip_before : forall A B C (R : relation A B) (Q : relation B C),
  forall (a : A) (c : C), (^ (R /> Q)) = ((^ Q) /> (^ R)).
Proof.
  intros.
  apply extensionality.
  intro.
  apply extensionality.
  intro.
  rewrite indistinguishability.
  split;
  intros [b [H0 H1]];
  exists b;
  split; assumption.
Qed.

Lemma flip_id : forall A, (^ (ID A)) = ID A.
Proof.
  intros.
  apply extensionality.
  intro.
  apply extensionality.
  intro.
  rewrite indistinguishability.
  split; intro; (assumption + (symmetry;assumption)).
Qed.


Definition subrelation (A B : Type) (R Q : relation A B) := forall (a : A) (b : B), R a b -> Q a b.

Notation "R <= Q" := (subrelation _ _ R Q).

Lemma subrelation_refl : forall A B (R : relation A B), R <= R.
Proof.
  intros A B R x y.
  intro.
  assumption.
Qed.


Lemma subrelation_trans : forall A B (R P Q : relation A B), R <= P -> P <= Q -> R <= Q.
Proof.
  intros A B R P Q HL HR a b.
  intro.
  apply HR.
  apply HL.
  apply H.
Qed.



Lemma subrelation_antisym : forall A B (R P : relation A B), R <= P -> P <= R -> R = P.
Proof.
  intros A B R P HL HR.
  apply extensionality.
  intro.
  apply extensionality.
  intro b.
  rewrite indistinguishability.
  split.
  intro.
  apply HL.
  assumption.
  intro.
  apply HR.
  assumption.
Qed.

Lemma subrelation_before_left : forall A B C (R1 R2 : relation A B) (Q : relation B C),
  R1 <= R2 -> (R1 /> Q) <= (R2 /> Q).
Proof.
  intros A B C R1 R2 Q H a c [b [HL HR]].
  exists b.
  split.
  apply H.
  assumption.
  assumption.
Qed.

Lemma subrelation_before_right : forall A B C (R : relation A B) (Q1 Q2 : relation B C),
  Q1 <= Q2 -> (R /> Q1) <= (R /> Q2).
Proof.
  intros A B C R Q1 Q2 H a c [b [HL HR]].
  exists b.
  split.
  assumption.
  apply H.
  assumption.
Qed.


Lemma flip_monotone : forall A B (R Q : relation A B),
  R <= Q -> (^ R) <= (^ Q).
Proof.
  intros A B R Q H b a.
  intro.
  apply H.
  assumption.
Qed.

Definition reflexive {A : Type} (R : relation A A) := ID A <= R.
Definition coreflexive {A : Type} (R : relation A A) := R <= ID A .
Definition symmetric {A : Type} (R : relation A A) := (^ R) <= R.
Definition transitive {A : Type} (R : relation A A) := (R /> R) <= R.



Definition surjective {A B : Type} (R : relation A B) := reflexive ((^ R) /> R).
Definition deterministic {A B : Type} (R : relation A B) := coreflexive ((^ R) /> R).
Definition injective {A B : Type} (R : relation A B) := coreflexive (R /> (^ R)).
Definition full {A B : Type} (R : relation A B) := reflexive (R /> (^ R)).




Lemma surjective_before : forall A B C (R : relation A B) (Q : relation B C),
  surjective R /\ surjective Q -> surjective (R /> Q).
Proof.
  intros A B C R Q [sR sQ].
  unfold surjective, reflexive.
  rewrite flip_before.
  rewrite <- before_assoc.
  unfold surjective, reflexive in sQ.
  rewrite <- (before_unit_l B C Q) in sQ.


Admitted.




(*Chapter unions, intersections*)

Definition union {A B : Type} (R Q : relation A B) (a : A) (b : B) :=
  R a b \/ Q a b.

Definition unbounded_union {A B I: Type} (f : I -> relation A B) (a : A) (b : B) :=
  exists i : I, f i a b.

Definition intersect {A B : Type} (R Q : relation A B) (a : A) (b : B) :=
  R a b /\ Q a b.

Definition unbounded_intersection {A B I: Type} (f : I -> relation A B) (a : A) (b : B) :=
  forall i : I, f i a b.

Notation "R +/ Q" := (union R Q) (at level 50).
Notation "R */ Q" := (intersect R Q) (at level 50).

Definition op_intersection {A} (R : relation A A) := (^ R) */ R.

Definition antisymmetric {A : Type} (R : relation A A) := coreflexive (op_intersection R).

Lemma intersection_less_than_before_right : forall A B C (R : relation A B) (P Q : relation B C),
  (R /> (P */ Q)) <= ((R /> P) */ (R /> Q)).
Proof.
  intros A B C R P Q a c [b [H0 [H1 H2]]].
  split.
  exists b.
  split; assumption.
  exists b.
  split; assumption.
Qed.


Lemma union_preserves_before_left : forall A B C (R1 R2 : relation A B) (Q : relation B C),
  (R1 /> Q) +/ (R2 /> Q) = ((R1 +/ R2) /> Q).
Proof.
  intros.
  apply extensionality.
  intro.
  apply extensionality.
  intro c.
  rewrite indistinguishability.
  split.
  intros [[b [H1 H2]] | [b [H1 H2]]].
  exists b.
  split.
  left.
  assumption.
  assumption.
  exists b.
  split.
  right.
  assumption.
  assumption.
  intros [b [[H1 | H2] H3]].
  left.
  exists b.
  split;assumption.
  right.
  exists b.
  split; assumption.
Qed.


(*Lemma union_preserves_subrelation*)


(*Chapter: closures*)

Definition closureRefl {A : Type} (R : relation A A) := R +/ ID A.
Definition closureSym {A : Type} (R : relation A A) := R +/ (^R).

Fixpoint exponent_endorelation {A : Type} (R : relation A A) (n : nat) :=
match n with
| O => ID A
| S n => (exponent_endorelation R n) /> R
end.

Lemma exponent_endorelation_left: forall {A : Type} (R : relation A A) (n : nat),
  exponent_endorelation R (S n) = (R /> (exponent_endorelation R n)).
Proof.
  intros.
  induction n.
  simpl.
  rewrite before_unit_l.
  rewrite before_unit_r.
  reflexivity.
  simpl.
  rewrite before_assoc.
  rewrite <- IHn.
  reflexivity.
Qed.



Definition closureTrans {A : Type} (R : relation A A) := unbounded_union (fun x => exponent_endorelation R (S x) ).

Lemma closureRefl_correct : forall A (R : relation A A), reflexive (closureRefl R).
Proof.
  intros A R a a' eq.
  right.
  assumption.
Qed.

Lemma closureSym_correct : forall A (R : relation A A), symmetric (closureSym R).
Proof.
  intros A R a a' [opl | opr].
  right.
  assumption.
  left.
  assumption.
Qed.

Lemma closureTrans_correct : forall A (R : relation A A), transitive (closureTrans R).
Proof.
  intros A R a a' [x [[i TL] [j TR]]].

Admitted.


(*Chapter: equivalence relations*)

Definition equivalence_relation {A : Type} (R : relation A A) := reflexive R /\ symmetric R /\ transitive R.

Lemma equivalence_flip : forall A (R : relation A A), equivalence_relation R -> equivalence_relation (^ R) /\ R = ^ R.
Proof.
Admitted.

(*Chapter: quotients*)

(* how to do this*)

(*Chapter ordered sets*)

Definition preorder {A : Type} (R : relation A A) := reflexive R /\ transitive R.

Lemma preorder_flip : forall A (R : relation A A), preorder R -> preorder (^ R).
Proof.
Admitted.


Definition partial_order {A : Type} (R : relation A A) := reflexive R /\ transitive R /\ antisymmetric R.

Lemma partial_order_flip : forall A (R : relation A A), partial_order R -> partial_order (^ R).
Proof.

Admitted.

Definition composition {A B C} (f : A-> B) (g : B -> C) (x : A) :=
  g (f x).


Definition reindex {A B C D} (f : A -> C) (g : B -> D) (R : relation C D) (a : A) (b : B) := R (f a) (g b).

Definition monotone_map {A B} (f : A -> B) (R : relation A A) (Q : relation B B) :=
  partial_order R /\ partial_order Q /\ R <= (reindex f f Q).




Lemma composition_preserves_monotone : forall A B C (f : A -> B) (g : B -> C) (R : relation A A) (P : relation B B) (Q : relation C C),
  partial_order R -> partial_order P -> partial_order Q -> monotone_map f R P -> monotone_map g P Q ->
  monotone_map (composition f g) R Q.
Proof.
Admitted.


Lemma op_intersection_preorder_is_equivalence : forall A (R : relation A A),
  preorder R -> equivalence_relation (op_intersection R).
Proof.
  intros A R [Refl Trans].
  split.
  intros a b eq.
  split; apply Refl.
  symmetry.
  assumption.
  assumption.
  split.
  intros a b [H H1].
  split;assumption.
  intros a b [x [[HP HN] [KP KN]]].
  split;
  apply Trans;
  exists x;
  split; assumption.
Qed.


Lemma op_intersection_preorder_is_minimal_equivalence : forall A (R : relation A A), preorder R ->
  forall Q : relation A A, equivalence_relation Q -> Q <= R -> Q <= op_intersection R.
Proof.
  intros A R [ReflR TransR] Q [ReflQ [SymQ TransQ]] SubRel a a' H.
  split.
  apply SubRel.
  apply SymQ.
  assumption.
  apply SubRel.
  assumption.
Qed.

Lemma op_intersection_identity_iff_antisym : forall A (R : relation A A),
  preorder R -> (op_intersection R = ID A <-> antisymmetric R).
Proof.
  intros A R [Refl Trans].
  split.
  intro.
  intros a b [HL HR].
  rewrite <- H.
  split;assumption.
  intro.
  apply extensionality.
  intro.
  apply extensionality.
  intro.
  apply indistinguishability.
  split.
  intros [HL HR].
  apply H.
  split; assumption.
  intro.
  rewrite H0.
  split; apply Refl; reflexivity.
Qed.





Definition discrete_preorder (A : Type) (x y : A) := x = y.
Definition codiscrete_preorder (A: Type) (x y : A) := True.

Lemma discrete_preorder_correct : forall A, preorder (discrete_preorder A).
Proof.
  intros A.
  split.
  intros a b eq.
  assumption.
  intros a b [x [tl tr]].
  transitivity x; assumption.
Qed.


Lemma codiscrete_preorder_correct : forall A, preorder (codiscrete_preorder A).
Proof.
  intros A.
  split.
  intros a b eq.
  exact I.
  intros a b t.
  exact I.
Qed.

Definition join {A} (I : Type) (R : relation A A) (p : preorder R) (f : I -> A) :=
  exists x: A, forall (x' : A) (i: I), R (f i ) x' -> R x x'.

Definition binary_join := join bool.

Definition meet {A I} (R : relation A A) (p : preorder R) (f : I -> A) :=
  exists x: A, forall (x' : A) (i: I), R x' (f i ) -> R x' x.



(*universal properties of quotients, codiscrete and discrete and closures*)


(*X is preordered by R, then R' is a partial order on X/opintersection R*)

(*Chapter, quotient of any preorder is a univeral poset*)

