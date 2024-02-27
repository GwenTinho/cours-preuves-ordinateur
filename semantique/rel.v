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
  (^ (R /> Q)) = ((^ Q) /> (^ R)).
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

Require Coq.Classes.Morphisms.


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

Lemma usual_surjectivity {A B : Type} (R : relation A B) : surjective R <->  forall b : B, exists a : A, R a b.
Proof.
  split.
  intros.
  destruct (H b b).
  reflexivity.
  exists x.
  destruct H0.
  assumption.
  intro.
  intros b b' eq.
  destruct (H b).
  exists x.
  rewrite <- eq.
  split; assumption.
Qed.


Lemma surjective_before : forall A B C (R : relation A B) (Q : relation B C),
  surjective R /\ surjective Q -> surjective (R /> Q).
Proof.
  intros A B C R Q [sR sQ].
  unfold surjective, reflexive.
  rewrite flip_before.
  rewrite <- before_assoc.
  rewrite usual_surjectivity in sR.
  rewrite usual_surjectivity in sQ.
  intros c c' eq.
  destruct (sQ c) as [b sQ'].
  destruct (sR b) as [a sR'].
  exists b.
  split; try assumption.
  exists a.
  split; try assumption.
  exists b.
  split.
  assumption.
  rewrite <- eq.
  assumption.
Qed.


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
  intros A B C R1 R2 Q.
  apply extensionality.
  intro a.
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

Require Import List.
Import ListNotations.

Ltac extensionality_intros name := apply extensionality; intro name.


Lemma unbounded_union_preserves_before_left : forall I A B C (Rs : I -> relation A B) (Q : relation B C),
  unbounded_union (fun i => (Rs i) /> Q) = ((unbounded_union Rs) /> Q).
Proof.
  intros I A B C Rs Q.
  extensionality_intros a.
  extensionality_intros c.
  rewrite indistinguishability.
  split.
  {
  intros [i [b [HL HR]]].
  exists b.
  split.
    {
      exists i.
      assumption.
    }
    {
      assumption.
    }}
  {
    intros [b [[i HL] HR]].
    exists i.
    exists b.
    split;assumption.
  }
Qed.


Lemma union_preserves_subrelation : forall I A B (Rs : I -> relation A B) (Qs : I -> relation A B),
  (forall i, (Rs i) <= (Qs i)) -> unbounded_union Rs <= unbounded_union Qs.
Proof.
  intros I A B Rs Qs H a a' [i K].
  exists i.
  apply H.
  assumption.
Qed.



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

Lemma exponent_endorelation_sum : forall {A : Type} (R : relation A A) (n m : nat),
  (exponent_endorelation R (S n) /> exponent_endorelation R (S m)) = (exponent_endorelation R (S n + S m)).
Proof.
  intros A R n m.
  extensionality_intros a.
  extensionality_intros a'.
  rewrite indistinguishability.
  split.

Admitted.





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
  exists (S i + j).
  simpl.



Admitted.

(*Closure interactions*)


(*Chapter: equivalence relations*)

Definition equivalence_relation {A : Type} (R : relation A A) := reflexive R /\ symmetric R /\ transitive R.

Definition closure_Equiv {A : Type} (R : relation A A) := closureTrans (closureSym (closureRefl R)).


Lemma closure_Equiv_correct : forall A (R : relation A A), equivalence_relation (closure_Equiv R).
Proof.
Admitted.

Lemma equivalence_flip : forall A (R : relation A A), equivalence_relation R -> equivalence_relation (^ R) /\ R = ^ R.
Proof.
Admitted.

(*Chapter: quotients*)

Definition compatible {A B : Type} (R : relation A A) (f : A -> B) :=
  equivalence_relation R -> forall a a', R a a' -> f a = f a'.



Axiom Quotient : forall (X : Type) (R : relation X X) (p : equivalence_relation R), Type.

Axiom Quotient_map : forall (X : Type) (R : relation X X) (p : equivalence_relation R), X -> Quotient X R p.

Axiom Quotient_map_preserves : forall (X : Type) (R : relation X X) (p : equivalence_relation R), compatible R (Quotient_map X R p).

Axiom univ_quot : forall X Y (R : relation X X) (f : X -> Y) (p : equivalence_relation R),
   compatible R f -> exists! g : (Quotient X R p) -> Y, forall x : X, g (Quotient_map X R p x) = f x.

Definition generated_equiv {X Y} (f g : X -> Y) := closure_Equiv (fun y y' => exists x, f x = y /\ g x = y').

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

Definition join (A : Type) (I : Type) (R : relation A A) (p : preorder R) (f : I -> A) :=
  exists x: A, forall (x' : A) (i: I), R (f i ) x' -> R x x'.

Definition binary_join := join bool.

Definition meet {A I} (R : relation A A) (p : preorder R) (f : I -> A) :=
  exists x: A, forall (x' : A) (i: I), R x' (f i ) -> R x' x.



(*universal properties of quotients, codiscrete and discrete and closures*)


(*X is preordered by R, then R' is a partial order on X/opintersection R*)

(*Chapter, quotient of any preorder is a univeral poset*)

(*Free forget constructions and universal algebra*)

Record pointed_magma := mkPointedMagma {
  pm_carrier :> Set;
  pm_mult : pm_carrier -> pm_carrier -> pm_carrier;
  pm_unit : pm_carrier
}.

Notation "a /* b" := (pm_mult _ a b) (at level 20).
Notation "$" := (pm_unit _).

Inductive pm_closure {M : pointed_magma} (R : relation M M)  : M -> M -> Prop :=
  | Inclusion : forall a b, R a b -> pm_closure R a b
  | Units : pm_closure R $ $
  | Products : forall a b a' b' : M, pm_closure R a b -> pm_closure R a' b' -> pm_closure R (a /* a') (b /* b')
.

Lemma pm_closure_of_er_is_reflexive : forall (M : pointed_magma) (R : relation M M),
  equivalence_relation R -> reflexive (pm_closure R).
Proof.
  intros M R [Refl [Symm Trans]] a b eq.
  apply Inclusion.
  rewrite eq.
  apply Refl.
  reflexivity.
Qed.


Lemma pm_closure_of_er_is_symmetric : forall (M : pointed_magma) (R : relation M M),
  equivalence_relation R -> symmetric (pm_closure R).
Proof.
  intros M R [Refl [Symm Trans]] a b H.
  induction H.
  - apply Inclusion.
    apply Symm.
    assumption.
  - apply Units.
  - apply Products; assumption.
Qed.

Lemma pm_closure_of_composition_if : forall (M : pointed_magma) (R P: relation M M),
  pm_closure (R /> P) <= ((pm_closure R) /> (pm_closure P)).
Proof.
  intros M R P a b H.
  induction H.
  - destruct H  as [c [HL HR]].
    exists c.
    split; apply Inclusion; assumption.
  - exists $.
    split; apply Units.
  - destruct IHpm_closure1 as [c [HL1 HR1]].
    destruct IHpm_closure2 as [c' [HL2 HR2]].
    exists (c /* c').
    split; apply Products; assumption.
Qed.

Inductive closure_refl_trans {A : Type} (R : relation A A) : A -> A -> Prop :=
  | RT_Inclusion : forall x y, R x y -> closure_refl_trans R x y
  | RT_Refl : forall x, closure_refl_trans R x x
  | RT_Trans : forall x y z, closure_refl_trans R x y -> closure_refl_trans R y z -> closure_refl_trans R x z.

Inductive closure_symm {A : Type} (R : relation A A) : A -> A -> Prop :=
  | S_Inclusion : forall x y, R x y -> closure_symm R x y
  | S_Symm : forall x y, closure_symm R x y -> closure_symm R y x.

Definition closure_equiv {A : Type} (R : relation A A) := closure_refl_trans (closure_symm R).

Lemma closure_equiv_is_equiv : forall A (R : relation A A), equivalence_relation (closure_equiv R).
Proof.
  intros.
  split.
  - intros a b eq.
    rewrite eq.
    apply RT_Refl.
  - split.
    + intros a b H.
      induction H.
      * apply RT_Inclusion.
        apply S_Symm.
        assumption.
      * apply RT_Refl.
      * apply RT_Trans with y; assumption.
    + intros a b [c [HL HR]].
      apply RT_Trans with c; assumption.
Qed.


Inductive R_mon {M : pointed_magma} : M -> M -> Prop :=
| Assoc : forall a b c, R_mon ((a /* b) /* c) (a /* (b /* c))
| Unit_r : forall a, R_mon (a /* $) a
| Unit_l : forall a, R_mon ($ /* a) a.

Lemma R_mon_still_works : forall M : pointed_magma, equivalence_relation (pm_closure (closure_equiv (@R_mon M))).
Proof.
  intro M.
  split.
  * apply pm_closure_of_er_is_reflexive.
    apply closure_equiv_is_equiv.
  * split.
    + apply pm_closure_of_er_is_symmetric.
      apply closure_equiv_is_equiv.
    + intros a c [b [HL HR]].
      induction HL;induction HR.
      - apply Inclusion.
        apply RT_Trans with a0; assumption.
      - replace $ with (@pm_mult M $ $).
        **replace a with (a /* $).
          ++apply Products.
            --apply Inclusion. assumption.
            --apply Units.
          ++ admit.
Admitted.

(*More relations*)

Definition extension {A B C: Type} (Q : relation A C) (R : relation A B) (c : C) (b : B)  :=
  forall a : A, Q a c -> R a b.

Infix "|>" := extension (at level 50).


(*right kan extension internal in REL !!!*)

Definition restriction {A B C} (R : relation A B) (Q : relation C B) (a : A) (c : C) :=
  forall b : B, Q c b -> R a b.

Infix "<|" := restriction (at level 50).

Definition subset_left {A} (P : A -> Prop) : relation unit A := fun _ y => P y.
Definition subset_right {A} (P : A -> Prop) : relation A unit := fun x _ => P x.

Example extension_example1 : forall A (P : A -> Prop) (Q : relation A A),
  forall x : A, (Q |> (subset_right P)) x tt <-> forall x': A, Q x' x -> P x'.
Proof.
Admitted.

Example restriction_example1 : forall A (P : A -> Prop) (Q : relation A A),
  forall x : A, ((subset_left P) <| Q) tt x <-> forall x': A, Q x x' -> P x'.
Proof.
Admitted.

Theorem adjointness_for_extensions : forall A B C (R : relation A B) (P : relation A C) (Q : relation C B),
    Q <= (P |> R) <-> ((P /> Q) <= R).
Proof.
  intros A B C R P Q.
  split.
  * intros H x z [y [KL KR]].
    unfold extension in H.
    specialize (H  y z KR) as G.
    simpl in G.
    apply (G x).
    assumption.
  * intros H x z K y K0.
    apply H.
    exists x.
    split; assumption.
Qed.
    


Theorem adjointness_for_restrictions : forall A B C (R : relation A B) (P : relation A C) (Q : relation C B),
    ((P /> Q) <= R) <-> P <= (R  <| Q).
Proof.
  intros A B C R P Q.
  split.
  * intros H x z K y K0.
    apply H.
    exists z.
    split; assumption.
  * intros H x z [y [KL KR]].
    unfold restriction in H.
    specialize (H x y KL ) as G.
    simpl in G.
    apply (G z).
    assumption.
Qed.

Lemma variance_of_extension : forall A B C (R R': relation A B) (Q Q' : relation A C),
  Q' |> R <= Q |> R'.


Lemma variance_of_restriction : forall A B C (R R': relation A B) (Q Q' : relation C B),
  R <| Q' <= R' <| Q.

Lemma flip_restriction : forall A B C (R: relation A B) (Q : relation C B),
  (^ (R <| Q)) = (^ Q) |> (^ R).


Lemma flip_extension : forall A B C (R: relation A B) (Q : relation A C),
  (^ (R |> Q)) = (^ Q) <| (^ R).

Definition complement {A B} (R : relation A B) (a : A) (b : B) := ~ R a b.

Notation "- R" := (complement R).

Lemma complement_decreasing : forall A B (R R' : relation A B),
  R <= R' -> - R' <= - R.

Lemma de_morgan_1 : forall A B (R P Q : relation A B),
  - (R +/ Q) = (- R */ - Q).

Lemma de_morgan_2 : forall A B (R P Q : relation A B),
  - (R */ Q) = (- R +/ - Q).

Lemma complement_full : forall A B, - (Full A B) = Empty A B.
Lemma complement_empty : forall A B, - (Empty A B) = Full A B.
Lemma complement_opposite : forall A B (R : relation A B), - (^ R) = ^ (- R).
Lemma complement_composition_1 : forall A B C (R : relation A B) (Q : relation B C),
  - (R /> Q) = (^ R) |> (- Q).
Lemma complement_involution : forall A B (R : relation A B), - (- R) = R.

Lemma complement_composition_2 : forall A B C (R : relation A B) (Q : relation B C),
  - (R /> Q) = (- R) <| (^ Q).

Lemma complement_extension : forall A B C (R: relation A B) (Q : relation A C),
  - (Q |> R) = ((^ Q) /> (- R)).

Lemma extension_flip : forall A B C (R: relation A B) (Q : relation A C),
  (^ (Q |> R)) = (- R) |> (- Q).


Lemma restriction_flip : forall A B C (R: relation A B) (Q : relation C B),
  (^ (R <| Q)) = (- Q) <| (- R).

(*Chapter fixpoints :*)

Definition comptabible_with_magma {M : pointed_magma} (R : relation M M) := forall x y: M, pm_closure R x y <-> R x y.



Lemma equiv_closure_of_pm_closure_is_compatible : forall (M : pointed_magma) (R : relation M M),
  comptabible_with_magma (closure_equiv (pm_closure R)).
Proof.
  intros M R x y.
  split.
  * intro H.
    induction H.
    + assumption.
    + apply RT_Refl.
    + apply RT_Inclusion.
      apply S_Inclusion.
      apply Products.

Admitted.


Definition ars (A : Type) := relation A A.

Definition church_rosser {A : Type} (R : ars A) :=
  closure_equiv R <= ((closure_refl_trans R) /> (^ (closure_refl_trans R))).

(* Note the converse is always true.*)

Definition confluence {A : Type} (R Q : ars A) := ((^ R) /> R) <= (Q /> (^ Q)).

Lemma det_confluence : forall A (R : ars A), deterministic R <-> (confluence R (ID A)).

Definition diamond_property {A : Type} (R : ars A) := confluence R R.

Definition locally_confluent {A : Type} (R : ars A) := confluence R (closure_refl_trans R).
Definition confluent {A : Type} (R : ars A) := confluence (closure_refl_trans R) (closure_refl_trans R).


(*deterministic -> diamond -> locally*)

Lemma deterministic_implies_diamond : forall A (R : ars A), deterministic R -> diamond_property R.
Lemma diamond_implies_locally_confluent : forall A (R : ars A), diamond_property R -> locally_confluent R.

Lemma flip_of_refl_trans_closure : forall A (R : ars A), (^ (closure_refl_trans R)) = (closure_refl_trans (^ R)).
Proof.
  intros A R.
  extensionality_intros a.
  extensionality_intros b.
  apply indistinguishability.
  split.
  * intro H.
    induction H.
    + apply RT_Inclusion.
      assumption.
    + apply RT_Refl.
    + apply RT_Trans with y; assumption.
  * intro H.
    induction H.
    + apply RT_Inclusion.
      assumption.
    + apply RT_Refl.
    + apply RT_Trans with y; assumption.
Qed.



Theorem church_rosser_iff_confluent : forall A (R : ars A), church_rosser R <-> confluent R.

Lemma rt_closure_locally_confluent_iff_confluent: forall A (R : ars A),
  locally_confluent (closure_refl_trans R) <-> confluent R.


Lemma diamond_implies_confluence : forall A (R : ars A), diamond_property R -> confluent R.

(*closure union formula*)

(*prove strong induction*)
(*use union expression to use strong induction on n+m !!*)

Lemma sandwicz_theorem : forall A (R Q : ars A),
  R <= Q -> Q <= (closure_refl_trans R) -> diamond_property Q -> confluent R.

Definition normalization {A: Type} (R : ars A) := (closure_refl_trans R) */ (Empty A A <| R).

(*R hat contains normal forms*)

Theorem confluent_implies_normalization_deterministic : forall A (R : ars A),
  confluent R -> deterministic (normalization R).

(*TODO*)
(*Define weakly diverging terms*)
(*Define strongly normalizing terms*)
(*define fixpoint operators in this context*)

(*van neuman theorem*)


