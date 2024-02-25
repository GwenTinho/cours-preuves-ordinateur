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
Definition symmetric {A : Type} (R : relation A A) := (^ R) <= R.
Definition transitive {A : Type} (R : relation A A) := (R /> R) <= R.



Ltac extensionality_intros name := apply extensionality; intro name.


(*Closure interactions*)


(*Chapter: equivalence relations*)

Definition equivalence_relation {A : Type} (R : relation A A) := reflexive R /\ symmetric R /\ transitive R.


Lemma equivalence_flip : forall A (R : relation A A), equivalence_relation R -> equivalence_relation (^ R) /\ R = ^ R.
Proof.
  intros A R [Refl [Symm Trans]].
  split.
  - split.
    * intros a b eq.
      apply Refl.
      symmetry.
      assumption.
    * split.
      + intros a b H.
        apply Symm.
        assumption.
      + intros a c [b [H K]].
        apply Trans.
        exists b. split; assumption.
  - extensionality_intros a.
    extensionality_intros b.
    apply indistinguishability.
    split; intro; apply Symm; assumption.
Qed.

Record pointed_magma := mkPointedMagma {
  pm_carrier : Set;
  pm_mult : pm_carrier -> pm_carrier -> pm_carrier;
  pm_unit : pm_carrier
}.

Notation "| M |" := (pm_carrier M) (at level 20).
Notation "a /* b" := (pm_mult _ a b) (at level 20).
Notation "$" := (pm_unit _).

Inductive pm_closure {M : pointed_magma} (R : relation (| M |) (| M |))  : | M | -> | M | -> Prop :=
  | Inclusion : forall a b, R a b -> pm_closure R a b
  | Units : pm_closure R $ $
  | Products_Left : forall a b c : | M |, pm_closure R a b -> pm_closure R (c /* a) (c /* b)
  | Products_Right : forall a b c : | M |, pm_closure R a b -> pm_closure R (a /* c) (b /* c)
.

Lemma pm_closure_of_er_is_reflexive : forall (M : pointed_magma) (R : relation (| M |) (| M |)),
  equivalence_relation R -> reflexive (pm_closure R).
Proof.
  intros M R [Refl [Symm Trans]] a b eq.
  apply Inclusion.
  rewrite eq.
  apply Refl.
  reflexivity.
Qed.


Lemma pm_closure_of_er_is_symmetric : forall (M : pointed_magma) (R : relation (| M |) (| M |)),
  equivalence_relation R -> symmetric (pm_closure R).
Proof.
  intros M R [Refl [Symm Trans]] a b H.
  induction H.
  - apply Inclusion.
    apply Symm.
    assumption.
  - apply Units.
  - apply Products_Left; assumption.
  - apply Products_Right; assumption.
Qed.



Definition phi {A : Type} (R : relation A A) (a c : A) := forall b, R c b -> R a b.

Lemma relation_is_transitive_iff_included_in_phi : forall A (R : relation A A),
  transitive R <-> R <= phi R.
Proof.
  intros.
  split.
  - intros Trans a b H c K.
    apply Trans.
    exists b. split; assumption.
  - intros Sub a c [b [H K]].
    apply (Sub a b H c K).
Qed.


Lemma pm_closure_of_er_is_transitive : forall (M : pointed_magma) (R : relation (| M |) (| M |)),
  equivalence_relation R -> transitive (pm_closure R).
Proof.
  intros M R [Refl [Symm Trans]].
  rewrite relation_is_transitive_iff_included_in_phi.
  intros a b Closure c.

  induction Closure.
  - intros K.
    induction K.
    * apply Inclusion.
      apply Trans.
      exists a0. split; assumption.
    * apply Inclusion. assumption.
    *
      admit.
  - intros b H. assumption.
  - admit.
