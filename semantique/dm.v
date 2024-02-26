Axiom extensionality : forall A B (f g: A -> B), (forall a: A, f a = g a) -> f = g.

Axiom indistinguishability : forall P Q: Prop, P = Q <-> (P <-> Q).

Require Setoid.


Definition relation (A B : Type) :=  A -> B -> Prop.

Definition flip (A B : Type) (R : (relation A B)) := fun x y => R y x.


Definition before (A B C: Type) (R : (relation A B)) (Q : (relation B C)) (x : A) (z : C) :=
  exists y : B, R x y /\ Q y z.

Definition ID (A : Type) (x y : A) := x = y.


Notation "R /> Q" := (before _ _ _ R Q) (at level 80, right associativity).
Notation "^ R" := (flip _ _ R) (at level 79, right associativity).


Definition subrelation (A B : Type) (R Q : relation A B) := forall (a : A) (b : B), R a b -> Q a b.



Notation "R <= Q" := (subrelation _ _ R Q).




Definition reflexive {A : Type} (R : relation A A) := ID A <= R.
Definition symmetric {A : Type} (R : relation A A) := (^ R) <= R.
Definition transitive {A : Type} (R : relation A A) := (R /> R) <= R.
Definition equivalence_relation {A : Type} (R : relation A A) := reflexive R /\ symmetric R /\ transitive R.


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




Inductive lat : Type :=
| A : lat
| Top : lat
| Bot : lat.

Definition L : pointed_magma := {|
  pm_carrier := lat;
  pm_unit := Top;
  pm_mult := fun x y : lat => match (x,y) with
    | (A,A) => A
    | (Top,Top) => Top
    | (Bot,Bot) => Bot
    | (Top, A) => A
    | (A, Top) => A
    | (Bot, _) => Bot
    | (_, Bot) => Bot
  end
|}.

Definition break (x y : L) := match (x,y) with
| (Top,Top) => True
| (Bot,Bot) => True
| (A,A) => True
| (Top, Bot) => True
| (Bot, Top) => True
| _ => False
end.

Lemma break_equiv : equivalence_relation break.
Proof.
  split.
  * intros a b eq.
    rewrite eq.
    destruct b; exact I.
  * split.
    + intros a b H.
      destruct a;
      destruct b; exact I + contradiction.
    + intros a c [b [HL HR]].
      destruct a; destruct b; destruct c; exact I + contradiction.
Qed.

Definition explicit_closure_of_break (a b : L) := break a b \/
match (a,b) with
| (A, Bot) => True
| (Bot, A) => True
| _ => False
end.

Lemma explicit_closure_of_break_works : break <= explicit_closure_of_break
/\ explicit_closure_of_break Top Top /\
forall a b a' b' : L, explicit_closure_of_break a b -> explicit_closure_of_break a' b' -> explicit_closure_of_break (a /* a') (b /* b').
Proof.
  split.
  * intros a b H.
    left. assumption.
  * split.
    + left. exact I.
    + intros a b a' b' H H0.
      destruct a; destruct a'; destruct b; destruct b'; simpl; try (left; exact I) + assumption + (right; exact I).
Qed.

Lemma explicit_closure_of_break_is_correct : explicit_closure_of_break = (pm_closure break).
Proof.
  apply extensionality.
  intro a.
  apply extensionality.
  intro b.
  apply indistinguishability.
  split.
  * intro.
    destruct a; destruct b; try (apply Inclusion;exact I) + (destruct H; contradiction).
    + replace A with (pm_mult L A Top).
      - replace Bot with (pm_mult L A Bot).
        **apply Products; apply Inclusion; exact I.
        **reflexivity.
      - reflexivity.
    + replace A with (pm_mult L A Top).
      - replace Bot with (pm_mult L A Bot).
        **apply Products; apply Inclusion; exact I.
        **reflexivity.
      - reflexivity.
  * intro.
    induction H.
    + left. assumption.
    + left. exact I.
    + destruct a; destruct b;destruct a'; destruct b'; simpl; try (left; exact I) + assumption + (right; exact I).
Qed.


Theorem closure_break_not_transitive : ~ transitive (pm_closure break).
Proof.
  rewrite <- explicit_closure_of_break_is_correct.
  intro.
  assert (G := H A Top).
  assert (explicit_closure_of_break A Top -> False).
  * intros [L| R]; contradiction.
  * apply H0.
    apply G.
    exists Bot.
    split.
    + right. exact I.
    + left. exact I.
Qed.

Theorem counterexample : ~ (forall (M : pointed_magma) (R : relation M M), equivalence_relation R -> equivalence_relation (pm_closure R)).
Proof.
  intro H.
  assert (G := H L break).
  assert (K := break_equiv).
  apply G in K.
  rewrite <- explicit_closure_of_break_is_correct in K.
  destruct K as [Refl [Symm Trans]].
  assert (KN := closure_break_not_transitive).
  rewrite <- explicit_closure_of_break_is_correct in KN.
  contradiction.
Qed.

