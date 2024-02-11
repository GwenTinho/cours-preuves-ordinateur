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
  forall (a : A) (d : D),  (R /> P /> Q) a d <-> ((R /> P) /> Q) a d.
Proof.
  intros.
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

Lemma before_unit_l : forall A B (R : relation A B), forall (a : A) (b : B), ((ID A) /> R) a b <-> R a b.
Proof.
  intros.
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


Lemma before_unit_r : forall A B (R : relation A B), forall (a : A) (b : B),  (R /> (ID B)) a b <-> R a b.
Proof.
  intros.
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
  forall (a : A) (c : C), (^ (R /> Q)) c a <-> ((^ Q) /> (^ R)) c a.
Proof.
  intros.
  split;
  intros [b [H0 H1]];
  exists b;
  split; assumption.
Qed.

Lemma flip_id : forall A (x y: A), (^ (ID A)) x y <-> ID A y x.
Proof.
  intros.
  split; intro; assumption.
Qed.


Definition subrelation (A B : Type) (R Q : relation A B) := forall (a : A) (b : B), R a b -> Q a b.

Notation "R <= Q" := (subrelation _ _ R Q).

Lemma subrelation_refl : forall A B (R : relation A B), R <= R.
Proof.
  intros A B R x y.
  intro.
  assumption.
Qed.


Lemma subrelation_trans : forall A B (R P Q : relation A B), R <= P /\ P <= Q -> R <= Q.
Proof.
  intros A B R P Q [HL HR] a b.
  intro.
  apply HR.
  apply HL.
  apply H.
Qed.

Lemma subrelation_antisym : forall A B (R P : relation A B), R <= P /\ P <= R -> forall (a : A) (b : B), R a b <-> P a b.
Proof.
  intros A B R P [HL HR] a b.
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


Lemma flip_monotone : forall A B (R Q : relation A B),
  R <= Q -> (^ R) <= (^ Q).
Proof.
  intros A B R Q H b a.
  intro.
  apply H.
  assumption.
Qed.


