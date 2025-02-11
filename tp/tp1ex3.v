Axiom not_not_elim : forall A : Prop, ~~A -> A.

Lemma lem : forall A : Prop,( A \/ ~A).
Proof.
    intro.
    assert (H := not_not_elim (A \/ ~A)).
    apply H.
    intro.
    apply H0.
    right.
    intro.
    apply H0.
    left.
    assumption.
Qed.


Lemma demorgan1 : forall A B, ~(A \/ B) <-> ~A /\ ~B.
Proof.
    intros A B.
    split.
    intro f.
    split; intro; apply f.
    left. assumption.
    right. assumption.
    intros [f g] [a | b].
    apply f. apply a.
    apply g. apply b.
Qed.
Lemma demorgan2 : forall A B, ~(A /\ B) <-> ~A \/ ~B.
Proof.
    intros A B.
    split.
    intro f.
    apply not_not_elim.
    intro g.
    apply g.
    left.
    intro.
    apply g.
    right.
    intro.
    apply f.
    split; assumption.
    intros [f | g] [a b].
    apply f. assumption.
    apply g. assumption.
Qed.

Lemma trivial1 : ~ True <-> False.
Proof.
    split.
    intros.
    apply H.
    exact I.
    intro.
    exfalso.
    assumption.
Qed.
Lemma trivial2 : ~ False <-> True.
Proof.
    split.
    intro.
    exact I.
    intros H f.
    assumption.
Qed.
Lemma implication_classical : forall A B, (A -> B) <-> ~A \/ B.
Proof.
    intros A B.
    split.
    intro.
    apply not_not_elim.
    intro f.
    apply f.
    left.
    intro a.
    apply f.
    right.
    apply H. assumption.
    intros [na | b] a.
    contradiction.
    assumption.
Qed.

Lemma not_implication_classical : forall A B, ~ (A -> B) <-> A /\ ~ B.
Proof.
    intros A B.
    split.
    intro f.
    apply not_not_elim.
    intro g.
    apply f.
    intro.
    apply not_not_elim.
    intro.
    apply g.
    split; assumption.
    intros [a nb] f.
    apply nb.
    apply f.
    apply a.
Qed.







Lemma pierce : forall A B : Prop, ((A -> B) -> A) -> A.
Proof.
  intros A B f.
  apply not_not_elim.
  intro.
  apply H.
  apply f.
  intro.
  contradiction.
Qed.


Lemma de_morgan_forall {X: Set} {A : X -> Prop}: ~ (forall x: X, A x) <-> (exists y : X, ~ (A y)).
Proof.
  split.
  intro f.
  apply not_not_elim.
  intro.
  apply f.
  intro.
  apply not_not_elim.
  intro.
  apply H.
  exists x.
  assumption.
  intros [x H0].
  intro.
  apply H0.
  apply (H x).
Qed.

Lemma de_morgan_exists {X: Set} {A : X -> Prop}: ~ (exists x: X, A x) <-> (forall y : X, ~ (A y)).
Proof.
  split.
  intros f x a.
  apply f.
  exists x.
  exact a.
  intros f [x H0].
  apply (f x); assumption.
Qed.


Lemma implication_swap {X : Set} {P : X -> Prop} {A: Prop} : (forall x : X, (P x -> A)) <-> ((exists x : X, P x) -> A).
Proof.
  split.
  intros f (x, a).
  apply (f x); assumption.
  intros f x a.
  apply f.
  exists x.
  assumption.
Qed.

