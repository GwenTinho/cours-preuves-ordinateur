Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Inductive equals : nat -> nat -> Prop :=
| Refl : equals O O
| Step : forall n m, equals n m -> equals (S n) (S m).

Notation "a == b" := (equals a b) (at level 70).

Lemma equal_refl : forall a, a == a.
Proof.
  intro a.
  induction a.
  apply Refl.
  apply Step.
  apply IHa.
Qed.

Lemma equal_symmetry : forall a b, a == b -> b == a.
Proof.
  intros.
  induction H.
  apply Refl.
  apply Step.
  apply IHequals.
Qed.

Lemma equal_trans : forall a b c, a == b -> b == c -> a == c.
Proof.
  intros a b c.
  intros H.
  generalize c.
  induction H.
  intros; assumption.
  intros.
  inversion H0.
  apply Step.
  apply IHequals.
  assumption.
Qed.


Hypothesis tests : nat -> nat -> Prop.



Fixpoint add n m := match n with
| O => m
| S n => S (add n m)
end.

Notation "a /+ b" := (add a b) (at level 50, left associativity).

Fixpoint mult n m := match n with
| O => O
| S n => add (mult n m) m
end.

Notation "a /* b" := (mult a b) (at level 40, left associativity).



Lemma nat_equals_implies_equals : forall a b, a == b -> a = b.
Proof.
  intros.
  induction H.
  reflexivity.
  rewrite IHequals.
  reflexivity.
Qed.

Lemma equals_implies_nat_equals : forall a b, a = b -> a == b.
Proof.
  intros.
  rewrite H.
  apply equal_refl.
Qed.

Lemma add_O : forall a, a /+ O = a.
Proof.
  intro.
  induction a.
  simpl.
  reflexivity.
  simpl.
  f_equal.
  assumption.
Qed.

Lemma add_S : forall a b, a /+ S b = S a /+ b.
Proof.
  intros.
  induction a.
  reflexivity.
  simpl.
  f_equal.
  rewrite IHa.
  reflexivity.
Qed.

Lemma mult_0 : forall a, a /* O = O.
Proof.
  intro.
  induction a.
  reflexivity.
  simpl.
  rewrite IHa.
  reflexivity.
Qed.

Lemma add_commutes : forall a b, a /+ b = b /+ a.
Proof.
  intros.
  induction a.
  simpl.
  rewrite add_O.
  reflexivity.
  simpl.
  rewrite add_S.
  rewrite IHa.
  reflexivity.
Qed.

Lemma add_assoc : forall a b c, a /+ (b /+ c) = a /+ b /+ c.
Proof.
  intros.
  induction a.
  reflexivity.
  simpl.
  f_equal.
  assumption.
Qed.

Lemma mult_S : forall a b, a /* S b = a /* b /+ a.
Proof.
  intro a.
  induction a.
  intro.
  reflexivity.
  intro.
  simpl.
  rewrite IHa.
  rewrite <- add_assoc.
  rewrite add_commutes with (a := a) (b := S b).
  rewrite <- add_assoc.
  simpl.
  rewrite add_S with b a.
  reflexivity.
Qed.


Lemma add_cancel : forall x y m, m /+ x = m /+ y -> x = y.
Proof.
  intros.
  induction m.
  simpl in H.
  assumption.
  apply IHm.
  injection H.
  intro.
  assumption.
Qed.

Lemma parity : forall x, exists y, x = S (S O) /* y \/ x = S ((S (S O) /* y)).
Proof.
  intro.
  induction x.
  exists O.
  simpl.
  left.
  reflexivity.
  simpl.
  destruct IHx as [y [H | H]].
  exists y.
  right.
  f_equal.
  assumption.
  exists (S y).
  left.
  simpl.
  f_equal.
  rewrite H.
  simpl.
  rewrite add_S.
  reflexivity.
Qed.

Lemma mult_commutes : forall a b, a /* b = b /* a.
Proof.
  intros.
  induction a.
  simpl.
  rewrite mult_0.
  reflexivity.
  simpl.
  rewrite IHa.
  rewrite mult_S.
  reflexivity.
Qed.

Lemma mult_dist_r : forall a b c, a /* (b /+ c) = a /* b /+ a /* c.
Proof.
  intros.
  induction a.
  reflexivity.
  simpl.
  rewrite IHa.
  rewrite add_commutes with (a /* c) c.
  rewrite add_assoc with (a /* b /+ b) c (a /* c).
  rewrite <- add_assoc with (a /* b) (a /* c) (b /+ c).
  rewrite add_commutes with (a /* c) (b /+ c).
  repeat rewrite add_assoc.
  reflexivity.
Qed.

Lemma mult_dist_l : forall a b c, (b /+ c) /* a  = b /* a /+ c /* a.
Proof.
  intros.
  rewrite mult_commutes.
  rewrite mult_commutes with b a.
  rewrite mult_commutes with c a.
  exact (mult_dist_r a b c).
Qed.



Lemma mult_assoc : forall a b c, a /* (b /* c) = a /* b /* c.
Proof.
  intros.
  induction a.
  reflexivity.
  simpl.
  rewrite IHa.
  rewrite mult_dist_l.
  reflexivity.
Qed.

Inductive leq : nat -> nat -> Prop :=
| Zero_leq : forall n, leq O n
| Succ_leq : forall n m, leq n m -> leq (S n) (S m).

Definition pred n := match n with
| O => O
| S n => n
end.

Lemma pred_trans : forall a b c, leq a b -> leq b c -> leq a c.
Admitted.

Lemma pred_S : forall x, leq x (S x).
Proof.
  intro.
  induction x.
  apply Zero_leq.
  apply Succ_leq.
  assumption.
Qed.

Lemma pred_refl : forall x, leq x x.
Proof.
  intro.
  induction x.
  apply Zero_leq.
  apply Succ_leq.
  apply IHx.
Qed.

Definition leq_sum a b := exists k, a /+ k = b.


Lemma leq_iff_leq_sum : forall a b, leq_sum a b <-> leq a b.
Proof.
  intro a.
  induction a.
  intro.
  split.
  intro.
  apply Zero_leq.
  intro.
  exists b.
  reflexivity.
  intro.
  split.
  intros [k H].
  rewrite <- H.
  simpl.
  apply Succ_leq.
  apply IHa.
  exists k.
  reflexivity.
  intro.

Admitted.





Lemma minimal_principal : forall (A : nat -> Prop),
(exists x, A x) -> (exists x0, A x0 /\ forall y, A y -> leq_sum x0 y).
Proof.
  intros A [x H].























Lemma ex1n1 : forall x y z, x = y -> (x /* x) /+ ((S (S O)) /* (x /* z)) /+ (z /* z) = (y /* y) /+ ((S (S O)) /* (y /* z)) /+ (z /* z).
Proof.
  intros x y z.
  generalize x y.
  induction z.
  intros.
  simpl.
  rewrite add_O.
  rewrite mult_0.
  rewrite add_O.
  rewrite mult_0.
  simpl.
  rewrite add_O.
  rewrite add_O.
  rewrite H.
  reflexivity.
  intros.
  simpl.
Admitted.







(*Decidable equality for nats*)
