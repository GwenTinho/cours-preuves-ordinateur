Parameters A B C : Prop.

Lemma refl_impl : A -> A.
Proof.
    intro. assumption.
Qed.
Lemma trans_impl : (A -> B) -> (B -> C) -> A -> C.
Proof.
    intros f g a.
    apply g.
    apply f.
    apply a.
Qed.
Lemma comm_conj : A /\ B <-> B /\ A.
Proof.
    split;
    intros [a b];
      split; assumption.
Qed.
Lemma comm_disj : A \/ B <-> B \/ A.
Proof.
  split; intros [a | b]; (left; assumption) + (right; assumption).
Qed.
Lemma assoc_conj : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
  split.
  - intros [[a b] c].
    repeat split; assumption.
  - intros [a [b c]].
    repeat split; assumption.
Qed.
Lemma assoc_disj : (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  split.
  - intros [[a | b] | c].
    * left. assumption.
    * right. left. assumption.
    * right. right. assumption.
  - intros [a | [b | c]].
    * left. left. assumption.
    * left. right. assumption.
    * right. assumption.
Qed.
Lemma double_neg : A -> ~~A.
Proof.
  intros a f.
  apply f. apply a.
Qed.
Lemma contra : (A -> B) -> ~B -> ~A.
Proof.
  intros f nb a.
  apply nb.
  apply f.
  apply a.
Qed.
Lemma double_neg_excluded_middle : ~~(A \/ ~A).
Proof.
  intros f.
  apply f.
  right.
  intro a.
  apply f.
  left.
  assumption.
Qed.
Lemma iso_curry : (A /\ B -> C) <-> (A -> B -> C).
Proof.
  split.
  intros f a b.
  apply f.
  split; assumption.
  intros f [a b].
  apply f; assumption.
Qed.
Lemma distrib_conj : A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C).
Proof.
  split.
  intros [a [b | c]].
  left. split; assumption.
  right. split; assumption.
  intros [[a b] | [a c]].
  split; repeat (try left; assumption).
  split; repeat (try right; assumption).
Qed.
Lemma distrib_disj : A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C).
Proof.
  split.
  intros [a | [b c]].
  split; left; assumption.
  split; right; assumption.
  intros [[a | b] [a' | c]].
  left. assumption.
  left. assumption.
  left. assumption.
  right; split; assumption.
Qed.


Lemma distrib_conj_impl : (A -> (B /\ C)) <-> (A -> B) /\ (A -> C).
Proof.
  split.
  intro f.
  split; intro a;
  destruct (f a) as [b c]; assumption.
  intros [f g] a.
  split.
  apply f. apply a.
  apply g. apply a.
Qed.
Lemma distrib_disj_impl : ((A \/ B) -> C) <-> (A -> C) /\ (B -> C).
Proof.
  split.
  intro f.
  split; intro a; apply f.
  left. assumption.
  right. assumption.
  intros [f g] [a | b].
  apply f. apply a.
  apply g. apply b.
Qed.

Definition iso (A B : Type) := exists (f : A -> B) (g : B -> A), forall x : A, g (f x) = x /\ forall y : B, f (g y) = y.
Definition functor (F : Type -> Type) (A B : Type) := (A -> B) -> F A -> F B.

Definition covar_hom (C : Type) (A B : Type) (f : A -> B) (h : C -> A) (x : C) := f (h x).

Lemma covar_hom_is_functor: forall C : Type, functor (covar_hom C).




(*how to make a functor work in this world*)
