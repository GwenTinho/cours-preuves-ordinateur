Parameter X Y : Set.
Parameter P Q : X -> Prop.
Parameter R : X -> Y -> Prop.
Lemma distrib_forall_conj : (forall x, P x /\ Q x) <-> (forall x, P x) /\ (forall x, Q x).
Proof.
    split.
    intro H.
    split; intro.
    apply H.
    apply H.
    intros [L R] x.
    split.
    apply L.
    apply R.
Qed.

Lemma distrib_exists_disj : (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
    split.
    intros [x [L | R]].
    left. exists x. assumption.
    right. exists x. assumption.
    intros [[x H] | [x H]].
    exists x.
    left. assumption.
    exists x.
    right. assumption.
Qed.


Lemma switch_forall : (forall x, forall y, R x y) <-> (forall y, forall x, R x y).
Proof.
    split;
    intros H x y;
    apply H.
Qed.
Lemma switch_exists : (exists x, exists y, R x y) <-> (exists y, exists x, R x y).
    split; intros [y [x H]]; exists x; exists y; assumption.
Qed.
Lemma switch_forall_exists : (exists y, forall x, R x y) -> forall x, exists y, R x y.
Proof.
    intros [y H] x.
    exists y.
    apply H.
Qed.

