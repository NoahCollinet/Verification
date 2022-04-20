Parameter A : Prop.
Parameter B : Prop.
Goal A -> B -> A.
intros.
assumption.
Qed.
Parameter C : Prop.
Goal (A->B->C)->(A->B)->A->C.
intro.
intro.
intro.
apply(H H1).
apply(H0 H1).
Qed.

Goal   A /\ B->B.
intros.
destruct(H).
assumption.
Qed.

Goal B->A \/ B.
intros.
right.
assumption.
Qed.

Goal (A \/ B)->(A->C)->(B->C)->C.
intros.
elim H.
intro.
apply(H0 H2).
intro.
apply(H1 H2).
Qed.

Goal (A-> False -> ~A).
intros.
auto.
Qed.

Goal (False -> A).
intros.
auto.
destruct H.
Qed.

Goal (A <-> B) -> B -> A.
intros.
elim H.
intros.
apply(H2 H0).
Qed.

Goal (A -> B) -> (B-> A) -> (A <-> B).
intros.
split.
intros.
apply(H H1).
intros.
apply(H0 H1).
Qed.


