Require Export Classical.
(* ex1 *)
Parameter E : Set.
Parameters P Q : E -> Prop.

Goal (forall x: E, P(x) -> Q(x)) -> (exists x: E, P(x)) -> (exists x: E, Q(x)).
intros.
elim H0.
intros.
exists x.
apply H.
assumption.
Qed.


Goal (exists x: E, P(x) /\ Q(x)) -> (exists x: E, P(x)) /\ (exists x: E, Q(x)).
intros.
elim H.
intros.
split.
exists x.
apply H0.
exists x.
apply H0.
Qed.

(* ex2 *)
Parameter R : Set .
Parameters zero one : R.
Parameter opp : R -> R.

Parameters plus mult : R -> R -> R.
Section Commutative_ring .
Variables a b c : R.
Axiom ass_plus : plus ( plus a b ) c = plus a ( plus b c ) .
Axiom com_plus : plus a b = plus b a .
Axiom com_mult : mult a b = mult b a .
Axiom ass_mult : mult ( mult a b ) c = mult a ( mult b c ) .
Axiom dis_left : mult a ( plus b c ) = plus ( mult a b ) ( mult a c ) .
Axiom dis_right : mult ( plus b c ) a = plus ( mult b a ) ( mult c a ) .
Axiom neu_plus_r : plus a zero = a .
Axiom neu_plus_l : plus zero a = a .
Axiom neu_mult_r : mult a one = a .
Axiom neu_mult_l : mult one a = a .
Axiom opp_right : plus a ( opp a ) = zero .
Axiom opp_left : plus ( opp a ) a = zero .
End Commutative_ring .

Lemma ex2 : forall a b : R, (mult ( plus one one) (plus a b) ) = (plus ( plus a a) (plus b b)).
intros.
rewrite dis_left.
rewrite dis_right.
rewrite neu_mult_l.
rewrite dis_right.
rewrite neu_mult_l.
reflexivity.
Qed.

(* ex3 *)
Require Export List.
Open Scope list_scope.
Import List Notations.
Inductive is_rev : list nat -> list nat -> Prop :=
| is_rev_nil : is_rev nil nil
| is_rev_cons : forall ( n : nat ) ( l1 l2 : list nat ) ,
is_rev l1 l2 -> is_rev ( n :: l1 ) ( l2 ++ n :: nil ).

Fixpoint rev ( l : list nat ) { struct l } : list nat :=
match l with
| nil => nil
| e :: q => ( rev q ) ++ ( e :: nil )
end.

Theorem first : forall l1 l2 : list nat, (rev l1) = l2 -> (is_rev l1 l2).
induction l1.
intros.
rewrite <- H.
simpl.
apply is_rev_nil.

intros.
rewrite <- H.
simpl.
apply is_rev_cons.
apply IHl1.
reflexivity.
Qed.







