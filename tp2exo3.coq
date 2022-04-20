Open Scope type_scope.
Section Iso_axioms.
Variables A B C : Set.
Axiom Com : A * B = B * A.
Axiom Ass : A * (B * C) = A * B * C.
Axiom Cur : (A * B -> C) = (A -> B -> C).
Axiom Dis : (A -> B * C) = (A -> B) * (A -> C).
Axiom P_unit : A * unit = A.
Axiom AR_unit : (A -> unit) = unit.
Axiom AL_unit : (unit -> A) = A.
End Iso_axioms.

Lemma isos_ex1 : forall A B :Set, A * (B -> unit) = A.
Proof.
  intros.
  rewrite -> AR_unit.
  rewrite -> P_unit.
  reflexivity.
Qed.

Lemma isos_ex2 : forall A B : Set, A * unit * B = B * (unit * A).
Proof.
  intros.
  rewrite <- Com.
  rewrite (Com unit A).
 reflexivity.
Qed.

Lemma isos_ex3 : forall A B C : Set,(A * unit -> B * (C * unit)) =
(A * unit -> (C -> unit) * C) * (unit -> A -> B).
Proof.
intros.
rewrite -> AR_unit.
rewrite -> P_unit.
rewrite (Com unit).
rewrite -> P_unit.
rewrite <- Cur.
rewrite(Com unit A).
rewrite -> P_unit.
rewrite <- Dis.
rewrite (Com B C).
reflexivity.
Qed.
Ltac simplifie := 
intros;
repeat
  (rewrite P_unit || rewrite AR_unit || rewrite AL_unit);
try reflexivity.


