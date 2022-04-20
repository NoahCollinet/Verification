(* 1 Relation Factorielle inductive *)

Inductive is_fact : nat -> nat -> Prop :=
  | is_fact_O : is_fact O (S O)
  | is_fact_S : forall n m : nat, is_fact n m -> is_fact (S n) (mult m (S n)).

(* 2 Fonction factorielle *)
Fixpoint fact (n : nat) : nat :=
  match n with
  | O => (S O)
  | (S p) => (mult (fact p) n)
end.

(* 3 Schéma d'induction fonctionnel *)
Require Import FunInd.
Functional Scheme fact_ind := Induction for fact Sort Prop.

Print fact_ind.

(* 4 Correction avec le schéma d'induction struturel *)
Goal forall n m : nat, (fact n) = m -> (is_fact n m).
Proof.
  induction n.
    intros.
    rewrite <- H.
    simpl.
    apply is_fact_O.
    
    intros.
    rewrite <- H.
    simpl.
    apply is_fact_S.
    apply IHn.
    reflexivity.
Qed.

(* 5 Correction avec le schéma d'induction fonctionnel *)

Goal forall n m : nat, (fact n) = m -> (is_fact n m).
Proof.
  intro.
  functional induction (fact n) using fact_ind.
    intros.
    rewrite <- H.
    apply is_fact_O.

    intros.
    rewrite <- H.
    apply is_fact_S.
    apply IHn0.
    reflexivity.
Qed.

(* 6 Complétude *)

Goal forall n m : nat, (is_fact n m) -> (fact n) = m.
Proof.
  intros.
  elim H.
    simpl.
    reflexivity.
    
    intros.
    simpl.
    rewrite H1.
    reflexivity.
Qed.


(* 2e partie *)

(* 1 Relation is_even *)
Inductive is_even : nat -> Prop :=
  | is_even_O : is_even O
  | is_even_S : forall n : nat, is_even n -> is_even (S (S n)).

(* 2 Fonction récursive *)
Fixpoint even(n : nat) : bool :=
  match n with 
  | O => true
  | (S O) => false
  | (S (S p)) => even p
end.

Require Import FunInd.
Functional Scheme even_ind := Induction for even Sort Prop.

(* 3 Démonstration de la correction pour les pairs *)
Goal forall n : nat, (even n) = true -> is_even n.
Proof.
  intros.
  functional induction (even n) using even_ind.
    apply is_even_O.
    
    inversion H.
    
    apply is_even_S.
    apply IHb.
    assumption.
Qed.

 
(* 4 Démonstration de la correction de tous les impairs *)
Goal forall n : nat, (even n) = false -> (not (is_even n)).
Proof.
  intros.
  functional induction (even n) using even_ind.
    inversion H.

    easy.
    intro.
    inversion H0.
    elim IHb.
    assumption.
    assumption.
Qed.

(* 5 Démonstration de la complétude even *)
Goal forall n :nat, (is_even n) -> (even n) = true.
Proof.
  intros.
  induction H.
    reflexivity.
    
    simpl.
    apply IHis_even.
Qed.

(* 6 Démonstration de la complétude de odd *)
Goal forall  n : nat, (not (is_even n)) -> (even n) = false.
Proof.
  intros.
  functional induction (even n) using even_ind.
    elimtype False.
    apply H.
    apply is_even_O.

    reflexivity.
    apply IHb.
    intro.
    apply H.
    apply is_even_S.
    assumption.
Qed.


 

