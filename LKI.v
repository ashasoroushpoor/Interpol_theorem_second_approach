Require Import Lang.
Require Import List.
Require Import multiset.
Import List.ListNotations.


(* Coercion nat_p (n : nat) : prop := nat_to_prop(n). *)

Reserved Notation "G ⇥ p >< n" (no associativity, at level 68).
Inductive Node : Type :=
|leaf : Node
|onen: Node -> Node
|twon: Node -> Node -> Node.

Notation "☉ M" := (onen M) (no associativity, at level 65).
Notation "M1 ≍ M2" := (twon M1 M2 )(no associativity, at level 66). 

Inductive LKI: Node -> multiset -> option prop -> Prop :=
(* 1 *)
|LKIA : forall (p : prop), {{p}} ⇥ Some p >< leaf
(* 2 *)
|LKIrW : forall G p n, G ⇥ None >< n -> G ⇥ Some p >< (☉ n)
(* 3 *)
|LKIlW : forall G op p n, G ⇥ op >< n -> G ⨣ p ⇥ op >< (☉ n)
(* 4 *)
|LKIlC : forall G op p n, (G ⨣ p) ⨣ p ⇥ op >< n -> G ⨣ p ⇥ op >< (☉ n)
(* 5 *)
|LKIrA : forall G (a b : prop) m n,
G ⇥ Some a >< n -> G ⇥ Some b >< m -> G ⇥ Some (a ∧ b) >< n ≍ m
(* 6 *)
|LKIl1A : forall G op (a b : prop) n, (G ⨣ a) ⇥ op >< n ->
(G ⨣ (a ∧ b)) ⇥ op >< (☉ n)
(* 7 *)
|LKIl2A : forall G op (a b : prop) n, (G ⨣ b) ⇥ op >< n ->
(G ⨣ (a ∧ b)) ⇥ op >< (☉ n)
(* 8 *)
|LKIr1O : forall G (a b : prop) n, G ⇥ Some a >< n 
-> G ⇥ Some (a ∨ b) >< (☉ n) 
(* 9 *)
|LKIr2O : forall G (a b : prop) n, G ⇥ Some b >< n 
-> G ⇥ Some (a ∨ b) >< (☉ n) 
(* 10 *)
|LKIlO: forall G op (a b : prop) m n,
(G ⨣ a) ⇥ op >< n -> (G ⨣ b) ⇥ op >< m -> (G ⨣ (a ∨ b)) ⇥ op >< (m ≍ n)
(* 11 *)
|LKIB : forall op, {{ ⊥ }} ⇥ op >< leaf
(* 12 *)
|LKrI: forall G (a b : prop) n, (G ⨣ a) ⇥ Some b >< n
-> G  ⇥ Some (a ⊃ b) >< (☉ n)
(* 13 *)
|LKlI: forall G op (a b : prop) m n,
G ⇥ Some a >< n -> (G ⨣ b) ⇥ op >< m -> (G ⨣ (a ⊃ b)) ⇥ op >< (m ≍ n)
where "G ⇥ p >< n" := (LKI n G p).

Lemma mp : forall p q : prop, exists n, ({{p}} ⨣ (p ⊃ q)) ⇥ Some q >< n.
Proof.
    intros.
    exists ((☉ leaf) ≍ (leaf)).
    constructor 13.
        - constructor 1.
        - rewrite single_add. constructor 3. constructor 1.
Qed.