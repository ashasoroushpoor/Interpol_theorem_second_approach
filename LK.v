Require Import Lang.
Require Import List.
Require Import multiset.
Import List.ListNotations.




Coercion p_nat (p : prop) : nat := prop_to_nat(p).
(* Coercion nat_p (n : nat) : prop := nat_to_prop(n). *)

Reserved Notation "G ⤑ p >< n" (no associativity, at level 68).
Inductive Node : Type :=
|leaf : Node
|onen: Node -> Node
|twon: Node -> Node -> Node.

Notation "☉ M" := (onen M) (no associativity, at level 65).
Notation "M1 ≍ M2" := (twon M1 M2 )(no associativity, at level 66). 

Inductive LKS : Node -> multiset -> multiset -> Prop :=
(* Axiom : A |- A *)
(* 1 *)
|LKSA: forall p: prop, {{p}} ⤑ {{p}} >< leaf
(* Structral rules *)
(* Weakening *)
(* 2 *)
|LKrW: forall G D p n, G ⤑ D >< n -> G ⤑ (D ⨣ p) >< (☉ n)
(* 3 *)
|LKlW: forall G D p n, G ⤑ D >< n ->  (G ⨣ p) ⤑ D >< (☉ n)
(* Contraction *)
(* 4 *)
|LKrC: forall G D p n, G ⤑ (D ⨣ p) ⨣ p >< n  -> G ⤑ (D ⨣ p) >< (☉ n)
(* 5 *)
|LKlC: forall G D p n, (G ⨣ p) ⨣ p ⤑ D >< n  -> (G ⨣ p) ⤑ D >< (☉ n)
(* Logical Rules *)
(* Conjunction *)
(* 6 *)
|LKrA: forall G D (a b : prop) m n,
G ⤑ (D ⨣ a) >< n -> G ⤑ (D ⨣ b) >< m -> G  ⤑ (D ⨣ (a ∧ b)) >< (m ≍ n)
(* 7 *)
|LKl1A: forall G D (a b : prop) n,
(G ⨣ a) ⤑ D >< n -> (G ⨣ (a ∧ b)) ⤑ D >< (☉ n)
(* 8 *)
|LKl2A: forall G D (a b : prop) n,
(G ⨣ b) ⤑ D >< n -> (G ⨣ (a ∧ b)) ⤑ D >< (☉ n)
(* Disjunction *)
(* 9 *)
|LKr1O: forall G D (a b : prop) n,
G ⤑ (D ⨣ a) >< n -> G  ⤑ (D ⨣ (a ∨ b)) >< (☉ n)
(* 10 *)
|LKr2O: forall G D (a b : prop) n,
G ⤑ (D ⨣ b) >< n -> G  ⤑ (D ⨣ (a ∨ b)) >< (☉ n)
(* 11 *)
|LKlO: forall G D (a b : prop) m n,
(G ⨣ a) ⤑ D >< n -> (G ⨣ b) ⤑ D >< m -> (G ⨣ (a ∨ b)) ⤑ D >< (m ≍ n)
(* Negation *)
(* 12 *)
|LKrN: forall G D (a : prop) n, (G ⨣ a) ⤑ D >< n -> G  ⤑ (D ⨣ (¬ a)) >< (☉ n)
(* 13 *)
|LKlN: forall G D (a : prop) n, G ⤑ (D ⨣ a) >< n -> (G ⨣ (¬ a)) ⤑ D >< (☉ n)
(* Implication *)
(* 14 *)
|LKrI: forall G D (a b : prop) n, (G ⨣ a) ⤑ (D ⨣ b) >< n
-> G  ⤑ (D ⨣ (a ⊃ b)) >< (☉ n)
(* 15 *)
|LKlI: forall G D (a b : prop) m n,
G ⤑ (D ⨣ a) >< n -> (G ⨣ b) ⤑ D >< m -> (G ⨣ (a ⊃ b)) ⤑ D >< (m ≍ n)
where "G ⤑ p >< n" := (LKS n G p).

Lemma mp : forall p q : prop, exists n, ({{p}} ⨣ (p ⊃ q)) ⤑ {{q}} >< n.
Proof.
    intros.
    exists ((☉ leaf) ≍ (☉ leaf)).
    constructor 15.
     - rewrite single_add. constructor 2. constructor 1.
     - rewrite single_add. constructor 3. constructor 1.
Qed.