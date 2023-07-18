Require Import Lang.
Require Import List.
Require Import multiset.

Fixpoint atoms_of (p : prop) (a: atom) : bool :=
  match p with
  | ^x_a' => if (Nat.eqb a a') then true else false
  | p1 ∧ p2 => (atoms_of p1 a) || (atoms_of p2 a)
  | p1 ∨ p2 => (atoms_of p1 a) || (atoms_of p2 a)
  | p1 ⊃ p2 => (atoms_of p1 a) || (atoms_of p2 a)
  | _ => false
  end.

Definition atom_in (s: multiset) (a: atom) : Prop :=
    exists (p: prop), (prop_to_nat p) ∈ s /\ atoms_of p a.

Definition atoms_incl (s1 s2: multiset) : Prop :=
    forall (a: atom), (atom_in s1 a) -> (atom_in s2 a).