Definition atom := nat.

Inductive prop : Type :=
| Var : atom  -> prop
| Neg : prop -> prop
| Disj : prop -> prop -> prop
| Conj : prop -> prop -> prop
| LDiv : prop -> prop -> prop.


Notation "^x_ x" := (Var x) (at level 30).
Coercion atom_as_prop (a : atom) : prop := Var a.


Notation "¬ P" := (Neg P) (at level 31). (* 00ac *)
Infix "∧" := Conj (left associativity, at level 32). (* 2227 *)
Infix "∨" := Disj (left associativity, at level 33). (* 2228 *)
Infix "⊃" := LDiv (right associativity, at level 34). (* 2283 *)
Require Import PeanoNat.
Theorem propeq_dec : forall p q : prop, {p = q} + {p <> q}.
Proof.
  induction p; induction q;
      try (left; reflexivity);
      try (right; intros H; inversion H; contradiction H);
      try (destruct (IHp1 q1); destruct (IHp2 q2); subst;
        try (right; intros H; inversion H; contradiction n);
        left; reflexivity).
    destruct (PeanoNat.Nat.eq_dec a a0).
      - left. subst. reflexivity.
      - right. intros H. inversion H. contradiction n.
      - destruct (IHp (q)).
        + left. subst. reflexivity.
        + right. intros H. inversion H. contradiction n.
Qed.

Fixpoint propeq (p q : prop) : bool :=
  match (p, q) with
  | (^x_n, ^x_m) => PeanoNat.Nat.eqb n m
  | (p1 ∧ p2, q1 ∧ q2) => (propeq p1 q1) && (propeq p2 q2)
  | (p1 ∨ p2, q1 ∨ q2) => (propeq p1 q1) && (propeq p2 q2)
  | (p1 ⊃ p2, q1 ⊃ q2) => (propeq p1 q1) && (propeq p2 q2)
  | _ => false
  end.