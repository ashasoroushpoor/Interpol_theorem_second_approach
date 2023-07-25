Coercion bool_to_Prop (b : bool) : Prop := b = true.

Definition atom := nat.

Inductive prop : Type :=
| Var : atom  -> prop
| Bot : prop
(* | Neg : prop -> prop *)
| Disj : prop -> prop -> prop
| Conj : prop -> prop -> prop
| LDiv : prop -> prop -> prop.

Definition Neg (p : prop) : prop := LDiv p Bot.
Definition Top := LDiv Bot Bot.
Axiom prop_to_nat: prop -> nat.
Axiom nat_to_prop: nat -> prop.

Axiom prop_to_prop: forall p, nat_to_prop(prop_to_nat(p)) = p.
Axiom nat_to_nat: forall n, prop_to_nat(nat_to_prop(n)) = n.

Notation "^x_ x" := (Var x) (at level 30).
Coercion atom_as_prop (a : atom) : prop := Var a.
Coercion p_nat (p : prop) : nat := prop_to_nat(p).


Notation "⊥" := Bot. (* 22a5 *)
Notation "⊤" := Top. (* 22a4 *)
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
Qed.

Fixpoint propeq (p q : prop) : bool :=
  match (p, q) with
  | (^x_n, ^x_m) => PeanoNat.Nat.eqb n m
  | (⊥, ⊥) => true
  | (p1 ∧ p2, q1 ∧ q2) => (propeq p1 q1) && (propeq p2 q2)
  | (p1 ∨ p2, q1 ∨ q2) => (propeq p1 q1) && (propeq p2 q2)
  | (p1 ⊃ p2, q1 ⊃ q2) => (propeq p1 q1) && (propeq p2 q2)
  | _ => false
  end.

Lemma propeq_refl: forall p, propeq p p.
Proof.
    intros. induction p.
    - simpl. apply PeanoNat.Nat.eqb_refl.
    - simpl. reflexivity.
    - simpl. rewrite IHp1. rewrite IHp2. simpl. reflexivity.
    - simpl. rewrite IHp1. rewrite IHp2. simpl. reflexivity.
    - simpl. rewrite IHp1. rewrite IHp2. simpl. reflexivity.
Qed.
Lemma eq_propeq: forall p q, p = q -> propeq p q.
Proof.
    intros. 
    subst. apply propeq_refl.
Qed.

(* Theorem propeq_eq_iff: forall p q, p = q <-> propeq p q.
Proof.
    intros. split; intros.
    - apply eq_propeq. assumption.
    - induction p, q; try inversion H.
        + rewrite PeanoNat.Nat.eqb_eq in H1. rewrite H1. reflexivity.
        + reflexivity.
        + apply andb_prop in H1. destruct H1.  admit.
        + apply andb_prop in H1. destruct H1. admit.
        + apply andb_prop in H1. destruct H1. admit.
Admitted. *)

Theorem eqb_eq: forall (p q :nat), (PeanoNat.Nat.eqb p q) <-> nat_to_prop p = nat_to_prop q.
Proof.
    intros; split; intros.
    - inversion H. rewrite PeanoNat.Nat.eqb_eq in H1. rewrite H1. reflexivity.
    - specialize (nat_to_nat p) as H'. rewrite H in H'. rewrite nat_to_nat in H'. rewrite H'.
    apply PeanoNat.Nat.eqb_refl.
Qed.
