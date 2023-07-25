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

Definition atoms_incl (p: prop) (s1 s2: multiset) : Prop :=
    forall (a: atom), (atoms_of p a) ->
    (atom_in s1 a) /\ (atom_in s2 a).


Lemma atomin_add: forall s a p, atom_in s a -> atom_in (s ⨣ p) a.
Proof.
    intros. unfold atom_in. unfold atom_in in H. destruct H as [p' [H H']].
    exists p'. split.
    - unfold In; unfold "⨣". destruct (PeanoNat.Nat.eqb p (prop_to_nat p')).
        + apply le_S_one.
        + assumption.
    - assumption.
Qed.
Lemma atomin_add_double: forall s a p, atom_in ((s ⨣ p) ⨣ p) a -> atom_in (s ⨣ p) a.
Proof. 
    intros. unfold atom_in. unfold atom_in in H. destruct H as [p' [H H']].
    exists p'. split.
        - unfold In; unfold "⨣". unfold In in H; unfold "⨣" in H.
        destruct (PeanoNat.Nat.eqb p (prop_to_nat p')).
            +apply le_S_one.
            + assumption.
        - assumption.
Qed.
Lemma atomin_andr: forall s a (p q : prop), atom_in (s ⨣ p) a -> atom_in (s ⨣ (p ∧ q)) a.
Proof.
    intros. unfold atom_in. unfold atom_in in H. destruct H as [p' [H H']].
    unfold In; unfold "⨣". unfold In in H; unfold "⨣" in H.
    destruct (PeanoNat.Nat.eqb p (prop_to_nat p')) eqn: E.
        - exists (p ∧ q). split.
            + rewrite PeanoNat.Nat.eqb_refl. apply le_S_one.
            + unfold atoms_of. apply eqb_eq in E. rewrite prop_to_prop in E.
            rewrite prop_to_prop in E. rewrite <- E in H'. rewrite H'.
            rewrite Bool.orb_true_l. reflexivity.
        - exists p'. destruct (PeanoNat.Nat.eqb (p ∧ q) (prop_to_nat p')) eqn: E'.
            + apply eqb_eq in E'. rewrite prop_to_prop in E'.
            rewrite prop_to_prop in E'. split.
                * apply le_S_one.
                * assumption.
            + split; assumption.
Qed.
Lemma atomin_andl: forall s a (p q : prop), atom_in (s ⨣ q) a -> atom_in (s ⨣ (p ∧ q)) a.
Proof.
    intros. unfold atom_in. unfold atom_in in H. destruct H as [p' [H H']].
    unfold In; unfold "⨣". unfold In in H; unfold "⨣" in H.
    destruct (PeanoNat.Nat.eqb q (prop_to_nat p')) eqn: E.
        - exists (p ∧ q). split.
            + rewrite PeanoNat.Nat.eqb_refl. apply le_S_one.
            + unfold atoms_of. apply eqb_eq in E. rewrite prop_to_prop in E.
            rewrite prop_to_prop in E. rewrite <- E in H'. rewrite H'.
            rewrite Bool.orb_true_r. reflexivity.
        - exists p'. destruct (PeanoNat.Nat.eqb (p ∧ q) (prop_to_nat p')) eqn: E'.
            + apply eqb_eq in E'. rewrite prop_to_prop in E'.
            rewrite prop_to_prop in E'. split.
                * apply le_S_one.
                * assumption.
            + split; assumption.
Qed.
Lemma atomin_orr: forall s a (p q : prop), atom_in (s ⨣ p) a -> atom_in (s ⨣ (p ∨ q)) a.
Proof.
    intros. unfold atom_in. unfold atom_in in H. destruct H as [p' [H H']].
    unfold In; unfold "⨣". unfold In in H; unfold "⨣" in H.
    destruct (PeanoNat.Nat.eqb p (prop_to_nat p')) eqn: E.
        - exists (p ∨ q). split.
            + rewrite PeanoNat.Nat.eqb_refl. apply le_S_one.
            + unfold atoms_of. apply eqb_eq in E. rewrite prop_to_prop in E.
            rewrite prop_to_prop in E. rewrite <- E in H'. rewrite H'.
            rewrite Bool.orb_true_l. reflexivity.
        - exists p'. destruct (PeanoNat.Nat.eqb (p ∨ q) (prop_to_nat p')) eqn: E'.
            + apply eqb_eq in E'. rewrite prop_to_prop in E'.
            rewrite prop_to_prop in E'. split.
                * apply le_S_one.
                * assumption.
            + split; assumption.
Qed.
Lemma atomin_orl: forall s a (p q : prop), atom_in (s ⨣ q) a -> atom_in (s ⨣ (p ∨ q)) a.
Proof.
    intros. unfold atom_in. unfold atom_in in H. destruct H as [p' [H H']].
    unfold In; unfold "⨣". unfold In in H; unfold "⨣" in H.
    destruct (PeanoNat.Nat.eqb q (prop_to_nat p')) eqn: E.
        - exists (p ∨ q). split.
            + rewrite PeanoNat.Nat.eqb_refl. apply le_S_one.
            + unfold atoms_of. apply eqb_eq in E. rewrite prop_to_prop in E.
            rewrite prop_to_prop in E. rewrite <- E in H'. rewrite H'.
            rewrite Bool.orb_true_r. reflexivity.
        - exists p'. destruct (PeanoNat.Nat.eqb (p ∨ q) (prop_to_nat p')) eqn: E'.
            + apply eqb_eq in E'. rewrite prop_to_prop in E'.
            rewrite prop_to_prop in E'. split.
                * apply le_S_one.
                * assumption.
            + split; assumption.
Qed.
Lemma atomin_imp: forall s1 s2 a (p q : prop), atom_in ((s1 ⨣ p) ∪ (s2 ⨣ q)) a -> atom_in (s1 ∪ (s2 ⨣ p ⊃ q)) a.
Proof.
    intros. unfold atom_in. unfold atom_in in H. destruct H as [p' [H H']].
    rewrite union_mem in H. destruct H; unfold In in H.
        - destruct (PeanoNat.Nat.eqb p (prop_to_nat p')) eqn: E.
            + exists (p ⊃ q); split.
                *unfold In. rewrite add_union_extrac. 
                unfold "⨣". rewrite PeanoNat.Nat.eqb_refl. apply le_S_one.
                * apply eqb_eq in E. rewrite prop_to_prop in E.
                rewrite prop_to_prop in E. rewrite <- E in H'.
                unfold atoms_of. rewrite H'. rewrite Bool.orb_true_l. reflexivity.
            + unfold "⨣" in H. rewrite E in H. exists p'; split.
                * rewrite union_comm. unfold In. unfold "∪".
                rewrite PeanoNat.Nat.add_comm. apply le_add_r2. assumption.
                * assumption.
        - destruct (PeanoNat.Nat.eqb q (prop_to_nat p')) eqn: E.
        + exists (p ⊃ q); split.
            *unfold In. rewrite add_union_extrac. 
            unfold "⨣". rewrite PeanoNat.Nat.eqb_refl. apply le_S_one.
            * apply eqb_eq in E. rewrite prop_to_prop in E.
            rewrite prop_to_prop in E. rewrite <- E in H'.
            unfold atoms_of. rewrite H'. rewrite Bool.orb_true_r. reflexivity.
        + unfold "⨣" in H. rewrite E in H. exists p'; split.
            * rewrite add_union_extrac. rewrite union_comm. rewrite <- add_union_extrac. rewrite union_comm.
            unfold In. unfold "∪".
            rewrite PeanoNat.Nat.add_comm. apply le_add_r2. assumption.
            * assumption.
Qed.
Lemma atomin_impr: forall s1 a (p q : prop), atom_in (s1 ⨣ q) a -> atom_in (s1 ⨣ p ⊃ q) a.
Proof.
    intros. unfold atom_in. unfold atom_in in H. destruct H as [p' [H H']].
    unfold In; unfold "⨣". unfold In in H; unfold "⨣" in H.
    destruct (PeanoNat.Nat.eqb q (prop_to_nat p')) eqn: E.
        - exists (p ⊃ q). split.
            + rewrite PeanoNat.Nat.eqb_refl. apply le_S_one.
            + unfold atoms_of. apply eqb_eq in E. rewrite prop_to_prop in E.
            rewrite prop_to_prop in E. rewrite <- E in H'. rewrite H'.
            rewrite Bool.orb_true_r. reflexivity.
        - exists p'. destruct (PeanoNat.Nat.eqb (p ⊃ q) (prop_to_nat p')) eqn: E'.
            + apply eqb_eq in E'. rewrite prop_to_prop in E'.
            rewrite prop_to_prop in E'. split.
                * apply le_S_one.
                * assumption.
            + split; assumption.
Qed.
Lemma atomin_impl: forall s1 a (p q : prop), atom_in (s1 ⨣ p) a -> atom_in (s1 ⨣ p ⊃ q) a.
Proof.
    intros. unfold atom_in. unfold atom_in in H. destruct H as [p' [H H']].
    unfold In; unfold "⨣". unfold In in H; unfold "⨣" in H.
    destruct (PeanoNat.Nat.eqb p (prop_to_nat p')) eqn: E.
        - exists (p ⊃ q). split.
            + rewrite PeanoNat.Nat.eqb_refl. apply le_S_one.
            + unfold atoms_of. apply eqb_eq in E. rewrite prop_to_prop in E.
            rewrite prop_to_prop in E. rewrite <- E in H'. rewrite H'.
            rewrite Bool.orb_true_l. reflexivity.
        - exists p'. destruct (PeanoNat.Nat.eqb (p ⊃ q) (prop_to_nat p')) eqn: E'.
            + apply eqb_eq in E'. rewrite prop_to_prop in E'.
            rewrite prop_to_prop in E'. split.
                * apply le_S_one.
                * assumption.
            + split; assumption.
Qed.
Lemma atomsof_or_destruct: forall p p' x, atoms_of (p ∨ p') x -> atoms_of p x \/ atoms_of p' x.
Proof. 
    intros. unfold atoms_of in H. apply Bool.orb_prop in H. assumption.
Qed.
Lemma atomsof_and_destruct: forall p p' x, atoms_of (p ∧ p') x -> atoms_of p x \/ atoms_of p' x.
Proof.
    intros. unfold atoms_of in H. apply Bool.orb_prop in H. assumption.
Qed.
Lemma atomsof_imp_destruct: forall p p' x, atoms_of (p ⊃ p') x -> atoms_of p x \/ atoms_of p' x.
Proof.
    intros. unfold atoms_of in H. apply Bool.orb_prop in H. assumption.
Qed.