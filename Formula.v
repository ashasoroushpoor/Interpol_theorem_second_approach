Require Import Lang.
Require Import List.
Require Import multiset.
Require Import PeanoNat.

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

(* This section was needed for intutionistic logic *)
Lemma atomin_singl_add: forall s a p, atom_in {{ a }} p -> atom_in (s ⨣ a) p.
Proof.
    intros. unfold atom_in in *. destruct H as [p' [H H']]. exists p'; split.
        -unfold In in *. unfold Singleton in H. unfold "⨣". destruct (a =? prop_to_nat p').
            + apply le_S_one.
            + inversion H.
        - assumption.
Qed.

Lemma option_add_emp: forall op, option_add ∅ op = option_to_multiset op.
Proof.
    intro. destruct op; simpl.
        - apply emp_add.
        - reflexivity.
Qed.
Lemma atomin_option_add_some: forall G a p, atom_in G a -> atom_in (option_add G (Some p)) a.
Proof.
    intros. unfold atom_in in *. destruct H as [p' [H1 H2]].
    exists p'; split.
        - simpl. apply in_add. assumption.
        - assumption.
Qed.

Lemma atomin_option_add: forall G a op, atom_in G a -> atom_in (option_add G op) a.
Proof.
    intros. destruct op.
        - apply atomin_option_add_some. assumption.
        - simpl. assumption.
Qed.

Lemma atomin_option_addr: forall G a op, atom_in (option_to_multiset op) a -> atom_in (option_add G op) a.
Proof.
    intros. destruct op.
        - simpl in *. unfold atom_in in *. destruct H as [p' [H H']].
        exists p'; split.
            + rewrite <- add_union_singl. rewrite union_mem. left. assumption.
            + assumption.
        - simpl in *. inversion H. destruct H0. apply In_emp_false in H0. inversion H0.
Qed.

Lemma atomin_option_destruct : forall G op a, atom_in (option_add G op) a
<-> atom_in G a \/ atom_in (option_to_multiset op) a.
Proof.
    intros. split; intros.
        - destruct op.
            + simpl in *. unfold atom_in in H. destruct H as [p' [H H']].
            rewrite <- add_union_singl in H. rewrite union_mem in H. destruct H.
            {
                right. unfold atom_in. exists p'. split; assumption.
            }
            {
                left. unfold atom_in. exists p'; split; assumption.
            }
            + simpl in *. left; assumption.
        - destruct H.
            + apply atomin_option_add. assumption.
            + apply atomin_option_addr. assumption.
Qed.


Lemma atomin_add_option: forall G op a p, atom_in (option_add G op) a -> atom_in (option_add (G ⨣ p) op) a.
Proof.
    intros. destruct op.
        - simpl in *. rewrite ms_add_comm. apply atomin_add. assumption.
        - simpl in *. apply atomin_add. assumption.
Qed.

Lemma atomin_add_destruct: forall G a p, atom_in (G ⨣ p) a <-> atom_in G a \/ atom_in {{ p }} a.
Proof.
    intros. split; intros. 
        - unfold atom_in in *. destruct H as [p' [H H1]]. unfold In in H.
        unfold "⨣" in H. destruct (PeanoNat.Nat.eqb p (prop_to_nat p')) eqn: E.
            -- right; exists p'; split.
                + unfold In. unfold Singleton. rewrite E. apply Nat.le_refl.
                + assumption.
            -- left; exists p'; split; assumption.
        - destruct H. 
            -- apply atomin_add. assumption.
            -- unfold atom_in in *. destruct H as [p' [H H1]].
                exists p';split.
                + unfold In in *. unfold Singleton in H. unfold "⨣".
                destruct (p =? prop_to_nat p'). apply le_S_one. inversion H.
                + assumption.
Qed.
Lemma atomin_add_double_option: forall G op a p, atom_in (option_add ((G ⨣ p) ⨣ p) op) a -> atom_in (option_add (G ⨣ p) op) a.
Proof.
    intros. destruct op.
        - simpl in *. apply atomin_add_destruct in H. destruct H. 
            + rewrite atomin_add_destruct. left. apply atomin_add_double. assumption.
            + rewrite atomin_add_destruct. right. assumption.
        - simpl in *. apply atomin_add_double. assumption.
Qed.