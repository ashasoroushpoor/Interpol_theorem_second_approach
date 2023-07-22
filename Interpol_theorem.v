Require Import Lang.
Require Import Formula.
Require Import LK.
Require Import List.
Require Import multiset.

Lemma equal_ext : forall A B, A = B <-> A ⩵ B .
Proof.
    split.
        - intros. rewrite H. unfold Equal. intros. reflexivity.
        - apply Extensionality_multiset.
Qed.

Lemma add_eq_one: forall m n, m + n = 1 -> m = 1 \/ n = 1.
Proof.
    intros. destruct n, m; try inversion H.
    - left. rewrite PeanoNat.Nat.add_0_r. reflexivity.
    - right. reflexivity.
    - rewrite <- PeanoNat.Nat.add_succ_comm in H1. inversion H1.
Qed.

Lemma add_eq_o: forall m n, m + n = 0 -> m = 0 /\ n = 0.
Proof.
    intros m n; destruct m ,n; intros; split; auto; try inversion H.
Qed.
Lemma one_in_union: forall x s1 s2, {{x}} = s1 ∪ s2
-> ({{x}} = s1) \/ {{x}} = s2.
Proof.
    intros. rewrite equal_ext in H. unfold "⩵" in H. unfold "∪" in H.
    specialize (H x) as H'. unfold Singleton in H'. rewrite PeanoNat.Nat.eqb_refl in H'.
    symmetry in H'. apply add_eq_one in H'. destruct H'.
        - left. rewrite equal_ext. unfold Equal. intros. unfold Singleton.
        destruct (PeanoNat.Nat.eqb x x0) eqn: E.
            + apply PeanoNat.Nat.eqb_eq in E. subst. symmetry. assumption.
            + specialize (H x0) as H'. unfold Singleton in H'. rewrite E in H'.
            symmetry in H'; apply add_eq_o in H'; destruct H'; auto.
        - right. rewrite equal_ext. unfold Equal. intros. unfold Singleton.
        destruct (PeanoNat.Nat.eqb x x0) eqn: E.
            + apply PeanoNat.Nat.eqb_eq in E. subst. symmetry. assumption.
            + specialize (H x0) as H'. unfold Singleton in H'. rewrite E in H'.
            symmetry in H'; apply add_eq_o in H'; destruct H'; auto.
Qed.

Lemma one_in_union2: forall x s1 s2, {{x}} = s1 ∪ s2
-> ({{x}} = s1 /\ s2 = ∅) \/ ({{x}} = s2 /\ s1 = ∅).
Proof.
    intros. apply one_in_union in H as H'. rewrite equal_ext in H. unfold "⩵" in H. unfold "∪" in H.
    destruct H'.
        - left; split; try assumption.
        rewrite equal_ext. unfold Equal. intros. unfold "∅".
        destruct (PeanoNat.Nat.eqb x x0) eqn: E.
            +apply PeanoNat.Nat.eqb_eq in E. subst.  specialize (H x0) as H'.
            unfold Singleton in H'; rewrite PeanoNat.Nat.eqb_refl in H'; inversion H'. reflexivity.
            +specialize (H x0) as H'. unfold Singleton in H'. rewrite E in H'.
            symmetry in H'. apply PeanoNat.Nat.eq_add_0 in H'. destruct H'. assumption.
        - right; split; try assumption.
        rewrite equal_ext. unfold Equal. intros. unfold "∅".
        destruct (PeanoNat.Nat.eqb x x0) eqn: E.
            +apply PeanoNat.Nat.eqb_eq in E. subst.  specialize (H x0) as H'.
            unfold Singleton in H'; rewrite PeanoNat.Nat.eqb_refl in H'.
            rewrite <- PeanoNat.Nat.add_succ_comm in H'. inversion H'. 
            rewrite PeanoNat.Nat.add_0_r in H1. auto.
            +specialize (H x0) as H'. unfold Singleton in H'. rewrite E in H'.
            symmetry in H'. apply PeanoNat.Nat.eq_add_0 in H'. destruct H'. assumption.
Qed.
Lemma add_union_singl: forall s x,
{{x}} ∪ s = s ⨣ x.
Proof.
    intros. apply Extensionality_multiset. unfold "⩵".
    intros. unfold "∪"; unfold Singleton; unfold "⨣".
    destruct (PeanoNat.Nat.eqb x x0); simpl; reflexivity.
Qed.

Lemma emp_add: forall x, ∅ ⨣ x = {{ x }}.
Proof.
    intros. rewrite <- add_union_singl. rewrite union_idr. reflexivity.
Qed.

Lemma ms_add_comm: forall s a b, (s ⨣ a) ⨣ b = (s ⨣ b) ⨣ a.
Proof.
    intros. rewrite equal_ext. unfold "⩵". intros. 
    unfold "⨣".
    destruct (PeanoNat.Nat.eqb b x), (PeanoNat.Nat.eqb a x); try reflexivity.
Qed.
Theorem LK_Interpol_strong: forall n (G1 G2 D1 D2 : multiset),
G1 ∪ G2 ⤑ D1 ∪ D2 >< n -> G1 ∩ G2 = ∅ -> D1 ∩ D2 = ∅-> 
(exists (c : prop) m1 m2, G1 ⤑ {{c}} ∪ D1 >< m1 /\ {{c}} ∪ G2 ⤑ D2 >< m2
/\ (atoms_incl c (G1 ∪ D1) (G2 ∪ D2))).
Proof.
    induction n; intros G1 G2 D1 D2 H Hg Hd; inversion H.
    - apply one_in_union2 in H0; apply one_in_union2 in H1; destruct H0, H1; destruct H0, H1.
        + exists (p ∧ ¬ p), (☉ leaf), (☉ (☉ (☉ (☉ leaf)))); repeat split.
            * rewrite add_union_singl. constructor 2. subst. constructor 1.
            * rewrite add_union_singl. rewrite H2; rewrite H3. 
            constructor 5. constructor 7. rewrite ms_add_comm. constructor 8.
            constructor 13. rewrite emp_add. constructor 1.
            * subst. unfold atom_in. exists p. split; simpl.
                ** unfold "∈". unfold "∪". unfold Singleton. rewrite PeanoNat.Nat.eqb_refl.
                auto.
                ** inversion H4. rewrite Bool.orb_false_r in H1. assumption.
            * subst. unfold atom_in. exists p. split; simpl.
            ** unfold "∈". unfold "∪". unfold Singleton. rewrite PeanoNat.Nat.eqb_refl.
            auto.
            ** inversion H4. rewrite Bool.orb_false_r in H1. assumption.
