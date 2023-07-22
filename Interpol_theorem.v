Require Import Lang.
Require Import Formula.
Require Import LK.
Require Import List.
Require Import multiset.

Lemma emp_add: forall p, ∅ ⨣ p = {{p}}.
Proof.
    intros. unfold "∅". unfold "⨣". unfold Singleton. reflexivity.
Qed.
Lemma add_sing_refl: forall p q, {{p}} ⨣ q = {{q}} ⨣ p.
Proof.
    intros. apply equal_ext. unfold Equal. intros. unfold Singleton. unfold "⨣".
    destruct (PeanoNat.Nat.eqb q x) ,(PeanoNat.Nat.eqb p x); simpl; try reflexivity.
Qed.
Lemma EmptySetDef: ∅ = fun (x : U) => 0.
Proof.
    apply equal_ext. unfold Equal. intros. unfold "∅". reflexivity.
Qed.

Theorem LK_Interpol_strong: forall n (G1 G2 D1 D2 : multiset),
G1 ∪ G2 ⤑ D1 ∪ D2 >< n -> G1 ∩ G2 = ∅ -> D1 ∩ D2 = ∅-> 
(exists (c : prop) m1 m2, G1 ⤑ {{c}} ∪ D1 >< m1 /\ {{c}} ∪ G2 ⤑ D2 >< m2
/\ (atoms_incl c (G1 ∪ D1) (G2 ∪ D2))).
Proof.
    induction n; intros G1 G2 D1 D2 H Hg Hd; inversion H.
    - apply one_in_union2 in H0; apply one_in_union2 in H1; destruct H0, H1; destruct H0, H1.
        + exists (⊥), (☉ leaf), leaf; repeat split.
            * rewrite add_union_singl. constructor 2. subst. constructor 1.
            * rewrite add_union_singl. rewrite H2; rewrite H3. rewrite emp_add.
            constructor 12.
            * subst. simpl in H4. discriminate. 
            * subst. simpl in H4. discriminate. 
        + exists p ,leaf ,leaf; repeat split.
            * subst. rewrite union_idr. constructor 1.
            * subst. rewrite union_idr. constructor 1.
            * subst. unfold atom_in. exists p. split.
                ** rewrite union_idr. unfold Singleton. unfold In. rewrite PeanoNat.Nat.eqb_refl.
                apply PeanoNat.Nat.le_refl.
                ** assumption.
            * subst. rewrite union_idl. exists p. split.
                ** unfold Singleton. unfold In. rewrite PeanoNat.Nat.eqb_refl.
                apply PeanoNat.Nat.le_refl.
                ** assumption.
        + exists (¬ p) ,(☉ (☉ leaf)) ,((☉ leaf) ≍ leaf); repeat split.
            * rewrite add_union_singl. apply LKrN. subst. rewrite emp_add. constructor 1.
            * subst. rewrite add_union_singl. unfold Neg. constructor 14.
                ** rewrite (emp_add p). constructor 1.
                ** rewrite add_sing_refl. constructor 3. constructor 12.
            * subst. rewrite union_idl. unfold atom_in. exists p. split.
                **  unfold Singleton. unfold In. rewrite PeanoNat.Nat.eqb_refl.
                apply PeanoNat.Nat.le_refl.
                ** unfold atoms_of in H4. inversion H4. rewrite Bool.orb_false_r in H1. apply H1.
            * subst.  rewrite union_idr. unfold atom_in. exists p. split.
            **  unfold Singleton. unfold In. rewrite PeanoNat.Nat.eqb_refl.
            apply PeanoNat.Nat.le_refl.
            ** unfold atoms_of in H4. inversion H4. rewrite Bool.orb_false_r in H1. apply H1.
        + exists ⊤, (☉ leaf), (☉ leaf); repeat split; unfold Top; subst.
            * rewrite union_idr. rewrite <- union_idl. constructor 13.
            rewrite emp_add. rewrite <- EmptySetDef. rewrite (emp_add ⊥). constructor 1.
            * rewrite add_union_singl. constructor 3. constructor 1.
            * simpl in H4. discriminate.
            * simpl in H4. discriminate.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
Admitted.