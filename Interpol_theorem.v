Require Import Lang.
Require Import Formula.
Require Import LK.
Require Import List.
Require Import multiset.



Theorem LK_Interpol_strong: forall n (G1 G2 D1 D2 : multiset),
G1 ∪ G2 ⤑ D1 ∪ D2 >< n -> 
(exists (c : prop) m1 m2, G1 ⤑ {{c}} ∪ D1 >< m1 /\ {{c}} ∪ G2 ⤑ D2 >< m2
/\ (atoms_incl c (G1 ∪ D1) (G2 ∪ D2))).
Proof.
    induction n; intros G1 G2 D1 D2 H; inversion H.
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
    - apply one_in_union2 in H0; destruct H0; destruct H0.
        + exists ⊥, leaf, leaf; repeat split; unfold Top; subst.
            * constructor 12.
            * rewrite union_idr. constructor 12.
            * simpl in H3. discriminate.
            * simpl in H3. discriminate.
        + exists ⊤, (☉ leaf), (☉ leaf); repeat split; unfold Top; subst.
            * rewrite add_union_singl. constructor 13. rewrite emp_add. constructor 12.
            * rewrite add_union_singl. constructor 3. constructor 12.
            * simpl in H3. discriminate.
            * simpl in H3. discriminate.
    - apply add_in_union in H1 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [D' H'].
        + rewrite <- H' in H1. rewrite union_comm in H1. rewrite add_union_extrac in H1. 
        apply add_union_remove in H1. rewrite union_comm in H1. rewrite H1 in H3.
        specialize (IHn G1 G2 D' D2 H3) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ m1), m2; repeat split; subst.
            * rewrite add_union_extrac. constructor 2. assumption.
            * assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            rewrite add_union_extrac. apply atomin_add. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            assumption.
        + rewrite <- H' in H1. rewrite add_union_extrac in H1. 
        apply add_union_remove in H1. rewrite H1 in H3.
        specialize (IHn G1 G2 D1 D' H3) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1 ,(☉ m2); repeat split; subst.
            * assumption.
            * constructor 2. assumption.
            *unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            rewrite add_union_extrac. apply atomin_add. assumption.
    - apply add_in_union in H1 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [G' H'].
        + rewrite <- H' in H1. rewrite union_comm in H1. rewrite add_union_extrac in H1. 
        apply add_union_remove in H1. rewrite union_comm in H1. rewrite H1 in H2.
        specialize (IHn G' G2 D1 D2 H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ m1), m2; repeat split; subst.
            * constructor 3. assumption.
            * assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            rewrite union_comm. rewrite add_union_extrac. apply atomin_add. rewrite union_comm. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            assumption.
        + rewrite <- H' in H1. rewrite add_union_extrac in H1. 
        apply add_union_remove in H1. rewrite H1 in H2.
        specialize (IHn G1 G' D1 D2 H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1 ,(☉ m2); repeat split; subst.
            * assumption.
            * rewrite add_union_extrac. constructor 3. assumption.
            *unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            rewrite union_comm. rewrite add_union_extrac. apply atomin_add. rewrite union_comm. assumption.
    - apply add_in_union in H1 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [D' H'].
        + rewrite <- H' in H1. rewrite union_comm in H1. rewrite add_union_extrac in H1. 
        apply add_union_remove in H1. rewrite union_comm in H1. rewrite H1 in H3.
        rewrite (union_comm D' D2) in H3. rewrite <- add_union_extrac in H3. rewrite <- add_union_extrac in H3.
        rewrite (union_comm D2 ((D' ⨣ p) ⨣ p)) in H3.
        specialize (IHn G1 G2 ((D' ⨣ p) ⨣ p) D2 H3) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ m1), m2; repeat split; subst.
            * rewrite add_union_extrac in IH1. rewrite add_union_extrac in IH1.
            rewrite add_union_extrac. constructor 4. assumption.
            * assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            rewrite add_union_extrac. apply atomin_add_double.
            rewrite <- add_union_extrac. rewrite <- add_union_extrac.
             assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            assumption.
        + rewrite <- H' in H1. rewrite add_union_extrac in H1. 
        apply add_union_remove in H1. rewrite H1 in H3. rewrite <- add_union_extrac in H3. rewrite <- add_union_extrac in H3.
        specialize (IHn G1 G2 D1 ((D' ⨣ p) ⨣ p) H3) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1 ,(☉ m2); repeat split; subst.
            * assumption.
            * constructor 4. assumption.
            *unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            rewrite add_union_extrac. apply atomin_add_double. 
            rewrite <- add_union_extrac. rewrite <- add_union_extrac. assumption.
    - apply add_in_union in H1 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [G' H'].
        + rewrite <- H' in H1. rewrite union_comm in H1. rewrite add_union_extrac in H1. 
        apply add_union_remove in H1. rewrite union_comm in H1. rewrite H1 in H2.
        rewrite (union_comm G' G2) in H2. rewrite <- add_union_extrac in H2. rewrite <- add_union_extrac in H2.
        rewrite (union_comm G2 ((G' ⨣ p) ⨣ p)) in H2.
        specialize (IHn ((G' ⨣ p) ⨣ p) G2 D1 D2 H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ m1), m2; repeat split; subst.
            * constructor 5. assumption.
            * assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            rewrite union_comm. rewrite add_union_extrac. apply atomin_add_double.
            rewrite <- add_union_extrac. rewrite <- add_union_extrac. rewrite union_comm.
            assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            assumption.
        + rewrite <- H' in H1. rewrite add_union_extrac in H1. 
        apply add_union_remove in H1. rewrite H1 in H2. rewrite <- add_union_extrac in H2. rewrite <- add_union_extrac in H2.
        specialize (IHn G1 ((G' ⨣ p) ⨣ p) D1 D2 H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1 ,(☉ m2); repeat split; subst.
            * assumption.
            * rewrite add_union_extrac. constructor 5. rewrite <- add_union_extrac. 
            rewrite <- add_union_extrac. assumption.
            *unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H4) as H5. destruct H5.
            rewrite union_comm. rewrite add_union_extrac. apply atomin_add_double.
            rewrite <- add_union_extrac. rewrite <- add_union_extrac. rewrite union_comm.
            assumption.
    - apply add_in_union in H1 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [G' H'].
        + rewrite <- H' in H1. rewrite union_comm in H1. rewrite add_union_extrac in H1.
        apply add_union_remove in H1. rewrite union_comm in H1. rewrite H1 in H2.
        rewrite (union_comm G' G2) in H2. rewrite <- add_union_extrac in H2. 
        rewrite union_comm in H2.
        specialize (IHn (G' ⨣ a) G2 D1 D2 H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ m1), m2; repeat split; subst.
            * constructor 7. assumption.
            * assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            rewrite union_comm. rewrite add_union_extrac. apply atomin_andr.
            rewrite <- add_union_extrac. rewrite union_comm. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            assumption.
        + rewrite <- H' in H1. rewrite add_union_extrac in H1. 
        apply add_union_remove in H1. rewrite H1 in H2. rewrite <- add_union_extrac in H2.
        specialize (IHn G1 (G' ⨣ a) D1 D2 H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1 ,(☉ m2); repeat split; subst.
            * assumption.
            * rewrite add_union_extrac. constructor 7. rewrite <- add_union_extrac. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            rewrite union_comm. rewrite add_union_extrac. apply atomin_andr.
            rewrite <- add_union_extrac. rewrite union_comm. assumption.
    - apply add_in_union in H1 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [G' H'].
        + rewrite <- H' in H1. rewrite union_comm in H1. rewrite add_union_extrac in H1.
        apply add_union_remove in H1. rewrite union_comm in H1. rewrite H1 in H2.
        rewrite (union_comm G' G2) in H2. rewrite <- add_union_extrac in H2. 
        rewrite union_comm in H2.
        specialize (IHn (G' ⨣ b) G2 D1 D2 H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ m1), m2; repeat split; subst.
            * constructor 8. assumption.
            * assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            rewrite union_comm. rewrite add_union_extrac. apply atomin_andl.
            rewrite <- add_union_extrac. rewrite union_comm. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            assumption.
        + rewrite <- H' in H1. rewrite add_union_extrac in H1. 
        apply add_union_remove in H1. rewrite H1 in H2. rewrite <- add_union_extrac in H2.
        specialize (IHn G1 (G' ⨣ b) D1 D2 H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1 ,(☉ m2); repeat split; subst.
            * assumption.
            * rewrite add_union_extrac. constructor 8. rewrite <- add_union_extrac. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            rewrite union_comm. rewrite add_union_extrac. apply atomin_andl.
            rewrite <- add_union_extrac. rewrite union_comm. assumption.
    - apply add_in_union in H1 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [D' H'].
        + rewrite <- H' in H1. rewrite union_comm in H1. rewrite add_union_extrac in H1.
        apply add_union_remove in H1. rewrite union_comm in H1. rewrite H1 in H3.
        rewrite (union_comm D' D2) in H3. rewrite <- add_union_extrac in H3. 
        rewrite (union_comm D2 (D' ⨣ a)) in H3.
        specialize (IHn G1 G2 (D' ⨣ a) D2 H3) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ m1), m2; repeat split; subst.
            * rewrite add_union_extrac. constructor 9. rewrite <- add_union_extrac. assumption.
            * assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            rewrite add_union_extrac. apply atomin_orr.
            rewrite <- add_union_extrac. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            assumption.
        +rewrite <- H' in H1. rewrite add_union_extrac in H1.
        apply add_union_remove in H1. rewrite union_comm in H1. rewrite H1 in H3.
        rewrite (union_comm D' D1) in H3. rewrite <- add_union_extrac in H3. 
        specialize (IHn G1 G2 D1 (D' ⨣ a) H3) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1 ,(☉ m2); repeat split; subst.
            * assumption.
            * constructor 9. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            rewrite add_union_extrac. apply atomin_orr.
            rewrite <- add_union_extrac. assumption.
    - apply add_in_union in H1 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [D' H'].
        + rewrite <- H' in H1. rewrite union_comm in H1. rewrite add_union_extrac in H1.
        apply add_union_remove in H1. rewrite union_comm in H1. rewrite H1 in H3.
        rewrite (union_comm D' D2) in H3. rewrite <- add_union_extrac in H3. 
        rewrite (union_comm D2 (D' ⨣ b)) in H3.
        specialize (IHn G1 G2 (D' ⨣ b) D2 H3) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ m1), m2; repeat split; subst.
            * rewrite add_union_extrac. constructor 10. rewrite <- add_union_extrac. assumption.
            * assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            rewrite add_union_extrac. apply atomin_orl.
            rewrite <- add_union_extrac. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            assumption.
        +rewrite <- H' in H1. rewrite add_union_extrac in H1.
        apply add_union_remove in H1. rewrite union_comm in H1. rewrite H1 in H3.
        rewrite (union_comm D' D1) in H3. rewrite <- add_union_extrac in H3. 
        specialize (IHn G1 G2 D1 (D' ⨣ b) H3) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1 ,(☉ m2); repeat split; subst.
            * assumption.
            * constructor 10. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            rewrite add_union_extrac. apply atomin_orl.
            rewrite <- add_union_extrac. assumption.  
    - apply add_in_union in H1 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [D' H'].
        + rewrite <- H' in H1. rewrite union_comm in H1. rewrite add_union_extrac in H1.
        apply add_union_remove in H1. rewrite union_comm in H1. rewrite H1 in H3.
        rewrite (union_comm D' D2) in H3. rewrite <- (add_union_extrac D2  D' b) in H3. 
        rewrite (union_comm D2 (D' ⨣ b)) in H3.
        rewrite (union_comm) in H3. rewrite <- add_union_extrac in H3. rewrite union_comm in H3.
        specialize (IHn (G1 ⨣ a)  G2 (D' ⨣ b) D2 H3) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ m1), m2; repeat split; subst.
            * rewrite add_union_extrac. constructor 13. rewrite <- add_union_extrac.
            assumption.
            * assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            apply atomin_imp. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            assumption.
        + rewrite <- H' in H1. rewrite add_union_extrac in H1.
        apply add_union_remove in H1. rewrite H1 in H3.
        rewrite <- (add_union_extrac D1 D' b) in H3. rewrite <- add_union_extrac in H3.
        specialize (IHn G1 (G2 ⨣ a) D1 (D' ⨣ b) H3) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1 ,(☉ m2); repeat split; subst.
            * assumption.
            * constructor 13. rewrite <- add_union_extrac.
            assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H4) as H5. destruct H5.
            apply atomin_imp. assumption.
    - apply add_in_union in H2 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [D' H'].
        + rewrite <- H' in H2. rewrite union_comm in H2. rewrite add_union_extrac in H2.
        apply add_union_remove in H2. 
        rewrite H2 in H4. rewrite <- add_union_extrac in H4. rewrite (union_comm D2 (D' ⨣ a)) in H4.
        rewrite H2 in H5. rewrite <- add_union_extrac in H5. rewrite (union_comm D2 (D' ⨣ b)) in H5.
        specialize (IHn1 G1  G2 (D' ⨣ b) D2 H5) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        specialize (IHn2 G1  G2 (D' ⨣ a) D2 H4) as IH. destruct IH as [c' [m1' [m2' [IH1' [IH2' IH3']]]]].
        exists (c ∨ c'), ((☉ m1) ≍ (☉ m1')) ,(m2' ≍ m2); repeat split; subst.
            * rewrite add_union_extrac. constructor 6.
                ** rewrite add_union_singl. rewrite ms_add_comm. constructor 10.
                rewrite <- add_union_singl. assumption.
                ** rewrite add_union_singl. rewrite ms_add_comm. constructor 9.
                rewrite <- add_union_singl. assumption.
            * rewrite add_union_singl. constructor 11;try rewrite <- add_union_singl; try assumption.
            * apply atomsof_or_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                rewrite add_union_extrac. apply atomin_andl. rewrite <- add_union_extrac. assumption. 
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                rewrite add_union_extrac. apply atomin_andr. rewrite <- add_union_extrac. assumption.
            * apply atomsof_or_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                assumption.
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                assumption.
        + rewrite <- H' in H2. rewrite add_union_extrac in H2.
        apply add_union_remove in H2. 
        rewrite H2 in H4. rewrite <- add_union_extrac in H4. 
        rewrite H2 in H5. rewrite <- add_union_extrac in H5.
        specialize (IHn1 G1  G2 D1 (D' ⨣ b) H5) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        specialize (IHn2 G1  G2 D1 (D' ⨣ a) H4) as IH. destruct IH as [c' [m1' [m2' [IH1' [IH2' IH3']]]]].
        exists (c ∧ c') ,(m1' ≍ m1), ((☉ m2) ≍ (☉ m2')); repeat split; subst.
            * rewrite add_union_singl. constructor 6; rewrite <- add_union_singl; try assumption.
            * constructor 6.
                ** rewrite add_union_singl. constructor 8. rewrite <- add_union_singl. assumption.
                ** rewrite add_union_singl. constructor 7. rewrite <- add_union_singl. assumption.
            * apply atomsof_and_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                assumption.
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                assumption.
            * apply atomsof_and_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                rewrite add_union_extrac. apply atomin_andl. rewrite <- add_union_extrac. assumption. 
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                rewrite add_union_extrac. apply atomin_andr. rewrite <- add_union_extrac. assumption.
    - apply add_in_union in H2 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [G' H'].
        + rewrite <- H' in H2. rewrite union_comm in H2. rewrite add_union_extrac in H2.
        apply add_union_remove in H2. 
        rewrite H2 in H3. rewrite <- add_union_extrac in H3. rewrite union_comm in H3.
        rewrite H2 in H5. rewrite <- add_union_extrac in H5. rewrite union_comm in H5.
        specialize (IHn1 (G' ⨣ b) G2 D1 D2 H5) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        specialize (IHn2 (G' ⨣ a) G2 D1 D2 H3) as IH. destruct IH as [c' [m1' [m2' [IH1' [IH2' IH3']]]]].
        exists (c ∨ c'), ((☉ m1) ≍ (☉ m1')) ,(m2' ≍ m2); repeat split; subst.
            * constructor 11.
                ** rewrite add_union_singl. constructor 10.
                rewrite <- (add_union_singl D1 c'). assumption.
                ** rewrite add_union_singl. constructor 9.
                rewrite <- (add_union_singl D1 c). assumption.
            * rewrite add_union_singl. constructor 11;try rewrite <- add_union_singl; try assumption.
            * apply atomsof_or_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                rewrite union_comm. rewrite add_union_extrac. apply atomin_orl. 
                rewrite <- add_union_extrac. rewrite union_comm. assumption. 
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                rewrite union_comm. rewrite add_union_extrac. apply atomin_orr. 
                rewrite <- add_union_extrac. rewrite union_comm. assumption.             
            * apply atomsof_or_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                assumption.
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                assumption.
        + rewrite <- H' in H2. rewrite add_union_extrac in H2.
        apply add_union_remove in H2. 
        rewrite H2 in H3. rewrite <- add_union_extrac in H3. 
        rewrite H2 in H5. rewrite <- add_union_extrac in H5. 
        specialize (IHn1 G1 (G' ⨣ b) D1 D2 H5) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        specialize (IHn2 G1 (G' ⨣ a) D1 D2 H3) as IH. destruct IH as [c' [m1' [m2' [IH1' [IH2' IH3']]]]].
        exists (c ∧ c') ,(m1' ≍ m1), ((☉ m2) ≍ (☉ m2')); repeat split; subst.
            * rewrite add_union_singl. constructor 6; rewrite <- add_union_singl; try assumption.
            * rewrite add_union_extrac. constructor 11.
                ** rewrite add_union_singl. rewrite ms_add_comm. constructor 8. 
                rewrite <- add_union_singl. assumption.
                ** rewrite add_union_singl. rewrite ms_add_comm. constructor 7.
                rewrite <- add_union_singl. assumption.
            * apply atomsof_and_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                assumption.
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                assumption.
            * apply atomsof_and_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                rewrite union_comm. rewrite add_union_extrac. apply atomin_orl. 
                rewrite <- add_union_extrac. rewrite union_comm. assumption. 
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                rewrite union_comm. rewrite add_union_extrac. apply atomin_orr. 
                rewrite <- add_union_extrac. rewrite union_comm. assumption.
    - apply add_in_union in H2 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [G' H'].
        + rewrite <- H' in H2. rewrite union_comm in H2. rewrite add_union_extrac in H2.
        apply add_union_remove in H2. 
        rewrite H2 in H3. rewrite (union_comm D1 D2) in H3. rewrite <- add_union_extrac in H3. 
        rewrite union_comm in H3. rewrite (union_comm D2 (D1 ⨣ a)) in H3.
        rewrite H2 in H5. rewrite <- add_union_extrac in H5. rewrite union_comm in H5.
        specialize (IHn1 (G' ⨣ b) G2 D1 D2 H5) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        specialize (IHn2 G' G2 (D1 ⨣ a) D2 H3) as IH. destruct IH as [c' [m1' [m2' [IH1' [IH2' IH3']]]]].
        exists (c ∨ c'), ((☉ m1) ≍ (☉ m1')) ,(m2' ≍ m2); repeat split; subst.
            * constructor 14.
                ** rewrite add_union_singl. rewrite ms_add_comm. constructor 10.
                rewrite <- (add_union_singl (D1 ⨣ a) c'). assumption.
                ** rewrite add_union_singl. constructor 9.
                rewrite <- (add_union_singl D1 c). assumption.
            * rewrite add_union_singl. constructor 11;try rewrite <- add_union_singl; try assumption.
            * apply atomsof_or_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                rewrite union_comm. rewrite add_union_extrac. apply atomin_impr. 
                rewrite <- add_union_extrac. rewrite union_comm. assumption. 
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                rewrite union_comm. rewrite add_union_extrac. apply atomin_impl. 
                rewrite union_comm. rewrite <- add_union_extrac. assumption.             
            * apply atomsof_or_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                assumption.
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                assumption.
        + rewrite <- H' in H2. rewrite add_union_extrac in H2.
        apply add_union_remove in H2. 
        rewrite H2 in H3. rewrite <- add_union_extrac in H3. 
        rewrite H2 in H5. rewrite <- add_union_extrac in H5. 
        specialize (IHn1 G1 (G' ⨣ b) D1 D2 H5) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        specialize (IHn2 G1 G' D1 (D2 ⨣ a) H3) as IH. destruct IH as [c' [m1' [m2' [IH1' [IH2' IH3']]]]].
        exists (c ∧ c') ,(m1' ≍ m1), ((☉ m2) ≍ (☉ m2')); repeat split; subst.
            * rewrite add_union_singl. constructor 6; rewrite <- add_union_singl; try assumption.
            * rewrite add_union_extrac. constructor 14.
                ** rewrite add_union_singl. constructor 8. 
                rewrite <- add_union_singl. assumption.
                ** rewrite add_union_singl. rewrite ms_add_comm. constructor 7.
                rewrite <- add_union_singl. assumption.
            * apply atomsof_and_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                assumption.
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                assumption.
            * apply atomsof_and_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                rewrite union_comm. rewrite add_union_extrac. apply atomin_impr. 
                rewrite <- add_union_extrac. rewrite union_comm. assumption. 
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                rewrite union_comm. rewrite add_union_extrac. apply atomin_impl. 
                rewrite union_comm. rewrite <- add_union_extrac. assumption.
Qed.

Theorem LK_Interpolation_Theorem: forall G D m, G ⤑ D >< m ->
exists (c : prop) m1 m2, G ⤑ {{ c }} >< m1 
/\ {{ c }} ⤑ D >< m2
/\ (atoms_incl c G D).
Proof.
    intros.
    specialize (LK_Interpol_strong m G ∅ ∅ D) as H'.
    rewrite union_idr in H'. rewrite union_idl in H'.
    apply H' in H.
    destruct H as [c [m1 [m2 [IH1 [IH2 IH3]]]]]. rewrite union_idr in IH1. rewrite union_idr in IH2.
    exists c, m1, m2; split; try split; assumption.
Qed.
