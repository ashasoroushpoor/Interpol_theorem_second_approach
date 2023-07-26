Require Import Lang.
Require Import Formula.
Require Import LKI.
Require Import List.
Require Import multiset.
Require Import PeanoNat.





Theorem LKI_Interpol_strong: forall n (G1 G2: multiset) (op : option prop),
G1 ∪ G2 ⇥ op >< n -> 
(exists (c : prop) m1 m2, G1 ⇥ Some c >< m1 /\ {{c}} ∪ G2 ⇥ op >< m2
/\ (atoms_incl c (G1) (option_add G2 op))).
Proof.
    induction n; intros G1 G2 op H; inversion H.
    - apply one_in_union2 in H0; destruct H0; destruct H0.
        + exists p, leaf, leaf; repeat split; subst.
            * constructor 1.
            * rewrite union_idr. constructor 1.
            * unfold atom_in. exists p. split. unfold In. unfold Singleton. 
            rewrite PeanoNat.Nat.eqb_refl. apply PeanoNat.Nat.le_refl. assumption.
            * simpl. rewrite emp_add. unfold atom_in.  exists p. split. unfold In. unfold Singleton. 
            rewrite PeanoNat.Nat.eqb_refl. apply PeanoNat.Nat.le_refl. assumption.
        + exists ⊤, (☉ leaf), (☉ leaf); repeat split; subst.
            * unfold "⊤". constructor 12. rewrite emp_add. constructor 11.
            * rewrite add_union_singl. constructor 3. constructor 1.
            * unfold atoms_of in H3. unfold "⊤" in H3. 
            simpl in H3. discriminate.
            * unfold atoms_of in H3. unfold "⊤" in H3. 
            simpl in H3. discriminate.
    - apply one_in_union2 in H0; destruct H0; destruct H0.
        + exists ⊥, leaf, leaf; repeat split; subst; try rewrite union_idr; try constructor 11;
        try (unfold atoms_of in H3;  discriminate).
        + exists ⊤, (☉ leaf), (☉ leaf); repeat split; subst.
            * unfold "⊤". constructor 12. rewrite emp_add. constructor 11.
            * rewrite add_union_singl. constructor 3. constructor 11.
            * unfold atoms_of in H3. unfold "⊤" in H3. 
            simpl in H3. discriminate.
            * unfold atoms_of in H3. unfold "⊤" in H3. 
            simpl in H3. discriminate.
    - subst. specialize (IHn G1 G2 None H1) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
    exists c, m1, (☉ m2); repeat split; subst.
        + assumption.
        + constructor 2. assumption.
        + simpl in IH3. unfold atoms_incl in IH3. specialize (IH3 a H0) as H5. destruct H5. assumption.
        + simpl in IH3. unfold atoms_incl in IH3. specialize (IH3 a H0) as H5. destruct H5. 
        apply atomin_option_add_some. assumption.
    - subst. apply add_in_union in H1 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [G' H'].
        + rewrite <- H' in H1. rewrite union_comm in H1. rewrite add_union_extrac in H1.
        apply add_union_remove in H1. rewrite union_comm in H1. rewrite H1 in H2.
        specialize (IHn G' G2 op H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ m1), m2; repeat split; subst.
            * constructor 3. assumption.
            * assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H0) as H5. destruct H5. 
            apply atomin_add. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H0) as H5. destruct H5.
            assumption.
        + rewrite <- H' in H1. rewrite add_union_extrac in H1.
        apply add_union_remove in H1. rewrite H1 in H2.
        specialize (IHn G1 G' op H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1 ,(☉ m2); repeat split; subst.
            * assumption.
            * rewrite add_union_extrac. constructor 3. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H0) as H5. destruct H5. 
            assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H0) as H5. destruct H5.
            apply atomin_add_option. assumption.
    - subst. apply add_in_union in H1 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [G' H'].
        + rewrite <- H' in H1. rewrite union_comm in H1. rewrite add_union_extrac in H1. 
        apply add_union_remove in H1. rewrite union_comm in H1. rewrite H1 in H2.
        rewrite (union_comm G' G2) in H2. rewrite <- add_union_extrac in H2. rewrite <- add_union_extrac in H2.
        rewrite (union_comm G2 ((G' ⨣ p) ⨣ p)) in H2.
        specialize (IHn ((G' ⨣ p) ⨣ p) G2 op H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ m1), m2; repeat split; subst.
            * constructor 4. assumption.
            * assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H0) as H5. destruct H5.
            apply atomin_add_double. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H0) as H5. destruct H5. assumption.
        + rewrite <- H' in H1. rewrite add_union_extrac in H1. 
        apply add_union_remove in H1. rewrite H1 in H2. rewrite <- add_union_extrac in H2. rewrite <- add_union_extrac in H2.
        specialize (IHn G1 ((G' ⨣ p) ⨣ p) op H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1 ,(☉ m2); repeat split; subst.
            * assumption.
            * rewrite add_union_extrac. constructor 4. rewrite <- add_union_extrac. 
            rewrite <- add_union_extrac. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H0) as H5. destruct H5. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a H0) as H5. destruct H5. 
            apply atomin_add_double_option. assumption.
    - subst. apply add_in_union in H1 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [G' H'].
        +rewrite <- H' in H1. rewrite union_comm in H1. rewrite add_union_extrac in H1.
        apply add_union_remove in H1. rewrite union_comm in H1. rewrite H1 in H2.
        rewrite (union_comm G' G2) in H2. rewrite <- add_union_extrac in H2. 
        rewrite union_comm in H2.
        specialize (IHn (G' ⨣ a) G2 op H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, (☉ m1), m2; repeat split; subst.
            * constructor 6. assumption.
            * assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H5. destruct H5.
            apply atomin_andr. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H5. destruct H5. assumption.
        + rewrite <- H' in H1. rewrite add_union_extrac in H1. 
        apply add_union_remove in H1. rewrite H1 in H2. rewrite <- add_union_extrac in H2.
        specialize (IHn G1 (G' ⨣ a) op H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        exists c, m1 ,(☉ m2); repeat split; subst.
            * assumption.
            * rewrite add_union_extrac. constructor 6. rewrite <- add_union_extrac. assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H5. destruct H5.
            assumption.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H5. destruct H5.
            rewrite atomin_option_destruct in H3. rewrite atomin_option_destruct.
            destruct H3.
                {
                    left. apply atomin_andr. assumption.
                }
                {
                    right. assumption.
                }
    - subst. apply add_in_union in H1 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [G' H'].
    +rewrite <- H' in H1. rewrite union_comm in H1. rewrite add_union_extrac in H1.
    apply add_union_remove in H1. rewrite union_comm in H1. rewrite H1 in H2.
    rewrite (union_comm G' G2) in H2. rewrite <- add_union_extrac in H2. 
    rewrite union_comm in H2.
    specialize (IHn (G' ⨣ b) G2 op H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
    exists c, (☉ m1), m2; repeat split; subst.
        * constructor 7. assumption.
        * assumption.
        * unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H5. destruct H5.
        apply atomin_andl. assumption.
        * unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H5. destruct H5. assumption.
    + rewrite <- H' in H1. rewrite add_union_extrac in H1. 
    apply add_union_remove in H1. rewrite H1 in H2. rewrite <- add_union_extrac in H2.
    specialize (IHn G1 (G' ⨣ b) op H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
    exists c, m1 ,(☉ m2); repeat split; subst.
        * assumption.
        * rewrite add_union_extrac. constructor 7. rewrite <- add_union_extrac. assumption.
        * unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H5. destruct H5.
        assumption.
        * unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H5. destruct H5.
        rewrite atomin_option_destruct in H3. rewrite atomin_option_destruct.
        destruct H3.
            {
                left. apply atomin_andl. assumption.
            }
            {
                right. assumption.
            }
    - subst. specialize (IHn G1 G2 (Some a) H1) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
    exists c, m1, (☉ m2); repeat split; subst.
        + assumption.
        + constructor 8. assumption.
        +unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H5. destruct H5.
        assumption.
        + unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H5. destruct H5.
        rewrite atomin_option_destruct in H3. rewrite atomin_option_destruct.
        destruct H3.
            *left; assumption.
            *right. simpl. apply atomin_orr. rewrite emp_add. simpl in H3. assumption.
    - subst. specialize (IHn G1 G2 (Some b) H1) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
    exists c, m1, (☉ m2); repeat split; subst.
        + assumption.
        + constructor 9. assumption.
        +unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H5. destruct H5.
        assumption.
        + unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H5. destruct H5.
        rewrite atomin_option_destruct in H3. rewrite atomin_option_destruct.
        destruct H3.
            *left; assumption.
            *right. simpl. apply atomin_orl. rewrite emp_add. simpl in H3. assumption.
    - subst. rewrite <- add_union_extrac in H1.
    specialize (IHn G1 (G2 ⨣ a) (Some b) H1) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
    exists c, m1, (☉ m2); repeat split; subst.
        + assumption.
        + constructor 12. rewrite <- add_union_extrac. assumption.
        + unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H5. destruct H5.
        assumption.
        + unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H5. destruct H5.
        simpl.  simpl in H3. 
        specialize (atomin_imp G2 ∅ a0 a b) as H4. rewrite emp_add in H4.
        rewrite union_comm in H4. rewrite add_union_singl in H4. apply H4 in H3.
        rewrite emp_add in H3. rewrite union_comm in H3. rewrite add_union_singl in H3.
        assumption.
    - subst.
    specialize (IHn1 G1  G2 (Some a) H2) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
    specialize (IHn2 G1  G2 (Some b) H5) as IH. destruct IH as [c' [m1' [m2' [IH1' [IH2' IH3']]]]].
    exists (c ∧ c'), (m1 ≍ m1'), ((☉ m2) ≍ (☉ m2')); repeat split; subst.
        + constructor 5; assumption.
        + constructor 5; rewrite add_union_singl.
            * constructor 6. rewrite <- add_union_singl. assumption.
            * constructor 7. rewrite <- add_union_singl. assumption.
        + apply atomsof_and_destruct in H0; destruct H0.
            * unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6. assumption.
            * unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6. assumption.
        + apply atomsof_and_destruct in H0; destruct H0; simpl in *.
            *unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
            apply atomin_andr. assumption.
            * unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
            apply atomin_andl. assumption.
    - apply add_in_union in H2 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [G' H'].
        + rewrite <- H' in H2. rewrite union_comm in H2. rewrite add_union_extrac in H2.
        apply add_union_remove in H2. 
        rewrite H2 in H3. rewrite <- add_union_extrac in H3. rewrite union_comm in H3.
        rewrite H2 in H5. rewrite <- add_union_extrac in H5. rewrite union_comm in H5.
        specialize (IHn1 (G' ⨣ b) G2 op H5) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        specialize (IHn2 (G' ⨣ a) G2 op H3) as IH. destruct IH as [c' [m1' [m2' [IH1' [IH2' IH3']]]]].
        exists (c ∨ c'), ((☉ m1) ≍ (☉ m1')) ,(m2' ≍ m2); repeat split; subst.
            * constructor 10.
                ** constructor 9. assumption.
                ** constructor 8. assumption.
        * rewrite add_union_singl. constructor 10;try rewrite <- add_union_singl; try assumption.
        * apply atomsof_or_destruct in H6; destruct H6.
            ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
            apply atomin_orl. assumption. 
            ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
            apply atomin_orr. assumption. 
        * apply atomsof_or_destruct in H6; destruct H6.
            ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
            assumption.
            ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
            assumption.
        +rewrite <- H' in H2. rewrite add_union_extrac in H2.
        apply add_union_remove in H2. 
        rewrite H2 in H3. rewrite <- add_union_extrac in H3. 
        rewrite H2 in H5. rewrite <- add_union_extrac in H5. 
        specialize (IHn1 G1 (G' ⨣ b) op H5) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        specialize (IHn2 G1 (G' ⨣ a) op H3) as IH. destruct IH as [c' [m1' [m2' [IH1' [IH2' IH3']]]]].
        exists (c ∧ c') ,(m1 ≍ m1'), ((☉ m2) ≍ (☉ m2')); repeat split; subst.
            * constructor 5; try assumption.
            * rewrite add_union_extrac. constructor 10.
                ** rewrite add_union_singl. rewrite ms_add_comm. constructor 7. 
                rewrite <- add_union_singl. assumption.
                ** rewrite add_union_singl. rewrite ms_add_comm. constructor 6.
                rewrite <- add_union_singl. assumption.
            * apply atomsof_and_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                assumption.
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                assumption.
            * apply atomsof_and_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                rewrite atomin_option_destruct. rewrite atomin_option_destruct in H2. destruct H2.
                    *** left.  apply atomin_orl. assumption.
                    *** right. assumption.
                **  unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                rewrite atomin_option_destruct. rewrite atomin_option_destruct in H2. destruct H2.
                    *** left.  apply atomin_orr. assumption.
                    *** right. assumption.
    - apply add_in_union in H2 as H'; destruct H' as [H' | H']; apply in_add_unfold in H'; destruct H' as [G' H'].
        + rewrite <- H' in H2. rewrite union_comm in H2. rewrite add_union_extrac in H2.
        apply add_union_remove in H2. 
        rewrite H2 in H3. 
        rewrite H2 in H5. rewrite <- add_union_extrac in H5. rewrite union_comm in H5.
        specialize (IHn1 (G' ⨣ b) G2 op H5) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        specialize (IHn2 G2 G' (Some a) H3) as IH. destruct IH as [c' [m1' [m2' [IH1' [IH2' IH3']]]]].
        exists (c' ⊃ c), ( ☉ ((☉ m1) ≍ m2')) ,(m2 ≍ m1'); repeat split; subst.
            * rewrite <- add_union_singl. constructor 12. 
            rewrite add_union_singl. rewrite ms_add_comm. constructor 13.  
                ** rewrite <- add_union_singl. assumption.
                ** rewrite ms_add_comm. constructor 3. assumption.
            * rewrite add_union_singl. constructor 13.
                ** assumption.
                ** rewrite <- add_union_singl. assumption. 
            * apply atomsof_or_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                rewrite atomin_option_destruct in H2. destruct H2.
                    {
                        apply atomin_add. assumption.
                    }
                    {
                        simpl in H2. apply atomin_impl. apply atomin_singl_add. assumption.
                    } 
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                apply atomin_impr. assumption.
                           
            * apply atomsof_or_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                apply atomin_option_add. assumption.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                assumption.
        + rewrite <- H' in H2. rewrite add_union_extrac in H2.
        apply add_union_remove in H2. 
        rewrite H2 in H3. 
        rewrite H2 in H5. rewrite <- add_union_extrac in H5. 
        specialize (IHn1 G1 (G' ⨣ b) op H5) as IH. destruct IH as [c [m1 [m2 [IH1 [IH2 IH3]]]]].
        specialize (IHn2 G1 G' (Some a) H3) as IH. destruct IH as [c' [m1' [m2' [IH1' [IH2' IH3']]]]].
        exists (c ∧ c') ,(m1 ≍ m1'), ((☉ m2) ≍ (☉ m2')); repeat split; subst.
            * constructor 5; try assumption.
            * rewrite add_union_extrac. constructor 13.
                ** rewrite add_union_singl. constructor 7. 
                rewrite <- add_union_singl. assumption.
                ** rewrite add_union_singl. rewrite ms_add_comm. constructor 6.
                rewrite <- add_union_singl. assumption.
            * apply atomsof_and_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                assumption.
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                assumption.
            * apply atomsof_and_destruct in H6; destruct H6.
                ** unfold atoms_incl in IH3. specialize (IH3 a0 H0) as H6. destruct H6.
                rewrite atomin_option_destruct. rewrite atomin_option_destruct in H2. destruct H2.
                    {
                        left. apply atomin_impr. assumption. 
                    }
                    {
                        right. assumption.
                    }
                ** unfold atoms_incl in IH3'. specialize (IH3' a0 H0) as H6. destruct H6.
                simpl in H2. apply atomin_option_add. apply atomin_impl. assumption. 
Qed.

Theorem LK_Interpolation_Theorem: forall G op m, G ⇥ op >< m ->
exists (c : prop) m1 m2, G ⇥ (Some c) >< m1 
/\ {{ c }} ⇥ op >< m2
/\ (atoms_incl c G (option_to_multiset op)).
Proof.
    intros.
    specialize (LKI_Interpol_strong m G ∅ op) as H'.
    rewrite union_idr in H'. 
    apply H' in H.
    destruct H as [c [m1 [m2 [IH1 [IH2 IH3]]]]]. rewrite union_idr in IH2. 
    rewrite option_add_emp in IH3.
    exists c, m1, m2; split; try split; subst; try assumption.
Qed.
