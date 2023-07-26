Require Import PeanoNat.
Require Import Lang.

(* we do generalization later since we need decidablity function and
it complicates things *)
(* Variable U : Type. *)
Definition U := nat .


Definition multiset := U -> nat.

Definition In (x : U) (A : multiset)  : Prop := 1 <= A x.
Definition Included (A B : multiset) : Prop := forall x, A x <= B x.
Definition EmptySet : multiset := fun (x : U) => 0.

Definition Singleton (x:U) : multiset :=
    fun (x' : U) => match ( x =? x') with
        | true => 1
        |false => 0
    end.

Definition Union (A B : multiset) : multiset :=
    fun (x : U) => (A x) + (B x).

Definition Intersection (A B : multiset) : multiset :=
    fun (x : U) => min (A x) (B x).

Definition SAdd (A : multiset) (x : U) : multiset :=
    fun (x' : U) => match ( x =? x') with
        | true => S (A x')
        |false => A x'
    end.

Definition Remove (A : multiset) (x : U) : multiset :=
    fun (x' : U) => match ( x =? x') with
        | true => pred (A x')
        |false => A x'
    end.

Definition Diff (A B : multiset) : multiset :=
    fun (x : U) => (A x) - (B x).

Definition Equal (A B : multiset) : Prop :=
    forall (x : U), (A x) = (B x).

    Notation "∅" := EmptySet.
    Infix "∪" := Union (left associativity, at level 62).
    Infix "∩" := Intersection (left associativity, at level 62).
    Infix "\" := Diff (left associativity, at level 63).
    Infix "∈" := In (at level 60).
    Infix "⊆" := Included (at level 71).
    Infix "⩵" := Equal (at level 70).
    Infix "⨣" := SAdd (at level 64).
    Infix "⨪" := Remove (at level 65).
    Notation "{{ n }}" := (Singleton n).
Axiom Extensionality_multiset : forall A B, A ⩵ B -> A = B.
Lemma emp_minimum : forall s, ∅ ⊆ s. 
Proof. 
    intros. unfold Included. unfold EmptySet. 
    intros. apply (le_0_n). 
Qed.

Lemma emp_min : forall s, s ⊆ ∅ -> ∅ = s.
Proof.
    intros. apply Extensionality_multiset.  unfold Included in H. unfold EmptySet in H.
    assert (forall x : U, s x = 0).
        - intros. rewrite <- Nat.le_0_r. auto.
        - unfold Equal. intros. unfold EmptySet. auto.
Qed.

Lemma incl_reflexive : forall s1, s1 ⊆ s1.
Proof.
    unfold "⊆". intros. auto.
Qed.

Lemma incl_transitive : forall s1 s2 s3, s1 ⊆ s2 -> s2 ⊆ s3 -> s1 ⊆ s3.
Proof.
    unfold "⊆". intros. apply (Nat.le_trans (s1 x) (s2 x) (s3 x)); auto.
Qed.

Lemma extensionality : forall s1 s2, s1 ⊆ s2 -> s2 ⊆ s1 -> s1 = s2.
Proof.
    intros. apply Extensionality_multiset. unfold "⊆" in *; unfold "⩵"; intros. apply Nat.le_antisymm; auto.
Qed.

Lemma extensionality_iff : forall s1 s2, (s1 ⊆ s2 /\ s2 ⊆ s1) <-> s1 = s2.
Proof.
    split; intros; unfold "⊆" in *; try split.
        - apply Extensionality_multiset; unfold "⩵". destruct H. intros. apply Nat.le_antisymm; auto.
        - intros. rewrite H. apply Nat.le_refl.
        - intros. rewrite H. apply Nat.le_refl.
Qed.
Lemma mem_incl : forall s1 s2, s1 ⊆ s2 -> forall n, n ∈ s1 -> n ∈ s2.
    unfold "⊆"; unfold "∈"; intros.
    apply (Nat.le_trans (1) (s1 n) (s2 n)); auto.
Qed.

Lemma union_idl : forall s, ∅ ∪ s = s. 
Proof. 
    intros; apply Extensionality_multiset; unfold "∪"; unfold "⩵"; simpl; auto. 
Qed.

Lemma union_idr : forall s, s ∪ ∅ = s. 
Proof. 
    intros; apply Extensionality_multiset; unfold "∪"; unfold "⩵"; simpl; auto. 
Qed.

Lemma intersection_empl : forall s, ∅ ∩ s = ∅. 
Proof. 
    intros; apply Extensionality_multiset; unfold "∩"; unfold "⩵"; simpl; auto. 
Qed.

Lemma intersection_empr : forall s, s ∩ ∅ = ∅. 
Proof. 
    intros;apply Extensionality_multiset; unfold "∩"; unfold "⩵"; unfold "∅"; simpl; intros; auto. apply Nat.min_0_r. 
Qed.

Lemma single_add: forall a b, {{ a }} ⨣ b = {{ b }} ⨣ a.
Proof.
    intros; apply Extensionality_multiset; unfold "⩵". unfold "⨣". unfold Singleton. intros. 
    replace (b =? a) with (a =? b). destruct (a =? x) eqn: E; destruct (b =? x) eqn: E'; simpl;try reflexivity.
        - rewrite Nat.eqb_sym; reflexivity.
Qed.

Lemma le_one_cases: forall n m, 1 <= n + m -> 1 <= n \/ 1 <= m.
Proof.
    intros. induction n.
        - auto.
        - simpl in H. rewrite <- Nat.succ_le_mono in H. specialize (Nat.add_nonneg_cases n m H) as H'.
        destruct H'.
            + left; rewrite <- Nat.succ_le_mono; assumption.
            + destruct m.
                * left. rewrite <- Nat.succ_le_mono. rewrite plus_n_O. assumption.
                * assert (1 <= n + S m).
                {
                    rewrite Nat.add_succ_r. rewrite <- Nat.succ_le_mono. 
                    apply le_0_n.
                }
                {
                    apply IHn in H1. destruct H1.
                    - left. apply Nat.le_le_succ_r. assumption.
                    - right. assumption.
                }
Qed.

Lemma le_add_r2: forall a b c, a <= b -> a <= b + c.
Proof.
    intros. induction c.
        - rewrite <- plus_n_O. assumption.
        -  rewrite Nat.add_succ_r. apply Nat.le_le_succ_r. assumption.
Qed. 
Lemma union_mem: forall s1 s2 x, x ∈ (s1 ∪ s2) <-> (x ∈ s1) \/ (x ∈ s2).
Proof.
    intros; split.
        - intros. unfold In in *. unfold "∪" in H.
        apply le_one_cases. assumption.
        - intros H; destruct H; unfold In in *; unfold "∪" .
            + apply le_add_r2. assumption.
            + rewrite Nat.add_comm. apply le_add_r2. assumption.
Qed.

Lemma union_comm: forall s1 s2, s1 ∪ s2 = s2 ∪ s1.
Proof.
    intros;apply Extensionality_multiset; unfold "∪"; unfold "⩵"; intros.
    apply Nat.add_comm.
Qed.
Lemma inter_comm: forall s1 s2, s1 ∩ s2 = s2 ∩ s1.
Proof.
    intros;apply Extensionality_multiset; unfold "∩"; unfold "⩵"; intros.
    apply Nat.min_comm.
Qed.

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

Definition option_add (s : multiset) (op : option prop) : multiset :=
    match op with
    | None => s
    | Some p => s ⨣ p
    end.

Lemma add_sing_refl: forall p q, {{p}} ⨣ q = {{q}} ⨣ p.
Proof.
    intros. apply equal_ext. unfold Equal. intros. unfold Singleton. unfold "⨣".
    destruct (PeanoNat.Nat.eqb q x) ,(PeanoNat.Nat.eqb p x); simpl; try reflexivity.
Qed.
Lemma EmptySetDef: ∅ = fun (x : U) => 0.
Proof.
    apply equal_ext. unfold Equal. intros. unfold "∅". reflexivity.
Qed.
Lemma add_in_union: forall s1 s2 s3 p, s1 ⨣ p = s2 ∪ s3 -> p ∈ s2 \/ p ∈ s3.
Proof. intros.
    rewrite equal_ext in H. unfold Equal in H. specialize (H p) as H'.
    unfold "⨣" in H'. rewrite PeanoNat.Nat.eqb_refl in H'.
    unfold "∪" in H'. assert (1 <= S (s1 p)).
        * apply le_n_S. apply le_0_n.
        * rewrite H' in H0. apply le_one_cases in H0. destruct H0.
            **left. assumption.
            **right. assumption.
Qed.
Lemma in_add_unfold: forall s1 p, p ∈ s1 -> exists s', s' ⨣ p = s1.
Proof.
    intros. exists (s1 ⨪ p). rewrite equal_ext. unfold Equal. intros. unfold "⨪". unfold "⨣". 
    destruct (PeanoNat.Nat.eqb p x) eqn: E.
    - apply PeanoNat.Nat.eqb_eq in E. subst. unfold In in H. 
    apply (PeanoNat.Nat.lt_succ_pred 0). assumption.
    - reflexivity.
Qed.
Lemma add_union_remove: forall s1 s2 p, s1 ⨣ p = s2 ⨣ p -> s1 = s2.
Proof.
    intros. rewrite equal_ext. unfold Equal. intros.
    rewrite equal_ext in H. unfold Equal in H. specialize (H x) as H'.
    unfold "⨣" in H'. destruct (PeanoNat.Nat.eqb p x); inversion H'; subst; reflexivity.
Qed.
Lemma add_union_extrac: forall s1 s2 p, s1 ∪ (s2 ⨣ p) = (s1 ∪ s2) ⨣ p.
Proof.
    intros. rewrite equal_ext. unfold Equal. intros.
    unfold "⨣". unfold "∪".
    destruct (PeanoNat.Nat.eqb p x).
    - rewrite PeanoNat.Nat.add_succ_r. reflexivity.
    - reflexivity.
Qed.
Lemma le_S_one: forall n, 1 <= S n.
Proof.
    intros. apply le_n_S. apply le_0_n.
Qed.

Definition option_to_multiset (op : option prop) :=
    match op with
    | None => ∅
    | Some p => {{ p }}
    end.
Lemma in_add: forall G a (p : prop), a ∈ G -> a ∈ (G ⨣ p).
Proof.
    intros. unfold In in *. unfold SAdd. destruct (PeanoNat.Nat.eqb p a).
        - apply le_S_one.
        - assumption.
Qed.
Lemma In_emp_false : forall x, x ∈ ∅ -> False.
Proof.
    intros. unfold In in H. unfold "∅" in H. inversion H.
Qed.
