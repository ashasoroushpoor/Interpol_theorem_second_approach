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
