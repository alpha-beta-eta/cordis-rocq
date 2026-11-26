(** * Canonical order for contributions (docs/CONTRIB.md, stage E6c)

    A middleware chain is the list of contributions under one name, and
    its order is meaning: each handler sees what the one before it passed
    on. [Listeners.v] proves confluence only up to [Permutation], so the
    order there is whatever the schedule left. Here the chain is the
    contributions sorted by a total order the host fixes ([ele]), so it is
    a function of the multiset alone:

    - [sort_unique]: two sorted permutations of one another are equal;
    - [chain_perm]: the chain for a name depends on the multiset alone, so
      any dispatch that folds over it does too;
    - [parties_perm]: the entries in a conflict, listed in the same order,
      depend on the multiset alone (E6a returned [RConflict] bare);
    - [prio_order]: ordering by priority first, then by any total order to
      break ties, meets the hypotheses, so a plugin that must run earlier
      raises its priority instead of loading first;
    - [chain_confluence], [chain_static]: through the summary theorem, two
      schedules (and static assembly) build the same chain for every name.

    The order says which handler runs first; it does not make two handlers
    that do not commute agree. It makes the result depend on the set of
    contributions, which is what confluence asks. *)

From Stdlib Require Import RelationClasses List PeanoNat Bool Permutation Sorting.
From Cordis Require Import Prelude Service ServiceSeq Calculus Recovery Compose
  Confluence SpawnConf Dynamic Summary Listeners Contrib ContribConf.
Import ListNotations.

(** ** Sorting by a total order, and its uniqueness *)
Section Sort.
  Context {A : Type} (le : A -> A -> bool).
  Hypothesis le_total : forall a b, le a b = true \/ le b a = true.
  Hypothesis le_trans : forall a b c, le a b = true -> le b c = true -> le a c = true.
  Hypothesis le_antisym : forall a b, le a b = true -> le b a = true -> a = b.

  Definition R (a b : A) : Prop := le a b = true.

  Fixpoint insert (e : A) (l : list A) : list A :=
    match l with
    | [] => [e]
    | x :: r => if le e x then e :: x :: r else x :: insert e r
    end.

  Fixpoint isort (l : list A) : list A :=
    match l with
    | [] => []
    | x :: r => insert x (isort r)
    end.

  Lemma insert_perm e l : Permutation (insert e l) (e :: l).
  Proof.
    induction l as [|x r IH]; cbn; [reflexivity|].
    destruct (le e x); [reflexivity|].
    transitivity (x :: e :: r); [apply perm_skip, IH | apply perm_swap].
  Qed.

  Lemma isort_perm l : Permutation (isort l) l.
  Proof.
    induction l as [|x r IH]; cbn; [reflexivity|].
    transitivity (x :: isort r); [apply insert_perm | apply perm_skip, IH].
  Qed.

  Lemma not_le e x : le e x = false -> le x e = true.
  Proof. intros H; destruct (le_total e x) as [E|E]; [congruence | exact E]. Qed.

  Lemma insert_hd x e r : HdRel R x r -> R x e -> HdRel R x (insert e r).
  Proof.
    intros Hr Hxe; destruct r as [|y r']; cbn; [constructor; exact Hxe|].
    destruct (le e y); constructor; [exact Hxe | exact (HdRel_inv Hr)].
  Qed.

  Lemma insert_sorted e l : Sorted R l -> Sorted R (insert e l).
  Proof.
    induction l as [|x r IH]; intros S; cbn; [repeat constructor|].
    destruct (le e x) eqn:E.
    - constructor; [exact S | constructor; exact E].
    - destruct (Sorted_inv S) as [Sr Hr].
      constructor; [exact (IH Sr) | exact (insert_hd x e r Hr (not_le e x E))].
  Qed.

  Lemma isort_sorted l : Sorted R (isort l).
  Proof. induction l as [|x r IH]; cbn; [constructor | apply insert_sorted, IH]. Qed.

  Lemma R_trans : Relations_1.Transitive R.
  Proof. intros a b c; exact (le_trans a b c). Qed.

  Theorem sort_unique l1 l2 :
    StronglySorted R l1 -> StronglySorted R l2 -> Permutation l1 l2 -> l1 = l2.
  Proof.
    revert l2; induction l1 as [|a r1 IH]; intros l2 S1 S2 P.
    - exact (eq_sym (Permutation_nil P)).
    - destruct l2 as [|b r2]; [exfalso; exact (Permutation_nil_cons (Permutation_sym P))|].
      destruct (StronglySorted_inv S1) as [S1' F1].
      destruct (StronglySorted_inv S2) as [S2' F2].
      assert (Eab : a = b).
      { pose proof (Permutation_in a P (or_introl eq_refl)) as Ha.
        pose proof (Permutation_in b (Permutation_sym P) (or_introl eq_refl)) as Hb.
        destruct Ha as [Ha|Ha]; [exact (eq_sym Ha)|].
        destruct Hb as [Hb|Hb]; [exact Hb|].
        apply le_antisym; [exact (proj1 (Forall_forall _ _) F1 b Hb)
                          | exact (proj1 (Forall_forall _ _) F2 a Ha)]. }
      subst b; f_equal; apply IH; [exact S1' | exact S2' | exact (Permutation_cons_inv P)].
  Qed.

  Corollary isort_perm_eq l l' : Permutation l l' -> isort l = isort l'.
  Proof.
    intros P; apply sort_unique;
      [apply Sorted_StronglySorted; [exact R_trans | apply isort_sorted]
      |apply Sorted_StronglySorted; [exact R_trans | apply isort_sorted]|].
    transitivity l; [apply isort_perm|].
    transitivity l'; [exact P | symmetry; apply isort_perm].
  Qed.
End Sort.

(** ** Priority first, then a tie-break *)
Section Prio.
  Context {A : Type} (key : A -> nat) (tie : A -> A -> bool).
  Hypothesis tie_total : forall a b, tie a b = true \/ tie b a = true.
  Hypothesis tie_trans : forall a b c, tie a b = true -> tie b c = true -> tie a c = true.
  Hypothesis tie_antisym : forall a b, tie a b = true -> tie b a = true -> a = b.

  (** Greater priority runs first. *)
  Definition prio_le (a b : A) : bool :=
    Nat.ltb (key b) (key a) || (Nat.eqb (key a) (key b) && tie a b).

  Lemma prio_order :
    (forall a b, prio_le a b = true \/ prio_le b a = true) /\
    (forall a b c, prio_le a b = true -> prio_le b c = true -> prio_le a c = true) /\
    (forall a b, prio_le a b = true -> prio_le b a = true -> a = b).
  Proof.
    unfold prio_le; repeat split.
    - intros a b.
      destruct (Nat.lt_trichotomy (key a) (key b)) as [H|[H|H]].
      + right; apply orb_true_iff; left; apply Nat.ltb_lt; exact H.
      + rewrite H, Nat.eqb_refl, Nat.ltb_irrefl; cbn.
        destruct (tie_total a b) as [T|T]; [left|right]; exact T.
      + left; apply orb_true_iff; left; apply Nat.ltb_lt; exact H.
    - intros a b c H1 H2.
      apply orb_true_iff in H1, H2; apply orb_true_iff.
      destruct H1 as [H1|H1], H2 as [H2|H2];
        try apply andb_true_iff in H1; try apply andb_true_iff in H2.
      + left; apply Nat.ltb_lt; apply Nat.ltb_lt in H1, H2; eapply Nat.lt_trans; eassumption.
      + left; destruct H2 as [H2 _]; apply Nat.eqb_eq in H2; apply Nat.ltb_lt in H1;
          apply Nat.ltb_lt; rewrite <- H2; exact H1.
      + left; destruct H1 as [H1 _]; apply Nat.eqb_eq in H1; apply Nat.ltb_lt in H2;
          apply Nat.ltb_lt; rewrite H1; exact H2.
      + right; destruct H1 as [E1 T1], H2 as [E2 T2]; apply Nat.eqb_eq in E1, E2.
        apply andb_true_iff; split; [apply Nat.eqb_eq; congruence | exact (tie_trans a b c T1 T2)].
    - intros a b H1 H2.
      apply orb_true_iff in H1, H2.
      destruct H1 as [H1|H1], H2 as [H2|H2].
      + apply Nat.ltb_lt in H1, H2; exfalso; exact (Nat.lt_asymm _ _ H1 H2).
      + apply andb_true_iff in H2; destruct H2 as [E _]; apply Nat.eqb_eq in E;
          apply Nat.ltb_lt in H1; exfalso; rewrite E in H1; exact (Nat.lt_irrefl _ H1).
      + apply andb_true_iff in H1; destruct H1 as [E _]; apply Nat.eqb_eq in E;
          apply Nat.ltb_lt in H2; exfalso; rewrite E in H2; exact (Nat.lt_irrefl _ H2).
      + apply andb_true_iff in H1, H2; exact (tie_antisym a b (proj2 H1) (proj2 H2)).
  Qed.
End Prio.

(** ** Chains and conflict parties on contribution keys *)
Section Chains.
  Context (Tag Name V : Type).
  Context (tag_eq_dec : forall x y : Tag, {x = y} + {x <> y}).
  Context (name_eq_dec : forall x y : Name, {x = y} + {x <> y}).
  Context (v_eq_dec : forall x y : V, {x = y} + {x <> y}).
  Context (public : Name -> bool) (prio : V -> nat).
  Context (ele : Entry Tag Name V -> Entry Tag Name V -> bool).
  Hypothesis ele_total : forall a b, ele a b = true \/ ele b a = true.
  Hypothesis ele_trans : forall a b c, ele a b = true -> ele b c = true -> ele a c = true.
  Hypothesis ele_antisym : forall a b, ele a b = true -> ele b a = true -> a = b.

  Local Notation CS := (Contrib Tag Name V tag_eq_dec name_eq_dec v_eq_dec public prio).
  Local Notation Entry := (Entry Tag Name V).
  Local Notation visible_to := (visible_to Tag Name V tag_eq_dec name_eq_dec public).
  Local Notation top := (top Tag Name V tag_eq_dec name_eq_dec v_eq_dec prio).

  (** The chain under name [x]: every contribution to it, in order. *)
  Definition chain (s : list Entry) (x : Name) : list Entry :=
    isort ele (filter (fun e => neqb Name name_eq_dec (ename Tag Name V e) x) s).

  (** The entries a read of [x] by [q] finds in conflict, in order. *)
  Definition parties (s : list Entry) (q : Tag) (x : Name) : list Entry :=
    isort ele (top (filter (visible_to q x) s)).

  Theorem chain_perm s s' x : Permutation s s' -> chain s x = chain s' x.
  Proof.
    intros P; apply (isort_perm_eq ele ele_total ele_trans ele_antisym).
    exact (filter_perm Tag Name V _ s s' P).
  Qed.

  Theorem parties_perm s s' q x : Permutation s s' -> parties s q x = parties s' q x.
  Proof.
    intros P; apply (isort_perm_eq ele ele_total ele_trans ele_antisym).
    apply top_perm, filter_perm, P.
  Qed.

  (** Every party is a live contribution visible to [q]. *)
  Lemma parties_in s q x e :
    In e (parties s q x) -> In e s /\ visible_to q x e = true.
  Proof.
    intros H; unfold parties in H.
    apply (Permutation_in _ (isort_perm ele _)) in H.
    unfold top in H; apply nodup_In, filter_In in H; destruct H as [H _].
    apply filter_In in H; exact H.
  Qed.

  (** ** Through the summary theorem *)
  Section Summaries.
    Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
    Context {C : Type} (prog : C -> @Component K CS C).

    Lemma agree_chain l1 l2 (γ1 γ2 : @State K CS C) :
      AgreeL CS l1 l2 γ1 γ2 ->
      forall k b1 b2, binds CS γ1 k = Some b1 -> binds CS γ2 k = Some b2 ->
        (forall x, chain (bst CS b1) x = chain (bst CS b2) x) /\
        (forall q x, parties (bst CS b1) q x = parties (bst CS b2) q x).
    Proof.
      intros A k b1 b2 H1 H2.
      destruct A as (_ & _ & _ & _ & _ & _ & _ & _ & St).
      pose proof (St k b1 b2 H1 H2) as P.
      split; [intros x; exact (chain_perm _ _ x P) | intros q x; exact (parties_perm _ _ q x P)].
    Qed.

    Theorem chain_confluence Kb rank Rb ins (γ1 γ2 : @State K CS C) rs1 rs2 :
      Covers CS prog (contrib_meet Tag Name V tag_eq_dec name_eq_dec v_eq_dec public prio) ->
      Obligations CS prog Kb rank Rb -> TotalProv CS prog ->
      DRun K_eq_dec CS prog (@init K CS C) [] ins γ1 rs1 ->
      DRun K_eq_dec CS prog (@init K CS C) [] ins γ2 rs2 ->
      quiet K_eq_dec CS prog γ1 -> quiet K_eq_dec CS prog γ2 -> NoFailed CS γ1 -> NoFailed CS γ2 ->
      forall k b1 b2, binds CS γ1 k = Some b1 -> binds CS γ2 k = Some b2 ->
        (forall x, chain (bst CS b1) x = chain (bst CS b2) x) /\
        (forall q x, parties (bst CS b1) q x = parties (bst CS b2) q x).
    Proof.
      intros HG HO HT R1 R2 Q1 Q2 N1 N2.
      exact (agree_chain _ _ γ1 γ2
               (summary_confluence K_eq_dec CS prog _ Kb rank Rb ins γ1 γ2 rs1 rs2
                  (contrib_hyps Tag Name V tag_eq_dec name_eq_dec v_eq_dec public prio)
                  HG HO HT R1 R2 Q1 Q2 N1 N2)).
    Qed.

    Theorem chain_static Kb rank Rb ins (γ γs : @State K CS C) rs rss :
      Covers CS prog (contrib_meet Tag Name V tag_eq_dec name_eq_dec v_eq_dec public prio) ->
      Obligations CS prog Kb rank Rb -> TotalProv CS prog ->
      DRun K_eq_dec CS prog (@init K CS C) [] ins γ rs ->
      DRun K_eq_dec CS prog (@init K CS C) [] (map IIns (scomps ins)) γs rss ->
      quiet K_eq_dec CS prog γ -> quiet K_eq_dec CS prog γs -> NoFailed CS γ -> NoFailed CS γs ->
      forall k b bs, binds CS γ k = Some b -> binds CS γs k = Some bs ->
        (forall x, chain (bst CS b) x = chain (bst CS bs) x) /\
        (forall q x, parties (bst CS b) q x = parties (bst CS bs) q x).
    Proof.
      intros HG HO HT R1 R2 Q1 Q2 N1 N2.
      exact (agree_chain _ _ γ γs
               (summary_static K_eq_dec CS prog _ Kb rank Rb ins γ γs rs rss
                  (contrib_hyps Tag Name V tag_eq_dec name_eq_dec v_eq_dec public prio)
                  HG HO HT R1 R2 Q1 Q2 N1 N2)).
    Qed.
  End Summaries.
End Chains.
