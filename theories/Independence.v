(** * Independence of effects (§3.4.1, read for effect functions) *)

From Stdlib Require Import List Lia Bool Permutation PeanoNat.
From Cordis Require Import Prelude Twisted EffectFun.
Import ListNotations.

(** ** Generated submonoids of End Γ *)
Section Generated.
  Context {Γ : Type}.

  (** ⟨S⟩: the least submonoid of End Γ containing S. *)
  Inductive Generated (S : End Γ -> Prop) : End Γ -> Prop :=
  | gen_base h : S h -> Generated S h
  | gen_id : Generated S id
  | gen_comp h1 h2 : Generated S h1 -> Generated S h2 -> Generated S (h1 ∘ h2).

  Lemma generated_submonoid (S : End Γ -> Prop) :
    IsSubmonoid comp id (Generated S).
  Proof. split; [apply gen_id | apply gen_comp]. Qed.

  (** ⟨S⟩ ⊆ T whenever S ⊆ ⟨T⟩. *)
  Lemma generated_sub (S T : End Γ -> Prop) :
    (forall h, S h -> Generated T h) ->
    forall h, Generated S h -> Generated T h.
  Proof.
    intros HST h Hh; induction Hh.
    - auto.
    - apply gen_id.
    - apply gen_comp; assumption.
  Qed.

  Lemma generated_mono (S T : End Γ -> Prop) :
    (forall h, S h -> T h) -> forall h, Generated S h -> Generated T h.
  Proof. intros H; apply generated_sub; intros h Hh; apply gen_base; auto. Qed.

  (** Two sets of transformations commute when every element of one commutes
      with every element of the other. *)
  Definition Commute (A B : End Γ -> Prop) : Prop :=
    forall a b, A a -> B b -> a ∘ b = b ∘ a.

  (** Lemma 41(1): commutation is settled on the generators. *)
  Lemma generated_commute (S T : End Γ -> Prop) :
    Commute S T -> Commute (Generated S) (Generated T).
  Proof.
    intros H.
    assert (H1 : forall a b, Generated S a -> T b -> a ∘ b = b ∘ a).
    { intros a b Ha Hb; induction Ha as [a Ha| |h1 h2 _ IH1 _ IH2].
      - apply H; assumption.
      - reflexivity.
      - transitivity (h1 ∘ (h2 ∘ b)); [reflexivity|].
        rewrite IH2.
        transitivity (h1 ∘ b ∘ h2); [reflexivity|].
        rewrite IH1; reflexivity. }
    intros a b Ha Hb; induction Hb as [b Hb| |h1 h2 _ IH1 _ IH2].
    - apply H1; assumption.
    - reflexivity.
    - transitivity (a ∘ h1 ∘ h2); [reflexivity|].
      rewrite IH1.
      transitivity (h1 ∘ (a ∘ h2)); [reflexivity|].
      rewrite IH2; reflexivity.
  Qed.
End Generated.

(** ** The transformation monoid 𝔐(e) (Definition 40) *)
Section TransformationMonoid.
  Context {Γ : Type}.

  (** The generators: the forward map of e and every inverse e yields. *)
  Definition Gen (e : Eff Γ) (h : End Γ) : Prop :=
    h = fst ∘ e \/ exists γ, h = snd (e γ).

  Definition M (e : Eff Γ) : End Γ -> Prop := Generated (Gen e).

  Lemma Gen_M (e : Eff Γ) h : Gen e h -> M e h.
  Proof. apply gen_base. Qed.

  Lemma fwd_M (e : Eff Γ) : M e (fst ∘ e).
  Proof. apply gen_base; left; reflexivity. Qed.

  Lemma inv_M (e : Eff Γ) γ : M e (snd (e γ)).
  Proof. apply gen_base; right; exists γ; reflexivity. Qed.

  (** Gen(⌜f, g⌝) = {f, g}. The inclusion ⊇ needs Γ to be inhabited: on an
      empty Γ the set {pr₂(e γ) | γ ∈ Γ} is empty. (There f = g anyway, so
      the two sets still agree classically, but not constructively.) *)
  Lemma Gen_induced (p : Twisted Γ) (h : End Γ) :
    inhabited Γ -> (Gen (induced p) h <-> h = fst p \/ h = snd p).
  Proof.
    intros [γ]; split.
    - intros [-> | [γ' ->]]; [left | right]; reflexivity.
    - intros [-> | ->]; [left; reflexivity | right; exists γ; reflexivity].
  Qed.

  (** The inclusion ⊆ holds unconditionally. *)
  Lemma Gen_induced_sub (p : Twisted Γ) (h : End Γ) :
    Gen (induced p) h -> h = fst p \/ h = snd p.
  Proof. intros [-> | [γ' ->]]; [left | right]; reflexivity. Qed.

  (** Lemma 41(2), in the form of the notes: 𝔐(e₁ ⋄ e₂) ⊆ ⟨Gen e₁ ∪ Gen e₂⟩. *)
  Lemma M_diamond_gen (e1 e2 : Eff Γ) h :
    M (e1 ⋄ e2) h -> Generated (fun h => Gen e1 h \/ Gen e2 h) h.
  Proof.
    apply generated_sub; intros h' [-> | [γ ->]].
    - change (Generated (fun h => Gen e1 h \/ Gen e2 h)
                ((fst ∘ e1) ∘ (fst ∘ e2))).
      apply gen_comp; apply gen_base; [left | right]; left; reflexivity.
    - change (Generated (fun h => Gen e1 h \/ Gen e2 h)
                (snd (e2 γ) ∘ snd (e1 (fst (e2 γ))))).
      apply gen_comp; apply gen_base.
      + right; right; exists γ; reflexivity.
      + left; right; exists (fst (e2 γ)); reflexivity.
  Qed.

  (** Lemma 41(2), in the form of the paper: 𝔐(e₁ ⋄ e₂) ⊆ ⟨𝔐(e₁) ∪ 𝔐(e₂)⟩. *)
  Lemma M_diamond (e1 e2 : Eff Γ) h :
    M (e1 ⋄ e2) h -> Generated (fun h => M e1 h \/ M e2 h) h.
  Proof.
    intros H; apply (generated_mono (fun h => Gen e1 h \/ Gen e2 h)).
    - intros h' [H' | H']; [left | right]; apply gen_base; exact H'.
    - apply M_diamond_gen; exact H.
  Qed.

  (** ** Independence (Definition 42) *)
  Definition Independent (e1 e2 : Eff Γ) : Prop :=
    Commute (M e1) (M e2) /\
    (forall g γ, M e2 g -> snd (e1 (g γ)) = snd (e1 γ)) /\
    (forall g γ, M e1 g -> snd (e2 (g γ)) = snd (e2 γ)).

  Lemma independent_sym (e1 e2 : Eff Γ) :
    Independent e1 e2 -> Independent e2 e1.
  Proof.
    intros [Hc [H1 H2]]; repeat split; auto.
    intros a b Ha Hb; symmetry; apply Hc; assumption.
  Qed.

  (** For effects induced by pairs (f₁, g₁), (f₂, g₂), clause (1) is the
      commutation of the four pairs f₁,f₂; g₁,g₂; f₁,g₂; g₁,f₂, and
      clause (2) holds outright. *)
  Theorem induced_independent (f1 g1 f2 g2 : End Γ) :
    f1 ∘ f2 = f2 ∘ f1 -> g1 ∘ g2 = g2 ∘ g1 ->
    f1 ∘ g2 = g2 ∘ f1 -> g1 ∘ f2 = f2 ∘ g1 ->
    Independent (induced (f1, g1)) (induced (f2, g2)).
  Proof.
    intros Hff Hgg Hfg Hgf; repeat split.
    - apply generated_commute.
      intros a b Ha Hb.
      apply Gen_induced_sub in Ha, Hb; cbn in Ha, Hb.
      destruct Ha as [-> | ->], Hb as [-> | ->]; assumption.
  Qed.

  (** A family e₀, …, eₙ₋₁ is pairwise independent. *)
  Definition PairwiseIndependent (e : nat -> Eff Γ) (n : nat) : Prop :=
    forall a b, a < n -> b < n -> a <> b -> Independent (e a) (e b).
End TransformationMonoid.

(** ** Sequences of independent effects
    Indices are 0-based: e₀, …, eₙ₋₁ are applied in order from γ₀;
    [st i] is the state before eᵢ is applied (the notes' γᵢ is [st i] and
    γᵢ₋₁ is [st (i-1)]), [fwd i] the forward map of eᵢ, and [inv i] the
    inverse eᵢ yields where it is applied. *)
Section Sequence.
  Context {Γ : Type} (e : nat -> Eff Γ) (n : nat) (γ0 : Γ).
  Hypothesis Hind : PairwiseIndependent e n.

  Definition fwd (i : nat) : End Γ := fst ∘ e i.

  Fixpoint st (i : nat) : Γ :=
    match i with
    | 0 => γ0
    | S i' => fwd i' (st i')
    end.

  Definition inv (i : nat) : End Γ := snd (e i (st i)).

  Lemma fwd_in_M i : M (e i) (fwd i).
  Proof. apply fwd_M. Qed.

  Lemma inv_in_M i : M (e i) (inv i).
  Proof. apply inv_M. Qed.

  Lemma commute_at a b ha hb x :
    a < n -> b < n -> a <> b -> M (e a) ha -> M (e b) hb ->
    ha (hb x) = hb (ha x).
  Proof.
    intros Ha Hb Hab HMa HMb.
    destruct (Hind a b Ha Hb Hab) as [Hc _].
    exact (equal_f (Hc ha hb HMa HMb) x).
  Qed.

  Lemma inverse_stable a b h γ :
    a < n -> b < n -> a <> b -> M (e b) h ->
    snd (e a (h γ)) = snd (e a γ).
  Proof.
    intros Ha Hb Hab HM.
    destruct (Hind a b Ha Hb Hab) as [_ [H _]].
    apply H; exact HM.
  Qed.

  (** *** Theorem 43, claims (1) and (2) of the proof
      Fix j and write [st' k] for the state reached from [st j] by
      e_{j+1}, …, e_{j+k}, i.e. the sequence with eⱼ omitted. (In the
      notes' 1-based indexing, γ'ᵤ is [st' (u - j)].) *)
  Section Omit.
    Variable j : nat.
    Hypothesis Hj : j < n.
    Hypothesis Hwj : Witnessed (e j).

    Fixpoint st' (k : nat) : Γ :=
      match k with
      | 0 => st j
      | S k' => fwd (j + 1 + k') (st' k')
      end.

    (** 1. γᵤ = fⱼ(γ'ᵤ) and gⱼ(γᵤ) = γ'ᵤ. *)
    Theorem omit_state :
      forall k, j + 1 + k <= n ->
      st (j + 1 + k) = fwd j (st' k) /\ inv j (st (j + 1 + k)) = st' k.
    Proof.
      pose proof (proj1 (witnessed_iff _) Hwj) as Hw.
      induction k as [|k IH]; intros Hk.
      - replace (j + 1 + 0) with (S j) by lia.
        split; [reflexivity | exact (Hw (st j))].
      - destruct (IH ltac:(lia)) as [IH1 IH2].
        replace (j + 1 + S k) with (S (j + 1 + k)) by lia.
        change (st (S (j + 1 + k))) with (fwd (j + 1 + k) (st (j + 1 + k))).
        change (st' (S k)) with (fwd (j + 1 + k) (st' k)).
        split.
        + rewrite IH1.
          apply (commute_at (j + 1 + k) j);
            [lia | lia | lia | apply fwd_in_M | apply fwd_in_M].
        + rewrite <- IH2.
          apply (commute_at j (j + 1 + k));
            [lia | lia | lia | apply inv_in_M | apply fwd_in_M].
    Qed.

    (** 2. Each eᵢ with i > j yields at γ'ᵢ₋₁ the same inverse it yields
          at γᵢ₋₁. *)
    Theorem omit_inverse :
      forall k, j + 1 + k < n -> snd (e (j + 1 + k) (st' k)) = inv (j + 1 + k).
    Proof.
      intros k Hk.
      destruct (omit_state k ltac:(lia)) as [H1 _].
      unfold inv; rewrite H1; symmetry.
      apply (inverse_stable (j + 1 + k) j); [lia | lia | lia | apply fwd_in_M].
    Qed.
  End Omit.

  (** *** Theorem 43
      Applying the n inverses at [st n], in the order of any permutation of
      {0, …, n-1}, reaches γ₀.

      The proof generalises claims (1) and (2) from omitting one effect to omitting
      any set R of them: [stR R i] is the state reached by e₀, …, eᵢ₋₁ with
      those in R skipped. Running inv j at [stR R n] omits j as well. *)
  Hypothesis Hw : forall i, i < n -> Witnessed (e i).

  Fixpoint stR (R : nat -> bool) (i : nat) : Γ :=
    match i with
    | 0 => γ0
    | S i' => if R i' then stR R i' else fwd i' (stR R i')
    end.

  (** The forward maps of the skipped effects below i. *)
  Fixpoint skipped (R : nat -> bool) (i : nat) : End Γ :=
    match i with
    | 0 => id
    | S i' => if R i' then fwd i' ∘ skipped R i' else skipped R i'
    end.

  Lemma stR_ext R R' i :
    (forall k, k < i -> R k = R' k) -> stR R i = stR R' i.
  Proof.
    induction i as [|i IH]; intros H; cbn [stR]; [reflexivity|].
    rewrite (H i ltac:(lia)), IH by (intros; apply H; lia); reflexivity.
  Qed.

  Lemma stR_none i : stR (fun _ => false) i = st i.
  Proof. induction i as [|i IH]; cbn [stR st]; [|rewrite IH]; reflexivity. Qed.

  Lemma stR_all R i : (forall k, k < i -> R k = true) -> stR R i = γ0.
  Proof.
    induction i as [|i IH]; intros H; cbn [stR]; [reflexivity|].
    rewrite (H i ltac:(lia)); apply IH; intros; apply H; lia.
  Qed.

  Lemma skipped_commute R i h :
    (forall r x, r < i -> R r = true -> h (fwd r x) = fwd r (h x)) ->
    forall x, h (skipped R i x) = skipped R i (h x).
  Proof.
    induction i as [|i IH]; intros H x; cbn [skipped]; [reflexivity|].
    destruct (R i) eqn:Ri.
    - change (h (fwd i (skipped R i x)) = fwd i (skipped R i (h x))).
      rewrite H by (auto; lia).
      f_equal; apply IH; intros; apply H; auto; lia.
    - apply IH; intros; apply H; auto; lia.
  Qed.

  Lemma skipped_inverse R i m x :
    i < n -> m <= i -> snd (e i (skipped R m x)) = snd (e i x).
  Proof.
    intros Hi; induction m as [|m IH]; intros Hm; cbn [skipped]; [reflexivity|].
    destruct (R m).
    - change (snd (e i (fwd m (skipped R m x))) = snd (e i x)).
      rewrite (inverse_stable i m) by (lia || apply fwd_in_M).
      apply IH; lia.
    - apply IH; lia.
  Qed.

  (** γᵢ is reached from [stR R i] by the forward maps of the skipped ones. *)
  Lemma st_decomp R i : i <= n -> st i = skipped R i (stR R i).
  Proof.
    induction i as [|i IH]; intros Hi; cbn [st stR skipped]; [reflexivity|].
    rewrite IH by lia.
    destruct (R i); [reflexivity|].
    apply skipped_commute; intros r x Hr _.
    apply (commute_at i r); [lia | lia | lia | apply fwd_in_M | apply fwd_in_M].
  Qed.

  (** An effect that is not skipped yields at [stR R i] the inverse it yields
      at γᵢ. *)
  Lemma stR_inverse R i : i < n -> snd (e i (stR R i)) = inv i.
  Proof.
    intros Hi; unfold inv.
    rewrite (st_decomp R i ltac:(lia)).
    symmetry; apply skipped_inverse; lia.
  Qed.

  Definition upd (R : nat -> bool) (j : nat) : nat -> bool :=
    fun k => R k || Nat.eqb k j.

  (** Running inv j at [stR R n] additionally omits eⱼ. *)
  Lemma omit_one R j :
    j < n -> R j = false -> inv j (stR R n) = stR (upd R j) n.
  Proof.
    intros Hj HRj.
    assert (Hlow : stR R j = stR (upd R j) j).
    { apply stR_ext; intros k Hk; unfold upd.
      rewrite (proj2 (Nat.eqb_neq k j)) by lia; rewrite orb_false_r; reflexivity. }
    assert (Hk : forall k, j + 1 + k <= n ->
                 inv j (stR R (j + 1 + k)) = stR (upd R j) (j + 1 + k)).
    { induction k as [|k IH]; intros Hk.
      - replace (j + 1 + 0) with (S j) by lia.
        cbn [stR]; rewrite HRj.
        replace (upd R j j) with true
          by (unfold upd; rewrite Nat.eqb_refl, orb_true_r; reflexivity).
        rewrite <- Hlow, <- (stR_inverse R j Hj).
        exact (proj1 (witnessed_iff _) (Hw j Hj) (stR R j)).
      - replace (j + 1 + S k) with (S (j + 1 + k)) by lia.
        set (i := j + 1 + k) in *.
        cbn [stR].
        assert (Hupd : upd R j i = R i).
        { unfold upd; rewrite (proj2 (Nat.eqb_neq i j)) by lia.
          apply orb_false_r. }
        rewrite Hupd.
        destruct (R i).
        + apply IH; lia.
        + rewrite <- IH by lia.
          apply (commute_at j i);
            [lia | lia | lia | apply inv_in_M | apply fwd_in_M]. }
    replace n with (j + 1 + (n - j - 1)) by lia.
    apply Hk; lia.
  Qed.

  Lemma inverses_omit (l : list nat) :
    forall R, NoDup l -> (forall i, In i l -> i < n /\ R i = false) ->
    fold_left (fun s i => inv i s) l (stR R n)
    = stR (fun k => R k || existsb (Nat.eqb k) l) n.
  Proof.
    induction l as [|i l IH]; intros R Hnd Hl; cbn [fold_left].
    - apply stR_ext; intros; cbn; rewrite orb_false_r; reflexivity.
    - apply NoDup_cons_iff in Hnd as [Hni Hnd].
      destruct (Hl i (or_introl eq_refl)) as [Hi HRi].
      rewrite (omit_one R i Hi HRi).
      rewrite IH; [| exact Hnd |].
      + apply stR_ext; intros k _; unfold upd; cbn [existsb].
        symmetry; apply orb_assoc.
      + intros i' Hi'.
        destruct (Hl i' (or_intror Hi')) as [Hi'n HRi'].
        split; [exact Hi'n|].
        unfold upd; rewrite HRi'; cbn.
        apply Nat.eqb_neq; intros ->; contradiction.
  Qed.

  Theorem any_order_recovers (l : list nat) :
    Permutation l (seq 0 n) ->
    fold_left (fun s i => inv i s) l (st n) = γ0.
  Proof.
    intros Hp.
    assert (Hin : forall i, In i l <-> i < n).
    { intros i; split; intros H.
      - apply (Permutation_in _ Hp), in_seq in H; lia.
      - apply (Permutation_in _ (Permutation_sym Hp)), in_seq; lia. }
    rewrite <- stR_none.
    rewrite inverses_omit.
    - apply stR_all; intros k Hk; cbn.
      apply existsb_exists; exists k; split.
      + apply Hin; exact Hk.
      + apply Nat.eqb_refl.
    - apply (Permutation_NoDup (Permutation_sym Hp)), seq_NoDup.
    - intros i Hi; split; [apply Hin; exact Hi | reflexivity].
  Qed.
End Sequence.
