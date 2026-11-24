(** * Extension 2: orchestrator obligations (docs/EXTENSIONS.md, section 2)

    Plugin markets, self-updaters and bundles install, remove and restart
    other plugins. What they install outlives them (it is written to
    configuration), so an orchestrator is not a parent fiber: it is a
    source of orchestration inputs ([Dynamic.Input]), which name roots by
    insertion index and are fed to the core execution [DRun].

    Obligations, and where each is used:
    - O1, orchestrate roots only: built into [Input], which can only name
      inserted roots. Disposing a child spawned at startup is not an input.
    - O2, finitely many inputs: an input list is finite. Liveness is stated
      for the state after the last input.
    - O3, a schedule-independent outcome: two orchestrations whose
      surviving components are the same multiset ([SameOutcome]).
    - O4, no self-restart inside one's own startup program, and O5, no
      uncontrolled orchestration (loader entries, [internal/*] hooks):
      outside the model; a plugin that violates them is not an input source
      but changes the runtime.

    Results, all derived from core theorems without changing the core:
    - every orchestrated execution is an execution of the calculus
      ([drun_labels]), so the summary theorem's tiers 0–2 apply to it
      ([orch_wf], [orch_live], [orch_recovery]);
    - tier 3 up to a permutation of the survivors ([dynamic_agree_perm]):
      two orchestrations that leave the same surviving components, in any
      order, reach final states that agree up to renaming. The core's
      [dynamic_agree] asks for the same order; here the second run's roots
      are relabelled by the permutation, and [SpawnConf.final_agree] does
      the rest. A plugin market that installs a set of plugins in
      whatever order downloads finish meets O3. *)

From Stdlib Require Import List PeanoNat Bool Lia Permutation FinFun.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering
  Recovery Progress Termination Confluence StateInv Episode StateConf SpawnConf Dynamic Compose Summary.
Import ListNotations.

Section Orchestrator.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).
  Local Notation Input := (@Input C).
  Local Notation S := (St Σ).
  Local Notation fibers := (fibers Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation fparent := (Calculus.parent Σ).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation DRun := (DRun K_eq_dec Σ prog).
  Local Notation cbody c := (body Σ (prog c)).
  Local Notation cprovs c := (provs Σ (prog c)).

  (** ** Orchestrated executions are executions of the calculus *)
  Lemma drun_labels (γ : State) rs ins γ' rs' :
    DRun γ rs ins γ' rs' -> exists ls, run_labels K_eq_dec Σ prog γ ls = Some γ'.
  Proof.
    intros R; induction R as [γ rs|γ rs ins ℓ γ1 γ2 rs2 _ Hs _ (ls & IH)|γ rs x ins ℓ γ1 γ2 rs2 _ Hs _ (ls & IH)].
    - exists []; reflexivity.
    - exists (ℓ :: ls); cbn; rewrite Hs; exact IH.
    - exists (ℓ :: ls); cbn; rewrite Hs; exact IH.
  Qed.

  Lemma drun_reachable ins (γ : State) rs :
    DRun (@init K Σ C) [] ins γ rs -> Reachable K_eq_dec Σ prog γ.
  Proof. intros R; exact (drun_labels _ _ _ _ _ R). Qed.

  (** ** Tier 0: safety, no hypothesis *)
  Theorem orch_wf ins (γ : State) rs :
    DRun (@init K Σ C) [] ins γ rs -> WF K_eq_dec Σ prog γ.
  Proof. intros R; exact (summary_wf K_eq_dec Σ prog γ (drun_reachable ins γ rs R)). Qed.

  (** ** Tier 1: after the last input, lifecycle steps terminate, and a
      state where none applies is settled *)
  Theorem orch_live Kb rank Rb ins (γ : State) rs :
    Obligations Σ prog Kb rank Rb -> DRun (@init K Σ C) [] ins γ rs ->
    Acc (LStepRel K_eq_dec Σ prog Kb) γ /\ (quiet K_eq_dec Σ prog γ -> settled Σ prog γ).
  Proof. intros O R; exact (summary_live K_eq_dec Σ prog Kb rank Rb γ O (drun_reachable ins γ rs R)). Qed.

  (** ** Tier 2: a fiber that is not installed has left no trace *)
  Theorem orch_recovery G n ins (γ : State) rs :
    Revertible Σ G -> Covers Σ prog G -> DRun (@init K Σ C) [] ins γ rs ->
    match fibers γ n with Some f => is_installed Σ (life Σ f) = false | None => True end ->
    exists ls σ,
      shadow_run K_eq_dec Σ prog n (@init K Σ C) ls (fun _ => None) = Some (γ, σ) /\
      forall k, match binds Σ γ k, σ k with
                | Some b, Some s => bst Σ b ≃ s
                | None, None => True
                | _, _ => False
                end.
  Proof.
    intros Rv Cv R Hn.
    destruct (drun_labels _ _ _ _ _ R) as (ls & Hls).
    destruct (shadow_run_total K_eq_dec Σ prog n _ ls (fun _ => None) γ Hls) as (σ & Hs).
    exists ls, σ; split; [exact Hs|].
    exact (summary_recovery K_eq_dec Σ prog G n ls γ σ Rv Cv Hs Hn).
  Qed.

  (** ** Tier 3: confluence up to a permutation of the survivors *)

  (** O3: the two orchestrations leave the same surviving components. *)
  Definition SameOutcome (ins1 ins2 : list Input) : Prop := Permutation (scomps ins1) (scomps ins2).

  Variable Kb : nat.
  Hypothesis HK : forall c, Bounded Σ Kb (cbody c).
  Variable rank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', Above Σ prog c c' -> rank c < rank c'.
  Hypothesis Hbnd : forall c, rank c <= Rb.
  Hypothesis Total : forall c k, In k (cprovs c) -> AllDoneProv Σ k (cbody c).
  Hypothesis Hwb : forall a t, WellBehaved (Σ := Σ) a t.
  Hypothesis HUI : forall (a : Op Σ) (t : nat) (s1 s2 s1' s2' : S) (g1 g2 : S -> S) (o1 o2 : Out Σ),
    run a t s1 = Some (s1', g1, o1) -> run a t s2 = Some (s2', g2, o2) -> fun_eq (Σ := Σ) g1 g2.
  Hypothesis HTI : forall (a : Op Σ) (t t' : nat) (s : S),
    match run a t s, run a t' s with
    | None, None => True
    | Some (s1, _, o1), Some (s2, _, o2) => @st_eq Σ s1 s2 /\ o1 = o2
    | _, _ => False
    end.
  Hypothesis HRI : forall (k : K) (a b : Op Σ) (ta tb : nat) (g : S -> S), CoPair Σ prog k a b -> ta <> tb ->
    yields (Σ := Σ) a ta g ->
    forall x, After (CoPair Σ prog k a) a ta x -> shifted_ok (Σ := Σ) g (run b tb x) (run b tb (g x)).
  Hypothesis HCom : forall (k : K) (a b : Op Σ) (ta tb : nat), CoPair Σ prog k a b -> ta <> tb ->
    Commute (Σ := Σ) a ta b tb.

  Local Notation Ledger := (Ledger Σ).

  (** At a final state, every survivor index holds a root of its component. *)
  Lemma root_at (γ : State) rs ins p c :
    Ledger γ rs ins -> nth_error (scomps ins) p = Some c ->
    exists n f, fibers γ n = Some f /\ fparent f = None /\ slab rs ins n = p /\ fcomp f = c.
  Proof.
    intros L Cs; unfold scomps in Cs.
    destruct (keepi_surj _ _ _ _ _ Cs) as (i & Lv & Ci & Ei); cbn in Lv.
    assert (Hi : i < length rs) by (rewrite (lg_len _ _ _ _ L); apply nth_error_Some; congruence).
    destruct (nth_error rs i) as [n|] eqn:E; [|apply nth_error_None in E; lia].
    destruct (lg_at _ _ _ _ L i n E) as [[_ D]|(f & Hf & Pf & Cf & _)].
    { apply live_ix_spec in Lv; contradiction. }
    exists n, f; split; [exact Hf|]; split; [exact Pf|]; split.
    - pose proof (keepi_nth (live_ix ins) rs 0 i n E Lv) as En.
      change (slab rs ins n) with (pos (keepi (live_ix ins) rs 0) n).
      rewrite (pos_nth _ _ n (keepi_nodup _ _ _ (lg_nodup _ _ _ _ L)) En); exact Ci.
    - congruence.
  Qed.

  Theorem dynamic_agree_perm ins1 ins2 (γ1 γ2 : State) rs1 rs2 :
    DRun (@init K Σ C) [] ins1 γ1 rs1 -> DRun (@init K Σ C) [] ins2 γ2 rs2 ->
    SameOutcome ins1 ins2 ->
    quiet K_eq_dec Σ prog γ1 -> quiet K_eq_dec Σ prog γ2 -> NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    exists π : nat -> nat, AgreeL Σ (slab rs1 ins1) (fun n => π (slab rs2 ins2 n)) γ1 γ2.
  Proof.
    intros R1 R2 SO Q1 Q2 NF1 NF2.
    apply Permutation_nth_error_bis in SO as (π & Inj & Bf & Hπ).
    exists π.
    assert (SL0 : SLInv Σ (@init K Σ C)) by (split; intros; discriminate).
    pose proof (pinv_init K_eq_dec Σ prog Kb) as P0.
    destruct (drun_inv K_eq_dec Σ prog Kb HK rank Hrank Total Hwb HUI HTI HRI HCom _ _ _ _ _ []
                R1 (ledger_init Σ) P0 SL0) as (L1 & P1 & S1).
    destruct (drun_inv K_eq_dec Σ prog Kb HK rank Hrank Total Hwb HUI HTI HRI HCom _ _ _ _ _ []
                R2 (ledger_init Σ) P0 SL0) as (L2 & P2 & S2).
    cbn [app] in L1, L2.
    pose proof (quiet_final K_eq_dec Σ prog Kb rank Rb Hrank Hbnd γ1 P1 S1 Q1 NF1) as F1.
    pose proof (quiet_final K_eq_dec Σ prog Kb rank Rb Hrank Hbnd γ2 P2 S2 Q2 NF2) as F2.
    pose proof (proj1 (proj2 (proj1 F1))) as St1; pose proof (proj1 (proj2 (proj1 F2))) as St2.
    assert (Sur : bSurjective (length (scomps ins1)) π)
      by (apply (bInjective_bSurjective Bf); intros x y _ _ E; exact (Inj x y E)).
    apply (final_agree K_eq_dec Σ prog Kb rank Rb Hrank Hbnd Hwb HTI HCom); try assumption.
    - exact (ledger_rootinj Σ prog γ1 rs1 ins1 L1 St1 NF1).
    - intros n n' f f' Hn Pn Hn' Pn' E.
      exact (ledger_rootinj Σ prog γ2 rs2 ins2 L2 St2 NF2 n n' f f' Hn Pn Hn' Pn' (Inj _ _ E)).
    - (* a root of γ1 at survivor index p: the root of γ2 at the index π sends to p *)
      intros n1 f1 Hn1 Pn1.
      destruct (final_slab Σ prog γ1 rs1 ins1 n1 f1 L1 St1 NF1 Hn1 Pn1) as (_ & _ & Cs1).
      assert (Hp : slab rs1 ins1 n1 < length (scomps ins1)) by (apply nth_error_Some; congruence).
      destruct (Sur _ Hp) as (q & Hq & Eq).
      assert (Cs2 : nth_error (scomps ins2) q = Some (fcomp f1)) by (rewrite Hπ, Eq; exact Cs1).
      destruct (root_at γ2 rs2 ins2 q _ L2 Cs2) as (n2 & f2 & Hf2 & Pf2 & Sl2 & Cf2).
      exists n2, f2; split; [exact Hf2|]; split; [exact Pf2|]; split; [rewrite Sl2; exact Eq | exact Cf2].
    - (* a root of γ2 at survivor index q: the root of γ1 at π q *)
      intros n2 f2 Hn2 Pn2.
      destruct (final_slab Σ prog γ2 rs2 ins2 n2 f2 L2 St2 NF2 Hn2 Pn2) as (_ & _ & Cs2).
      rewrite Hπ in Cs2.
      destruct (root_at γ1 rs1 ins1 _ _ L1 Cs2) as (n1 & f1 & Hf1 & Pf1 & Sl1 & Cf1).
      exists n1, f1; split; [exact Hf1|]; split; [exact Pf1|]; split; [exact Sl1 | exact Cf1].
  Qed.

  (** A market installs the same plugins in whatever order downloads finish:
      the final states agree with those of any other order. *)
  Corollary install_order cs1 cs2 (γ1 γ2 : State) rs1 rs2 :
    Permutation cs1 cs2 ->
    DRun (@init K Σ C) [] (map IIns cs1) γ1 rs1 -> DRun (@init K Σ C) [] (map IIns cs2) γ2 rs2 ->
    quiet K_eq_dec Σ prog γ1 -> quiet K_eq_dec Σ prog γ2 -> NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    exists π, AgreeL Σ (slab rs1 (map IIns cs1)) (fun n => π (slab rs2 (map IIns cs2) n)) γ1 γ2.
  Proof.
    intros Pm R1 R2; apply (dynamic_agree_perm _ _ γ1 γ2 rs1 rs2 R1 R2).
    unfold SameOutcome; rewrite !scomps_static; exact Pm.
  Qed.

  (** Self-update: disposing the old version and inserting the new one,
      at any point and interleaved with anything, ends where a plain
      installation of the survivors ends. *)
  Corollary self_update ins (γ γs : State) rs rss :
    DRun (@init K Σ C) [] ins γ rs -> DRun (@init K Σ C) [] (map IIns (scomps ins)) γs rss ->
    quiet K_eq_dec Σ prog γ -> quiet K_eq_dec Σ prog γs -> NoFailed Σ γ -> NoFailed Σ γs ->
    AgreeL Σ (slab rs ins) (slab rss (map IIns (scomps ins))) γ γs.
  Proof.
    exact (static_assembly K_eq_dec Σ prog Kb HK rank Rb Hrank Hbnd Total Hwb HUI HTI HRI HCom ins γ γs rs rss).
  Qed.
End Orchestrator.
