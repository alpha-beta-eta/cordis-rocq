(** * The summary theorem, extended

    Counterpart of [Summary.v] for the three extensions: for each, the
    obligations a component table (or an orchestrator) has to meet, bundled,
    and the guarantee tiers they buy. The service specification is the
    core's: the revertible tier [Revertible G] and the confluent tier
    [ConfHyps Σ G], with [G] covering the pairs of operations the programs
    allow ([Covers]).

    | tier | optional dependencies | orchestrators | intersection lifetimes |
    |---|---|---|---|
    | 0 safety | no hypothesis | no hypothesis | no hypothesis; containment |
    | 1 liveness | [XObligations] | [Obligations] | [IObligations] |
    | 2 recovery | revertible tier | revertible tier | revertible tier |
    | 3 confluence | confluent tier, [XObligations], [XTotal], [NoOptChild] | confluent tier, [Obligations], [TotalProv], same outcome up to order | not covered |

    Every statement is a corollary of a theorem proved in the extension's
    own files; this file only bundles the hypotheses and checks that they
    fit together. Nothing here is imported by the core. *)

From Stdlib Require Import List PeanoNat Lia.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering Recovery
  Progress Termination Confluence StateInv Episode StateConf SpawnConf Dynamic Compose Summary.
From Cordis Require Import Ext.Optional Ext.OptProgress Ext.OptRecovery Ext.OptTermination
  Ext.OptState Ext.OptSpawn Ext.OptDynamic Ext.Orchestrator Ext.Intersect Ext.IntersectLive.
Import ListNotations.

(** ** 1. Optional dependencies *)
Section OptSummary.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (C_eq_dec : forall x y : C, {x = y} + {x <> y}).
  Context (xprog : C -> @XComponent K Σ C).

  Local Notation CC := (@Optional.C' K C).
  Local Notation State := (@State K Σ CC).
  Local Notation prog' := (prog' K_eq_dec Σ xprog).

  (** Every variant is bounded; a bounded rank rises along provision,
      spawn, handlers, and optional dependencies. *)
  Definition XObligations (Kb : nat) (xrank : C -> nat) (Rb : nat) : Prop :=
    (forall c T, Bounded Σ Kb (xbody Σ (xprog c) T)) /\
    (forall c c', XAbove Σ xprog c c' -> xrank c < xrank c') /\
    (forall c, xrank c <= Rb).

  (** Every variant provides every key the component may provide. *)
  Definition XTotal : Prop :=
    forall c T k, In k (xprovs Σ (xprog c)) -> AllDoneProv Σ k (xbody Σ (xprog c) T).

  (** Components that may be spawned or run as handlers declare no
      optional dependency (asked by confluence only). *)
  Definition NoOptChild : Prop :=
    forall c c', XSpawns Σ xprog c c' -> xopt Σ (xprog c') = [].

  Theorem xsum_wf (γ : State) : XReachable K_eq_dec Σ xprog γ -> WF K_eq_dec Σ prog' γ.
  Proof. exact (xwf_reachable K_eq_dec Σ xprog γ). Qed.

  Theorem xsum_live Kb xrank Rb (γ : State) :
    XObligations Kb xrank Rb -> XReachable K_eq_dec Σ xprog γ ->
    Acc (XLStepRel K_eq_dec Σ xprog Kb) γ /\
    (xquiet K_eq_dec Σ xprog γ ->
     settled Σ prog' γ /\
     forall n f acc w, fibers Σ γ n = Some f -> life Σ f = Active Σ acc w ->
                       fresh K_eq_dec Σ xprog γ f = true).
  Proof.
    intros (HK & Hrank & Hbnd) R; split.
    - exact (xtermination_reachable K_eq_dec Σ C_eq_dec xprog Kb HK xrank Rb Hrank Hbnd γ R).
    - exact (xquiet_settled_reachable K_eq_dec Σ C_eq_dec xprog xrank Rb Hrank Hbnd γ R).
  Qed.

  Theorem xsum_recovery G n ls (γ : State) σ :
    Revertible Σ G -> Covers Σ prog' G ->
    xshadow_run K_eq_dec Σ xprog n (@init K Σ CC) ls (fun _ => None) = Some (γ, σ) ->
    match fibers Σ γ n with Some f => is_installed Σ (life Σ f) = false | None => True end ->
    forall k, match binds Σ γ k, σ k with
              | Some b, Some s => bst Σ b ≃ s
              | None, None => True
              | _, _ => False
              end.
  Proof.
    intros [Hwb Hri] HG.
    exact (xrecovery_from_init K_eq_dec Σ xprog Hwb
             (fun k a b ta tb Cab Ht => Hri a b ta tb (HG k a b Cab) Ht) n ls γ σ).
  Qed.

  Theorem xsum_confluence G Kb xrank Rb ins1 ins2 (γ1 γ2 : State) rs1 rs2 :
    ConfHyps Σ G -> Covers Σ prog' G -> XObligations Kb xrank Rb -> XTotal -> NoOptChild ->
    XDRun K_eq_dec Σ xprog (@init K Σ CC) [] ins1 γ1 rs1 ->
    XDRun K_eq_dec Σ xprog (@init K Σ CC) [] ins2 γ2 rs2 ->
    xscomps ins1 = xscomps ins2 ->
    xquiet K_eq_dec Σ xprog γ1 -> xquiet K_eq_dec Σ xprog γ2 -> NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    AgreeL Σ (slab rs1 ins1) (slab rs2 ins2) (norm Σ xprog γ1) (norm Σ xprog γ2).
  Proof.
    intros H HG (HK & Hrank & Hbnd) Total NOC.
    exact (xdynamic_agree K_eq_dec Σ C_eq_dec xprog Kb HK xrank Rb Hrank Hbnd Total NOC
             (ch_wb _ _ H) (ch_ui _ _ H) (ch_ti _ _ H)
             (fun k a b ta tb g Cab Ht Hy x Hx =>
                ch_ri _ _ H a b ta tb g (HG k a b Cab) Ht Hy x
                  (after_mono _ _ (fun b' => HG k a b') a ta x Hx))
             (fun k a b ta tb Cab Ht => ch_com _ _ H a b ta tb (HG k a b Cab) Ht)
             ins1 ins2 γ1 γ2 rs1 rs2).
  Qed.
End OptSummary.

(** ** 2. Orchestrators *)
Section OrchSummary.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).
  Local Notation DRun := (DRun K_eq_dec Σ prog).

  (** Tiers 0–2 are [Orchestrator.orch_wf], [orch_live], [orch_recovery];
      they ask the orchestrator for nothing beyond issuing [Input]s (O1, O2).
      Tier 3 asks, of two orchestrations, the same surviving components in
      any order (O3). *)
  Theorem osum_confluence G Kb rank Rb ins1 ins2 (γ1 γ2 : State) rs1 rs2 :
    ConfHyps Σ G -> Covers Σ prog G -> Obligations Σ prog Kb rank Rb -> TotalProv Σ prog ->
    DRun (@init K Σ C) [] ins1 γ1 rs1 -> DRun (@init K Σ C) [] ins2 γ2 rs2 ->
    SameOutcome ins1 ins2 ->
    quiet K_eq_dec Σ prog γ1 -> quiet K_eq_dec Σ prog γ2 -> NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    exists π, AgreeL Σ (slab rs1 ins1) (fun n => π (slab rs2 ins2 n)) γ1 γ2.
  Proof.
    intros H HG (HK & Hrank & Hbnd) Total.
    exact (dynamic_agree_perm K_eq_dec Σ prog Kb HK rank Rb Hrank Hbnd Total
             (ch_wb _ _ H) (ch_ui _ _ H) (ch_ti _ _ H)
             (fun k a b ta tb g Cab Ht Hy x Hx =>
                ch_ri _ _ H a b ta tb g (HG k a b Cab) Ht Hy x
                  (after_mono _ _ (fun b' => HG k a b') a ta x Hx))
             (fun k a b ta tb Cab Ht => ch_com _ _ H a b ta tb (HG k a b Cab) Ht)
             ins1 ins2 γ1 γ2 rs1 rs2).
  Qed.
End OrchSummary.

(** ** 3. Intersection lifetimes *)
Section ISummary.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (C_eq_dec : forall x y : C, {x = y} + {x <> y}).
  Context {E : Type} (iprog : C -> @IComponent K Σ C E).

  Local Notation State := (@State K Σ C).
  Local Notation progN := (progE Σ iprog None).
  Local Notation istep := (istep K_eq_dec Σ iprog).

  (** Programs are bounded; a bounded rank rises along provision, spawn,
      and every handler instance. *)
  Definition IObligations (Kb : nat) (rank : C -> nat) (Rb : nat) : Prop :=
    (forall c, Bounded Σ Kb (ibody Σ (iprog c))) /\
    (forall c c', IAbove Σ iprog c c' -> rank c < rank c') /\
    (forall c, rank c <= Rb).

  (** Safety, and containment: an installed fiber lives within its parent
      and every provider it resolves, and while it resolves a provision of
      an Unloading fiber, that fiber undoes nothing. *)
  Theorem isum_wf (γ : State) :
    IReachable K_eq_dec Σ iprog γ ->
    WF K_eq_dec Σ progN γ /\
    (forall x fx, fibers Σ γ x = Some fx -> is_installed Σ (life Σ fx) = true ->
       (forall q, Calculus.parent Σ fx = Some q ->
          exists fq, fibers Σ γ q = Some fq /\ is_installed Σ (life Σ fq) = true) /\
       (forall k p, In (k, p) (view_of Σ (life Σ fx)) ->
          exists b fo, binds Σ γ k = Some b /\ pid Σ b = p /\ owner Σ b <> x /\
                       fibers Σ γ (owner Σ b) = Some fo /\ is_installed Σ (life Σ fo) = true)) /\
    (forall n f acc w z k p m fm k',
       fibers Σ γ n = Some f -> life Σ f = Unloading Σ acc w z ->
       In (UProv Σ k p) acc -> m <> n -> fibers Σ γ m = Some fm ->
       In (k', p) (view_of Σ (life Σ fm)) ->
       istep γ (ICore (LUndo n)) = None /\ istep γ (ICore (LRetireChild n)) = None).
  Proof.
    intros R; pose proof (iwf_reachable K_eq_dec Σ iprog γ R) as W.
    split; [exact W|]; split.
    - intros x fx Hx Hi; exact (effect_within K_eq_dec Σ iprog γ x fx W Hx).
    - intros n f acc w z k p m fm k' Hn Hl Hu Hmn Hm Hv.
      exact (unload_blocked_i K_eq_dec Σ iprog γ n f acc w z k p m fm k' W Hn Hl Hu Hmn Hm Hv).
  Qed.

  Theorem isum_live Kb rank Rb (γ : State) :
    IObligations Kb rank Rb -> IReachable K_eq_dec Σ iprog γ ->
    Acc (ILStepRel K_eq_dec Σ iprog Kb) γ /\ (quiet K_eq_dec Σ progN γ -> settled Σ progN γ).
  Proof.
    intros (HK & Hrank & Hbnd) R; split.
    - exact (itermination_reachable K_eq_dec Σ C_eq_dec iprog Kb HK rank Rb Hrank Hbnd γ R).
    - exact (iquiet_settled K_eq_dec Σ C_eq_dec iprog Kb rank Rb Hrank Hbnd γ
               (iinv_reachable K_eq_dec Σ C_eq_dec iprog Kb HK γ R)).
  Qed.

  (** An effect, from before its fiber exists to after it is gone, leaves
      every binding as if it had never run. *)
  Theorem isum_recovery G n ls (γ : State) σ :
    Revertible Σ G -> Covers Σ progN G ->
    ishadow_run K_eq_dec Σ iprog n (@init K Σ C) ls (fun _ => None) = Some (γ, σ) ->
    match fibers Σ γ n with Some f => is_installed Σ (life Σ f) = false | None => True end ->
    forall k, match binds Σ γ k, σ k with
              | Some b, Some s => bst Σ b ≃ s
              | None, None => True
              | _, _ => False
              end.
  Proof.
    intros [Hwb Hri] HG Hrun Hn.
    exact (ieffect_exact K_eq_dec Σ iprog Hwb
             (fun k a b ta tb Cab Ht => Hri a b ta tb (HG k a b Cab) Ht) n (@init K Σ C) ls γ σ
             (wf_init K_eq_dec Σ progN) (prov_init Σ progN) eq_refl Hrun Hn).
  Qed.
End ISummary.
