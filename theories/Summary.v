(** * The summary theorem

    The shape announced in the principles: if the service meets its
    specification and the component table meets its obligations, the
    system has the lifecycle properties. The specification comes in two
    tiers, since recovery and confluence ask different things of the
    service; the obligations likewise come in two parts.

    - Service, revertible tier ([Revertible G]): every operation is well
      behaved, and operations related by [G] are revert-independent under
      distinct tokens.
    - Service, confluent tier ([ConfHyps Σ G], from [Compose.v]).
    - [G] covers the pairs the programs allow ([Covers G]).
    - Component obligations ([Obligations]): programs are bounded, and a
      bounded rank increases along [Above]. [Total] (every path to [Done]
      provides every key the component may provide) is asked for
      confluence only.

    Then, for every state reachable from the initial state:
    1. it is well formed (no hypothesis);
    2. lifecycle steps from it terminate, and where none applies the state
       is settled (obligations);
    3. a fiber that is not installed has left the store as the shadow
       execution without its operations would (revertible tier);
    4. two orchestrated executions with the same inputs that end quiet
       with no failed fiber agree up to renaming, and agree with static
       assembly (confluent tier, obligations, [Total]).

    Every part is a corollary of a theorem proved elsewhere; this file
    only bundles the hypotheses and checks that they fit together. *)

From Stdlib Require Import List PeanoNat Lia Wf_nat.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering
  Recovery Progress Termination Confluence SpawnConf Dynamic Compose.
Import ListNotations.

Section Summary.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation cbody c := (body Σ (prog c)).
  Local Notation cprovs c := (provs Σ (prog c)).

  Definition Reachable (γ : State) : Prop :=
    exists ls, run_labels K_eq_dec Σ prog (@init K Σ C) ls = Some γ.

  (** ** The specification and the obligations *)
  Definition Revertible (G : Op Σ -> Op Σ -> Prop) : Prop :=
    (forall a t, WellBehaved (Σ := Σ) a t) /\
    (forall a b ta tb, G a b -> ta <> tb -> RevertIndep (Σ := Σ) a ta b tb).

  Definition Covers (G : Op Σ -> Op Σ -> Prop) : Prop :=
    forall k a b, CoPair Σ prog k a b -> G a b.

  Definition Obligations (Kb : nat) (rank : C -> nat) (Rb : nat) : Prop :=
    (forall c, Bounded Σ Kb (cbody c)) /\
    (forall c c', Above Σ prog c c' -> rank c < rank c') /\
    (forall c, rank c <= Rb).

  Definition TotalProv : Prop :=
    forall c k, In k (cprovs c) -> AllDoneProv Σ k (cbody c).

  (** ** 1. Safety: no hypothesis *)
  Theorem summary_wf (γ : State) : Reachable γ -> WF K_eq_dec Σ prog γ.
  Proof. intros [ls H]; exact (wf_reachable K_eq_dec Σ prog γ ls H). Qed.

  (** ** 2. Liveness: the obligations *)
  Theorem summary_live Kb rank Rb (γ : State) :
    Obligations Kb rank Rb -> Reachable γ ->
    Acc (LStepRel K_eq_dec Σ prog Kb) γ /\
    (quiet K_eq_dec Σ prog γ -> settled Σ prog γ).
  Proof.
    intros (HK & Hrank & Hbnd) [ls H]; split.
    - exact (termination_reachable K_eq_dec Σ prog Kb HK rank Rb Hrank Hbnd ls γ H).
    - assert (Hwf : well_founded (fun c' c => Above Σ prog c c')).
      { apply (well_founded_lt_compat C (fun c => Rb - rank c)).
        intros c' c HA; pose proof (Hrank c c' HA); pose proof (Hbnd c'); lia. }
      intros Q.
      destruct (progress_reachable K_eq_dec Σ prog Hwf ls γ H) as [S | (n & ℓ & γ' & Hin & Hs)];
        [exact S|].
      rewrite (Q n ℓ Hin) in Hs; discriminate.
  Qed.

  (** ** 3. Recovery: the revertible tier *)
  Theorem summary_recovery G n ls (γ : State) σ :
    Revertible G -> Covers G ->
    shadow_run K_eq_dec Σ prog n (@init K Σ C) ls (fun _ => None) = Some (γ, σ) ->
    match fibers Σ γ n with Some f => is_installed Σ (life Σ f) = false | None => True end ->
    forall k, match binds Σ γ k, σ k with
              | Some b, Some s => bst Σ b ≃ s
              | None, None => True
              | _, _ => False
              end.
  Proof.
    intros [Hwb Hri] HG.
    exact (recovery_from_init K_eq_dec Σ prog Hwb
             (fun k a b ta tb Cab Ht => Hri a b ta tb (HG k a b Cab) Ht) n ls γ σ).
  Qed.

  (** ** 4. Confluence: the confluent tier, the obligations and [TotalProv] *)
  Theorem summary_confluence G Kb rank Rb ins (γ1 γ2 : State) rs1 rs2 :
    ConfHyps Σ G -> Covers G -> Obligations Kb rank Rb -> TotalProv ->
    DRun K_eq_dec Σ prog (@init K Σ C) [] ins γ1 rs1 ->
    DRun K_eq_dec Σ prog (@init K Σ C) [] ins γ2 rs2 ->
    quiet K_eq_dec Σ prog γ1 -> quiet K_eq_dec Σ prog γ2 -> NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    AgreeL Σ (slab rs1 ins) (slab rs2 ins) γ1 γ2.
  Proof.
    intros H HG (HK & Hrank & Hbnd) Total.
    exact (dynamic_confluence K_eq_dec Σ prog Kb HK rank Rb Hrank Hbnd Total
             (ch_wb _ _ H) (ch_ui _ _ H) (ch_ti _ _ H)
             (fun k a b ta tb g Cab Ht Hy x Hx =>
                ch_ri _ _ H a b ta tb g (HG k a b Cab) Ht Hy x
                  (after_mono _ _ (fun b' => HG k a b') a ta x Hx))
             (fun k a b ta tb Cab Ht => ch_com _ _ H a b ta tb (HG k a b Cab) Ht)
             ins γ1 γ2 rs1 rs2).
  Qed.

  Theorem summary_static G Kb rank Rb ins (γ γs : State) rs rss :
    ConfHyps Σ G -> Covers G -> Obligations Kb rank Rb -> TotalProv ->
    DRun K_eq_dec Σ prog (@init K Σ C) [] ins γ rs ->
    DRun K_eq_dec Σ prog (@init K Σ C) [] (map IIns (scomps ins)) γs rss ->
    quiet K_eq_dec Σ prog γ -> quiet K_eq_dec Σ prog γs -> NoFailed Σ γ -> NoFailed Σ γs ->
    AgreeL Σ (slab rs ins)
             (slab rss (map IIns (scomps ins))) γ γs.
  Proof.
    intros H HG (HK & Hrank & Hbnd) Total.
    exact (static_assembly K_eq_dec Σ prog Kb HK rank Rb Hrank Hbnd Total
             (ch_wb _ _ H) (ch_ui _ _ H) (ch_ti _ _ H)
             (fun k a b ta tb g Cab Ht Hy x Hx =>
                ch_ri _ _ H a b ta tb g (HG k a b Cab) Ht Hy x
                  (after_mono _ _ (fun b' => HG k a b') a ta x Hx))
             (fun k a b ta tb Cab Ht => ch_com _ _ H a b ta tb (HG k a b Cab) Ht)
             ins γ γs rs rss).
  Qed.
End Summary.
