(** * Extension 3: effects with intersection lifetime (docs/EXTENSIONS.md, section 3)

    A plugin P attaches an effect to an agent A's context (restrict A's
    tools, add a plugin to A): the effect must go when either P or A ends.
    The core can express this. The effect is a reaction child of P
    ([O-React]); it declares a dependency on A's entry key (an entry is a
    key, design item r). If P unloads, it waits for its reaction children
    to go first; if A leaves Active, the child's target becomes ⊥ and it
    unloads, and while the child still resolves A's entry, A undoes nothing
    at all (the core's unload guard, as in Cordis): the effect is gone
    before any of A's context is torn down.

    What the core lacks: the agent is runtime data, while [reacts] is a
    static list. Here a handler is a family [E -> C] indexed by the event
    payload [e] (an agent id, say), and [I-React n i e] runs the [i]-th
    handler's instance at [e]. It is the core [O-React n i] under the table
    whose handlers are instantiated at [e] ([progE (Some e)]); every other
    label is a core step ([progN], no handlers). The tables differ only in
    their handler lists, which no rule but [O-React] reads.

    Results:
    - safety: [WF] along every execution ([iwf_reachable]);
    - containment ([effect_within]): an installed fiber sits inside the
      lifetime of its parent and of the owner of every provision it
      resolves; while a child still resolves one of its provisions, an
      owner neither undoes anything nor retires any child
      ([unload_blocked_i], [withdraw_blocked_i]);
    - recovery ([irecovery_exact], [ieffect_exact]): an effect, from before
      it exists to after it is gone, leaves every binding as if it had never
      run, with independence asked of every pair of operations two
      components (any instances) may perform at one key;
    - liveness ([itermination], [iquiet_settled]): lifecycle steps
      terminate and quiet states are settled, when a rank rises along
      provision, spawn and every handler instance.
    Confluence is not covered, as in the core (it excludes [O-React]). *)

From Stdlib Require Import List PeanoNat Bool Lia Wf_nat.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Recovery Progress Termination.
Import ListNotations.

Section Intersect.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (C_eq_dec : forall x y : C, {x = y} + {x <> y}).
  Context {E : Type}.

  (** ** Components with handler families *)
  Record IComponent : Type := mkI {
    ideps : list K;
    iprovs : list K;
    ibody : @Prog K Σ C;
    ireacts : list (E -> C)
  }.

  Context (iprog : C -> IComponent).

  Local Notation State := (@State K Σ C).
  Local Notation Fiber := (@Fiber K Σ C).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation fparent := (Calculus.parent Σ).
  Local Notation acc_of := (acc_of Σ).
  Local Notation view_of := (view_of Σ).
  Local Notation is_installed := (is_installed Σ).
  Local Notation owner := (owner Σ).
  Local Notation bst := (bst Σ).

  (** The core table with handlers instantiated at [e], or with none. *)
  Definition progE (x : option E) (c : C) : @Component K Σ C :=
    let ic := iprog c in
    mkComponent (ideps ic) (iprovs ic) (ibody ic)
                (match x with Some e => map (fun h => h e) (ireacts ic) | None => [] end).

  Local Notation progN := (progE None).
  Local Notation WF := (WF K_eq_dec Σ progN).

  Inductive ILabel : Type :=
  | ICore (ℓ : @Label C)          (* a core label; [O-React] under it has no handler *)
  | IReact (n i : nat) (e : E).   (* the i-th handler of [n], at payload [e] *)

  Definition istep (γ : State) (ℓ : ILabel) : option State :=
    match ℓ with
    | ICore ℓ => step K_eq_dec Σ progN γ ℓ
    | IReact n i e => step K_eq_dec Σ (progE (Some e)) γ (OReact n i)
    end.

  Fixpoint irun (γ : State) (ls : list ILabel) : option State :=
    match ls with
    | [] => Some γ
    | ℓ :: ls' => match istep γ ℓ with Some γ' => irun γ' ls' | None => None end
    end.

  Definition IReachable (γ : State) : Prop := exists ls, irun (@init K Σ C) ls = Some γ.

  (** ** Tables that agree but for their handler lists *)

  (** Rules other than [O-React] do not read handler lists. *)
  Lemma step_tables x y (γ : State) ℓ :
    (forall n i, ℓ <> OReact n i) -> step K_eq_dec Σ (progE x) γ ℓ = step K_eq_dec Σ (progE y) γ ℓ.
  Proof. intros H; destruct ℓ; try reflexivity; exfalso; eapply H; reflexivity. Qed.

  Lemma wf_tables x y (γ : State) : Preservation.WF K_eq_dec Σ (progE x) γ -> Preservation.WF K_eq_dec Σ (progE y) γ.
  Proof. intros W; destruct W; split; assumption. Qed.

  Lemma prov_tables x y (γ : State) : Prov Σ (progE x) γ -> Prov Σ (progE y) γ.
  Proof. intros [P T]; split; assumption. Qed.

  (** An instance of a handler reacts as the core [O-React] does. *)
  Lemma ireact_shape (γ γ' : State) n i e :
    istep γ (IReact n i e) = Some γ' ->
    exists f acc w h, fibers γ n = Some f /\ life f = Active Σ acc w /\
      nth_error (ireacts (iprog (fcomp f))) i = Some h /\
      step K_eq_dec Σ (progE (Some e)) γ (OReact n i) = Some γ'.
  Proof.
    cbn [istep]; intros H; pose proof H as H0; cbn [Calculus.step] in H.
    destruct (fibers γ n) as [f|]; [|discriminate H].
    destruct (life f) as [| |acc w|] eqn:Hl; try discriminate H.
    destruct (nth_error (ireacts (iprog (fcomp f))) i) as [h|] eqn:Eh.
    - exists f, acc, w, h; auto.
    - exfalso; unfold progE in H; cbn [reacts] in H.
      rewrite nth_error_map, Eh in H; discriminate H.
  Qed.

  (** ** Safety *)
  Theorem ipreservation (γ γ' : State) ℓ : WF γ -> istep γ ℓ = Some γ' -> WF γ'.
  Proof.
    intros W; destruct ℓ as [ℓ|n i e]; cbn [istep]; intros H.
    - exact (preservation K_eq_dec Σ progN γ γ' ℓ W H).
    - apply (wf_tables (Some e) None).
      exact (preservation K_eq_dec Σ (progE (Some e)) γ γ' _ (wf_tables None (Some e) γ W) H).
  Qed.

  Lemma irun_inv (P : State -> Prop) :
    P (@init K Σ C) -> (forall γ γ' ℓ, P γ -> istep γ ℓ = Some γ' -> P γ') ->
    forall γ, IReachable γ -> P γ.
  Proof.
    intros P0 PS γ [ls H].
    assert (G : forall γ0, P γ0 -> irun γ0 ls = Some γ -> P γ).
    { clear H; induction ls as [|ℓ ls IH]; cbn; intros γ0 H0 Hr.
      - injection Hr as <-; exact H0.
      - destruct (istep γ0 ℓ) as [γ1|] eqn:Hs; [|discriminate].
        exact (IH γ1 (PS γ0 γ1 ℓ H0 Hs) Hr). }
    exact (G _ P0 H).
  Qed.

  Theorem iwf_reachable (γ : State) : IReachable γ -> WF γ.
  Proof.
    apply irun_inv; [exact (wf_init K_eq_dec Σ progN) | intros; eapply ipreservation; eauto].
  Qed.

  (** ** Containment: an effect lives inside its parent and its providers *)
  Theorem effect_within (γ : State) x fx :
    WF γ -> fibers γ x = Some fx -> is_installed (life fx) = true ->
    (forall q, fparent fx = Some q ->
       exists fq, fibers γ q = Some fq /\ is_installed (life fq) = true) /\
    (forall k p, In (k, p) (view_of (life fx)) ->
       exists b fo, binds γ k = Some b /\ pid Σ b = p /\ owner b <> x /\
                    fibers γ (owner b) = Some fo /\ is_installed (life fo) = true).
  Proof.
    intros W Hx _; split.
    - intros q Hq; destruct (wf_parent K_eq_dec Σ progN γ W x fx q Hx Hq) as (fq & Hfq & Iq & _).
      exists fq; auto.
    - intros k p Hin; exact (provider_outlives K_eq_dec Σ progN γ x fx k p W Hx Hin).
  Qed.

  (** While another fiber still resolves one of its provisions, an
      Unloading owner undoes nothing and retires no child: the whole of the
      agent's context outlives every effect attached to it. *)
  Theorem unload_blocked_i (γ : State) n f acc w z k p m fm k' :
    WF γ -> fibers γ n = Some f -> life f = Unloading Σ acc w z ->
    In (UProv Σ k p) acc -> m <> n -> fibers γ m = Some fm ->
    In (k', p) (view_of (life fm)) ->
    istep γ (ICore (LUndo n)) = None /\ istep γ (ICore (LRetireChild n)) = None.
  Proof. exact (unload_blocked K_eq_dec Σ progN γ n f acc w z k p m fm k'). Qed.

  (** In particular the agent's entry itself cannot be withdrawn. *)
  Theorem withdraw_blocked_i (γ : State) n f k p acc w z m fm k' :
    WF γ -> fibers γ n = Some f -> life f = Unloading Σ (UProv Σ k p :: acc) w z ->
    m <> n -> fibers γ m = Some fm -> In (k', p) (view_of (life fm)) ->
    istep γ (ICore (LUndo n)) = None.
  Proof. exact (withdraw_blocked K_eq_dec Σ progN γ n f k p acc w z m fm k'). Qed.

  (** A parent finishes withdrawing a reaction only once the child is gone. *)
  Theorem parent_waits_i (γ γ' : State) n f m acc w z :
    fibers γ n = Some f -> life f = Unloading Σ (USpawn Σ m :: acc) w z ->
    istep γ (ICore (LUndo n)) = Some γ' -> fibers γ m = None.
  Proof. exact (parent_waits_child K_eq_dec Σ progN γ γ' n f m acc w z). Qed.

  (** ** Recovery *)
  Hypothesis Hwb : forall a t, WellBehaved (Σ := Σ) a t.
  (** Any two operations two components may perform at one key, the
      components including every handler instance. *)
  Hypothesis Hind : forall k a b ta tb, CoPair Σ progN k a b -> ta <> tb ->
    RevertIndep (Σ := Σ) a ta b tb.

  Section Track.
    Variable n : nat.

    Definition ievent (γ : State) (ℓ : ILabel) : Event Σ :=
      match ℓ with
      | ICore ℓ => event K_eq_dec Σ progN γ ℓ
      | IReact _ _ _ => EvNone Σ
      end.

    Fixpoint ishadow_run (γ : State) (ls : list ILabel) (σ : Store Σ) : option (State * Store Σ) :=
      match ls with
      | [] => Some (γ, σ)
      | ℓ :: ls' =>
          match istep γ ℓ with
          | Some γ' => ishadow_run γ' ls' (shadow_apply K_eq_dec Σ n (ievent γ ℓ) σ)
          | None => None
          end
      end.

    Lemma iR_step (γ γ' : State) ℓ σ :
      WF γ -> Prov Σ progN γ -> R K_eq_dec Σ n γ σ -> istep γ ℓ = Some γ' ->
      WF γ' /\ Prov Σ progN γ' /\ R K_eq_dec Σ n γ' (shadow_apply K_eq_dec Σ n (ievent γ ℓ) σ).
    Proof.
      intros W P HR H; destruct ℓ as [ℓ|m i e]; cbn [istep ievent] in H |- *.
      - split; [exact (preservation K_eq_dec Σ progN γ γ' ℓ W H)|].
        split; [exact (prov_step K_eq_dec Σ progN γ γ' ℓ W P H)|].
        exact (R_step K_eq_dec Σ progN Hwb Hind n γ γ' ℓ σ W P HR H).
      - set (T := progE (Some e)).
        assert (W' : Preservation.WF K_eq_dec Σ T γ) by exact (wf_tables None (Some e) γ W).
        assert (P' : Prov Σ T γ) by exact (prov_tables None (Some e) γ P).
        split; [exact (wf_tables (Some e) None γ' (preservation K_eq_dec Σ T γ γ' _ W' H))|].
        split; [exact (prov_tables (Some e) None γ' (prov_step K_eq_dec Σ T γ γ' _ W' P' H))|].
        exact (R_step K_eq_dec Σ T Hwb Hind n γ γ' (OReact m i) σ W' P' HR H).
    Qed.

    Theorem irecovery (γ : State) ls σ γ' σ' :
      WF γ -> Prov Σ progN γ -> R K_eq_dec Σ n γ σ -> ishadow_run γ ls σ = Some (γ', σ') ->
      WF γ' /\ Prov Σ progN γ' /\ R K_eq_dec Σ n γ' σ'.
    Proof.
      revert γ σ; induction ls as [|ℓ ls IH]; cbn; intros γ σ W P HR H.
      - injection H as <- <-; auto.
      - destruct (istep γ ℓ) as [γ1|] eqn:Hs; [|discriminate].
        destruct (iR_step γ γ1 ℓ σ W P HR Hs) as (W1 & P1 & R1); exact (IH γ1 _ W1 P1 R1 H).
    Qed.

    Theorem irecovery_exact (γ0 : State) ls γ σ :
      WF γ0 -> Prov Σ progN γ0 -> no_pending K_eq_dec Σ n γ0 ->
      ishadow_run γ0 ls (store Σ γ0) = Some (γ, σ) -> no_pending K_eq_dec Σ n γ ->
      forall k, match binds γ k, σ k with
                | Some b, Some s => bst b ≃ s
                | None, None => True
                | _, _ => False
                end.
    Proof.
      intros W P H0 Hrun H1 k.
      destruct (irecovery γ0 ls (store Σ γ0) γ σ W P (R_store K_eq_dec Σ n γ0 H0) Hrun) as (_ & _ & HR).
      specialize (HR k); unfold Rk, pend in HR.
      destruct (binds γ k) as [b|]; [rewrite H1 in HR|]; exact HR.
    Qed.

    (** An effect, from before its fiber exists to after it is gone (the
        agent ended, or the plugin unloaded, or it was disposed), leaves
        every binding as if it had never run. *)
    Corollary ieffect_exact (γ0 : State) ls γ σ :
      WF γ0 -> Prov Σ progN γ0 -> fibers γ0 n = None ->
      ishadow_run γ0 ls (store Σ γ0) = Some (γ, σ) ->
      match fibers γ n with Some f => is_installed (life f) = false | None => True end ->
      forall k, match binds γ k, σ k with
                | Some b, Some s => bst b ≃ s
                | None, None => True
                | _, _ => False
                end.
    Proof.
      intros W P H0 R H1.
      apply (irecovery_exact γ0 ls γ σ W P); [|exact R|].
      - intros k p; unfold pacc; rewrite H0; reflexivity.
      - exact (no_pending_inactive K_eq_dec Σ n γ H1).
    Qed.
  End Track.
End Intersect.
