(** * Extension 1: recovery exactness with optional dependencies

    Counterpart of [Recovery.recovery_exact] and [recovery_from_init], for
    every extended execution (orchestration, runtime reactions and
    extended lifecycle steps, in any order). Fix a fiber [n]; the shadow
    store applies every other fiber's operations and undos and skips
    [n]'s. Once [n] holds no pending operation, the real store is ≃ the
    shadow.

    No restriction on children is needed. An extended step is a core step
    ([xstep_core]), or re-choosing an Inactive fiber's presence followed by
    the core [L-Begin], or the core [O-Restart]; re-choosing presence
    touches neither the store nor any accumulator, so it keeps the core
    invariant [R] ([R_transfer]) and the provenance invariant [Prov]
    ([prov_recomp]). *)

From Stdlib Require Import List PeanoNat Bool Lia RelationClasses.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Recovery.
From Cordis Require Import Ext.Optional.
Import ListNotations.

Section OptRecovery.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type}.
  Context (xprog : C -> @XComponent K Σ C).

  Local Notation CC := (@Optional.C' K C).
  Local Notation State := (@State K Σ CC).
  Local Notation Fiber := (@Fiber K Σ CC).
  Local Notation S := (St Σ).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation life := (life Σ).
  Local Notation bst := (bst Σ).
  Local Notation prog' := (prog' K_eq_dec Σ xprog).
  Local Notation step := (step K_eq_dec Σ prog').
  Local Notation xstep := (xstep K_eq_dec Σ xprog).
  Local Notation recomp := (recomp Σ xprog).
  Local Notation WF := (WF K_eq_dec Σ prog').
  Local Notation Prov := (Prov Σ prog').

  Hypothesis Hwb : forall a t, WellBehaved (Σ := Σ) a t.
  Hypothesis Hind : forall k a b ta tb, CoPair Σ prog' k a b -> ta <> tb ->
    RevertIndep (Σ := Σ) a ta b tb.

  Variable n : nat.

  Local Notation R := (R K_eq_dec Σ n).
  Local Notation shadow_apply := (shadow_apply K_eq_dec Σ n).

  (** The shadow event of an extended step: that of the core label. *)
  Definition xevent (γ : State) (ℓ : @Calculus.Label C) : Event Σ :=
    event K_eq_dec Σ prog' γ (xlab ℓ).

  Lemma prov_recomp (γ : State) m f :
    Prov γ -> fibers γ m = Some f -> is_installed Σ (life f) = false -> Prov (recomp γ m f).
  Proof.
    intros [PF PT] Hm Hi.
    assert (Hb : forall x fx, fibers (recomp γ m f) x = Some fx ->
                 exists fx0, fibers γ x = Some fx0 /\ life fx = life fx0 /\
                             (x <> m -> fx = fx0)).
    { intros x fx H; unfold Optional.recomp, set_fiber, with_fibers in H; cbn in H; unfold fupd in H.
      destruct (Nat.eqb_spec x m) as [->|Hne]; [injection H as <-; exists f; split; [exact Hm|]; split; [reflexivity|]; intros N; contradiction N; reflexivity|].
      exists fx; split; [exact H|]; split; [reflexivity | intros _; reflexivity]. }
    split.
    - intros x fx H; destruct (Hb x fx H) as (fx0 & H0 & El & E).
      destruct (Nat.eq_dec x m) as [->|Hne].
      + destruct (life f) as [z| | |] eqn:L; try discriminate.
        rewrite Hm in H0; injection H0 as <-; rewrite L in El.
        exact (ProvF_inactive Σ prog' _ fx z El).
      + rewrite (E Hne); exact (PF x fx0 H0).
    - intros m1 m2 f1 f2 k1 p1 g1 k2 p2 g2 t Hne H1 H2 I1 I2.
      destruct (Hb m1 f1 H1) as (f1' & H1' & E1 & _), (Hb m2 f2 H2) as (f2' & H2' & E2 & _).
      rewrite E1 in I1; rewrite E2 in I2; exact (PT m1 m2 f1' f2' k1 p1 g1 k2 p2 g2 t Hne H1' H2' I1 I2).
  Qed.

  Lemma R_recomp (γ : State) m f σ : fibers γ m = Some f -> R γ σ -> R (recomp γ m f) σ.
  Proof.
    intros Hm HR; apply (R_transfer K_eq_dec Σ n γ); [intros; reflexivity | | exact HR].
    intros k p; unfold pacc; unfold Optional.recomp, set_fiber, with_fibers; cbn; unfold fupd.
    destruct (Nat.eqb_spec n m) as [->|]; [rewrite Hm; reflexivity | reflexivity].
  Qed.

  Lemma core_inv (γ γ' : State) ℓ σ :
    WF γ -> Prov γ -> R γ σ -> step γ ℓ = Some γ' ->
    WF γ' /\ Prov γ' /\ R γ' (shadow_apply (event K_eq_dec Σ prog' γ ℓ) σ).
  Proof.
    intros W P HR H; split; [exact (preservation K_eq_dec Σ prog' γ γ' ℓ W H)|].
    split; [exact (prov_step K_eq_dec Σ prog' γ γ' ℓ W P H)|].
    exact (R_step K_eq_dec Σ prog' Hwb Hind n γ γ' ℓ σ W P HR H).
  Qed.

  (** ** Every extended step preserves the invariants *)
  Theorem xR_step (γ γ' : State) ℓ σ :
    WF γ -> Prov γ -> R γ σ -> xstep γ ℓ = Some γ' ->
    WF γ' /\ Prov γ' /\ R γ' (shadow_apply (xevent γ ℓ) σ).
  Proof.
    intros W P HR H.
    destruct (xstep_core K_eq_dec Σ xprog γ γ' ℓ H) as [St|[(m & f & -> & Hm & Hl & St)|(m & St)]].
    - exact (core_inv γ γ' _ σ W P HR St).
    - assert (Hi : is_installed Σ (life f) = false) by (rewrite Hl; reflexivity).
      exact (core_inv _ γ' _ σ (wf_recomp K_eq_dec Σ xprog γ m f W Hm Hi) (prov_recomp γ m f P Hm Hi)
               (R_recomp γ m f σ Hm HR) St).
    - destruct (core_inv γ γ' _ σ W P HR St) as (W' & P' & R').
      split; [exact W'|]; split; [exact P'|].
      (* a restart is an extended divert or leave: no shadow event either way *)
      assert (E : xevent γ ℓ = EvNone Σ \/ step γ (xlab ℓ) = Some γ').
      { destruct ℓ as [c|x|x|x|x|x|x|x|x|x|x|x i|x]; try (right; exact H); try (left; reflexivity).
        cbn [Optional.xstep] in H; destruct (fibers γ x) as [fx|]; [|discriminate].
        destruct (fresh K_eq_dec Σ xprog γ fx); [right; exact H | discriminate]. }
      destruct E as [E|E].
      + rewrite E; exact R'.
      + exact (proj2 (proj2 (core_inv γ γ' _ σ W P HR E))).
  Qed.

  (** ** Executions *)
  Fixpoint xshadow_run (γ : State) (ls : list (@Calculus.Label C)) (σ : Store Σ)
    : option (State * Store Σ) :=
    match ls with
    | [] => Some (γ, σ)
    | ℓ :: ls' =>
        match xstep γ ℓ with
        | Some γ' => xshadow_run γ' ls' (shadow_apply (xevent γ ℓ) σ)
        | None => None
        end
    end.

  Lemma xshadow_run_total (γ : State) ls σ γ' :
    xrun K_eq_dec Σ xprog γ ls = Some γ' -> exists σ', xshadow_run γ ls σ = Some (γ', σ').
  Proof.
    revert γ σ; induction ls as [|ℓ ls IH]; cbn; intros γ σ H.
    - injection H as <-; eauto.
    - destruct (xstep γ ℓ); [apply IH; exact H | discriminate].
  Qed.

  Theorem xrecovery (γ : State) ls σ γ' σ' :
    WF γ -> Prov γ -> R γ σ -> xshadow_run γ ls σ = Some (γ', σ') ->
    WF γ' /\ Prov γ' /\ R γ' σ'.
  Proof.
    revert γ σ; induction ls as [|ℓ ls IH]; cbn; intros γ σ W P HR H.
    - injection H as <- <-; auto.
    - destruct (xstep γ ℓ) as [γ1|] eqn:Hs; [|discriminate].
      destruct (xR_step γ γ1 ℓ σ W P HR Hs) as (W1 & P1 & R1); exact (IH γ1 _ W1 P1 R1 H).
  Qed.

  (** Recovery exactness: from a state where [n] holds no pending
      operation, along any extended execution, to a state where it again
      holds none, the real store is ≃ the shadow store. *)
  Theorem xrecovery_exact (γ0 : State) ls γ σ :
    WF γ0 -> Prov γ0 -> no_pending K_eq_dec Σ n γ0 ->
    xshadow_run γ0 ls (store Σ γ0) = Some (γ, σ) -> no_pending K_eq_dec Σ n γ ->
    forall k, match binds γ k, σ k with
              | Some b, Some s => bst b ≃ s
              | None, None => True
              | _, _ => False
              end.
  Proof.
    intros W P H0 Hrun H1 k.
    destruct (xrecovery γ0 ls (store Σ γ0) γ σ W P (R_store K_eq_dec Σ n γ0 H0) Hrun) as (_ & _ & HR).
    specialize (HR k); unfold Rk, pend in HR.
    destruct (binds γ k) as [b|]; [rewrite H1 in HR|]; exact HR.
  Qed.

  (** From the initial state: whenever [n] is not installed, the store is,
      up to ≃, what every other fiber's operations alone produce. *)
  Corollary xrecovery_from_init ls γ σ :
    xshadow_run (@init K Σ CC) ls (fun _ => None) = Some (γ, σ) ->
    match fibers γ n with Some f => is_installed Σ (life f) = false | None => True end ->
    forall k, match binds γ k, σ k with
              | Some b, Some s => bst b ≃ s
              | None, None => True
              | _, _ => False
              end.
  Proof.
    intros Hrun Hn.
    apply (xrecovery_exact (@init K Σ CC) ls); auto.
    - exact (wf_init K_eq_dec Σ prog').
    - exact (prov_init Σ prog').
    - intros k p; reflexivity.
    - apply no_pending_inactive; exact Hn.
  Qed.
End OptRecovery.
