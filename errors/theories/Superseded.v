(** * A superseded load does not fail (errors/DESIGN.md, section 4.0)

    In the core, a Loading fiber whose target has turned may still take
    [L-Step] (an iteration in flight lands), so when its next instruction
    fails, both [L-Step] (ending [Inactive (Some ξ)]) and [L-Divert]
    (ending [Inactive None]) apply, and which one happens is up to the
    schedule. Cordis always takes the second: a load whose epoch has
    changed is cleaned up but "cannot fail the new target"
    (cordis [fiber.ts:466]).

    [sstep] is [step] with that choice made: a failing [L-Step] on a fiber
    whose target has turned is the [L-Divert] step instead. It changes
    nothing else.

    - [sstep_core]: every [sstep] is a core [step], on the same label or on
      [LDivert n] in place of [LStep n]. So every [sstep] execution is a
      core execution ([srun_core]), and every invariant of the core holds
      ([sinv_step]); safety ([swf_reachable]) and termination
      ([stermination], [stermination_reachable]) follow.
    - [sstep_some]: the same labels are enabled under both, so quiescence
      is the same ([squiet_iff]) and progress carries over
      ([sprogress_reachable]).
    - [sfail_current]: under [sstep] a load ends in failure only while its
      target is still the view it committed to.

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool.
From Cordis Require Import Prelude Service Calculus Preservation Progress Termination.
Import ListNotations.

Section Superseded.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).
  Local Notation Label := (@Label C).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation load_step := (load_step K_eq_dec Σ prog).
  Local Notation target_is := (target_is K_eq_dec Σ prog).
  Local Notation may_step := (may_step K_eq_dec Σ prog).

  (** ** The rule *)

  (** Did [n] just fail? [load_step] leaves [n] Unloading with an error
      exactly when the instruction failed. *)
  Definition failed_at (γ : State) (n : nat) : bool :=
    match fibers Σ γ n with
    | Some f => match life Σ f with Unloading _ _ _ (Some _) => true | _ => false end
    | None => false
    end.

  Definition sstep (γ : State) (ℓ : Label) : option State :=
    match ℓ with
    | LStep n =>
        match fibers Σ γ n with
        | Some f =>
            match life Σ f with
            | Loading _ P acc w =>
                if may_step γ n P w then
                  if negb (target_is γ n w) && failed_at (load_step γ n f P acc w) n
                  then Some (set_life Σ γ n f (Unloading Σ acc w None))
                  else Some (load_step γ n f P acc w)
                else None
            | _ => None
            end
        | None => None
        end
    | _ => step γ ℓ
    end.

  Fixpoint srun_labels (γ : State) (ls : list Label) : option State :=
    match ls with
    | [] => Some γ
    | ℓ :: ls' =>
        match sstep γ ℓ with
        | Some γ' => srun_labels γ' ls'
        | None => None
        end
    end.

  (** ** Refinement of the core *)

  (** The core label that does what an [sstep] did. *)
  Definition core_label (γ : State) (ℓ : Label) : Label :=
    match ℓ with
    | LStep n =>
        match fibers Σ γ n with
        | Some f =>
            match life Σ f with
            | Loading _ P acc w =>
                if negb (target_is γ n w) && failed_at (load_step γ n f P acc w) n
                then LDivert n else LStep n
            | _ => LStep n
            end
        | None => LStep n
        end
    | _ => ℓ
    end.

  Lemma sstep_core (γ γ' : State) (ℓ : Label) :
    sstep γ ℓ = Some γ' -> step γ (core_label γ ℓ) = Some γ'.
  Proof.
    destruct ℓ; cbn [sstep core_label]; intros H; try exact H.
    destruct (fibers Σ γ n) as [f|] eqn:Hn; [|discriminate].
    destruct (life Σ f) as [|P acc w| |] eqn:Hl; try discriminate.
    destruct (may_step γ n P w) eqn:Hm; [|discriminate].
    destruct (negb (target_is γ n w) && failed_at (load_step γ n f P acc w) n) eqn:Hc.
    - injection H as <-.
      apply andb_true_iff in Hc as [Ht _]; apply negb_true_iff in Ht.
      cbn [step]; rewrite Hn, Hl, Ht; reflexivity.
    - cbn [step]; rewrite Hn, Hl, Hm; exact H.
  Qed.

  (** The replacement stays at the same fiber and stays a lifecycle step. *)
  Lemma core_label_lifecycle (γ : State) n ℓ :
    In ℓ (lifecycle_labels n) -> In (core_label γ ℓ) (lifecycle_labels n).
  Proof.
    intros Hin.
    destruct ℓ; cbn [core_label]; try exact Hin.
    assert (n0 = n) as ->.
    { cbn in Hin; repeat (destruct Hin as [Hin|Hin]; [congruence|]); destruct Hin. }
    destruct (fibers Σ γ n) as [f|]; [|exact Hin].
    destruct (life Σ f) as [|P acc w| |]; try exact Hin.
    destruct (negb (target_is γ n w) && failed_at (load_step γ n f P acc w) n);
      [cbn; auto 10 | exact Hin].
  Qed.

  (** Every [sstep] execution is a core execution. *)
  Theorem srun_core (γ0 γ : State) ls :
    srun_labels γ0 ls = Some γ ->
    exists ls', run_labels K_eq_dec Σ prog γ0 ls' = Some γ.
  Proof.
    revert γ0; induction ls as [|ℓ ls IH]; cbn; intros γ0 H.
    - injection H as <-; exists []; reflexivity.
    - destruct (sstep γ0 ℓ) as [γ1|] eqn:Hs; [|discriminate].
      destruct (IH γ1 H) as [ls' Hr].
      exists (core_label γ0 ℓ :: ls'); cbn; rewrite (sstep_core γ0 γ1 ℓ Hs); exact Hr.
  Qed.

  (** Any property the core steps preserve, [sstep] preserves. *)
  Lemma sinv_step (P : State -> Prop) :
    (forall γ γ' ℓ, P γ -> step γ ℓ = Some γ' -> P γ') ->
    forall γ γ' ℓ, P γ -> sstep γ ℓ = Some γ' -> P γ'.
  Proof. intros HP γ γ' ℓ Hγ H; exact (HP _ _ _ Hγ (sstep_core γ γ' ℓ H)). Qed.

  (** ** Safety *)
  Corollary swf_reachable (γ : State) ls :
    srun_labels (@init K Σ C) ls = Some γ -> WF K_eq_dec Σ prog γ.
  Proof.
    intros H; destruct (srun_core _ _ ls H) as [ls' Hr].
    exact (wf_reachable K_eq_dec Σ prog γ ls' Hr).
  Qed.

  (** ** Enabledness, quiescence, progress *)

  (** [sstep] and [step] are enabled on exactly the same labels. *)
  Lemma sstep_some (γ : State) (ℓ : Label) :
    (exists γ', sstep γ ℓ = Some γ') <-> (exists γ', step γ ℓ = Some γ').
  Proof.
    destruct ℓ; cbn [sstep]; try reflexivity.
    cbn [step].
    destruct (fibers Σ γ n) as [f|]; [|reflexivity].
    destruct (life Σ f) as [|P acc w| |]; try reflexivity.
    destruct (may_step γ n P w); [|reflexivity].
    destruct (negb (target_is γ n w) && failed_at (load_step γ n f P acc w) n);
      split; intros _; eauto.
  Qed.

  Lemma sstep_none (γ : State) (ℓ : Label) :
    sstep γ ℓ = None <-> step γ ℓ = None.
  Proof.
    pose proof (sstep_some γ ℓ) as E.
    destruct (sstep γ ℓ), (step γ ℓ); split; intros H; try reflexivity; try discriminate.
    - destruct (proj1 E (ex_intro _ _ eq_refl)) as [? ?]; discriminate.
    - destruct (proj2 E (ex_intro _ _ eq_refl)) as [? ?]; discriminate.
  Qed.

  Definition squiet (γ : State) : Prop :=
    forall n ℓ, In ℓ (lifecycle_labels n) -> sstep γ ℓ = None.

  Lemma squiet_iff (γ : State) : squiet γ <-> quiet K_eq_dec Σ prog γ.
  Proof.
    unfold squiet, quiet; split; intros H n ℓ Hin.
    - apply (proj1 (sstep_none γ ℓ)); exact (H n ℓ Hin).
    - apply (proj2 (sstep_none γ ℓ)); exact (H n ℓ Hin).
  Qed.

  (** Every state [sstep] reaches is settled or can take a lifecycle step. *)
  Corollary sprogress_reachable
      (Hwf : well_founded (fun c' c => Above Σ prog c c')) ls (γ : State) :
    srun_labels (@init K Σ C) ls = Some γ ->
    settled Σ prog γ \/ exists n ℓ γ', In ℓ (lifecycle_labels n) /\ sstep γ ℓ = Some γ'.
  Proof.
    intros H; destruct (srun_core _ _ ls H) as [ls' Hr].
    destruct (progress_reachable K_eq_dec Σ prog Hwf ls' γ Hr) as [S|(n & ℓ & γ' & Hin & Hs)];
      [left; exact S | right].
    destruct (proj2 (sstep_some γ ℓ) (ex_intro _ γ' Hs)) as [γ'' Hs'].
    exists n, ℓ, γ''; auto.
  Qed.

  (** ** Termination *)

  (** A lifecycle [sstep] is a lifecycle core step, so well-foundedness of
      the core's lifecycle steps (under any invariant [I]) carries over. *)
  Lemma sacc (I : State -> Prop) (γ : State) :
    Acc (fun γ' γ => I γ /\ exists n ℓ, In ℓ (lifecycle_labels n) /\ step γ ℓ = Some γ') γ ->
    Acc (fun γ' γ => I γ /\ exists n ℓ, In ℓ (lifecycle_labels n) /\ sstep γ ℓ = Some γ') γ.
  Proof.
    induction 1 as [γ _ IH]; constructor; intros γ' [Iγ (n & ℓ & Hin & Hs)].
    apply IH; split; [exact Iγ|].
    exists n, (core_label γ ℓ); split;
      [exact (core_label_lifecycle γ n ℓ Hin) | exact (sstep_core γ γ' ℓ Hs)].
  Qed.

  Section Term.
    Variable Kb : nat.
    Hypothesis HK : forall c, Bounded Σ Kb (body Σ (prog c)).
    Variable rank : C -> nat.
    Variable Rb : nat.
    Hypothesis Hrank : forall c c', Above Σ prog c c' -> rank c < rank c'.
    Hypothesis Hbnd : forall c, rank c <= Rb.

    Local Notation TInv := (TInv K_eq_dec Σ prog Kb).

    Definition sLStepRel (γ' γ : State) : Prop :=
      TInv γ /\ exists n ℓ, In ℓ (lifecycle_labels n) /\ sstep γ ℓ = Some γ'.

    Theorem stermination (γ : State) : TInv γ -> Acc sLStepRel γ.
    Proof.
      intros I; apply (sacc TInv).
      exact (termination K_eq_dec Σ prog Kb HK rank Rb Hrank Hbnd γ I).
    Qed.

    Corollary stermination_reachable ls (γ : State) :
      srun_labels (@init K Σ C) ls = Some γ -> Acc sLStepRel γ.
    Proof.
      intros H; destruct (srun_core _ _ ls H) as [ls' Hr].
      apply (sacc TInv).
      exact (termination_reachable K_eq_dec Σ prog Kb HK rank Rb Hrank Hbnd ls' γ Hr).
    Qed.
  End Term.

  (** ** A load fails only while it is current *)
  Theorem sfail_current (γ γ' : State) n f P acc w :
    fibers Σ γ n = Some f -> life Σ f = Loading Σ P acc w ->
    sstep γ (LStep n) = Some γ' -> failed_at γ' n = true ->
    target_is γ n w = true.
  Proof.
    intros Hn Hl H Hf; cbn [sstep] in H; rewrite Hn, Hl in H.
    destruct (may_step γ n P w); [|discriminate].
    destruct (target_is γ n w) eqn:Ht; [reflexivity|].
    destruct (failed_at (load_step γ n f P acc w) n) eqn:Hc; cbn in H.
    - injection H as <-.
      unfold failed_at in Hf; unfold set_life, set_fiber, with_fibers in Hf; cbn in Hf.
      unfold fupd in Hf; rewrite Nat.eqb_refl in Hf; cbn in Hf; discriminate.
    - injection H as <-; rewrite Hc in Hf; discriminate.
  Qed.
End Superseded.
