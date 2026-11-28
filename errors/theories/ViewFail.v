(** * Failures scoped to their view (errors/DESIGN.md, section 1)

    In the core a failed fiber stays [Inactive (Some ξ)] until the
    orchestrator resets it, even after its dependencies have been provided
    afresh and the reason for the failure may be gone. Whether a failure is
    still there at the end then depends on the schedule: in one schedule the
    fiber loads under an old provider and fails, in another it first loads
    under the new one and succeeds ([core_diverges] below). Confluence can
    only include failures if a failure counts for the view it happened
    under, and no longer.

    The state records, for each fiber, the view it last unloaded from
    ([fview], written by [L-Unloaded]). The new lifecycle rule
    [VClear n] clears the failure of an Inactive failed fiber whose target
    is no longer that view; it is the core [O-Reset n], taken by the
    runtime instead of the orchestrator.

    - [vstep_core], [vrun_core], [vwf_reachable]: every step is a core
      step ([VClear] is [O-Reset]); safety carries over.
    - [vquiet_current]: at a quiet reachable state every failed fiber
      failed under the view that is its target now. This is the property
      the confluence proof with failures starts from (DESIGN.md section 3).
    - [core_diverges], [view_agrees]: a computed example. With the same
      orchestration inputs, the core ends with a failed consumer in one
      schedule and an Active one in another; with [VClear] the first
      schedule goes on to the same end as the second.

    Termination needs its own measure (a failed fiber whose target has
    moved on carries pending work, like an Inactive fiber with a target)
    and is not proved here.

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool.
From Cordis Require Import Prelude Service Calculus Preservation Progress.
Import ListNotations.

Section ViewFail.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).
  Local Notation Label := (@Label C).
  Local Notation View := (@View K).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation target := (Calculus.target Σ prog).
  Local Notation target_is := (target_is K_eq_dec Σ prog).

  (** ** State and rules *)
  Record VState : Type := mkV {
    vcore : State;
    fview : nat -> option View
  }.

  Definition vinit : VState := mkV (@init K Σ C) (fun _ => None).

  Inductive VLabel : Type :=
  | VCore (ℓ : Label)
  | VClear (n : nat).

  Definition vupd (F : nat -> option View) (n : nat) (o : option View) :=
    fun m => if Nat.eqb m n then o else F m.

  (** The view [n] unloads from, when [L-Unloaded n] applies. *)
  Definition unloading_view (γ : State) (n : nat) : option View :=
    match fibers Σ γ n with
    | Some f => match life Σ f with Unloading _ [] w _ => Some w | _ => None end
    | None => None
    end.

  Definition clearable (γ : State) (F : nat -> option View) (n : nat) : bool :=
    match fibers Σ γ n, F n with
    | Some f, Some w =>
        match life Σ f with
        | Inactive _ (Some _) => negb (target_is γ n w)
        | _ => false
        end
    | _, _ => false
    end.

  Definition vstep (vs : VState) (ℓ : VLabel) : option VState :=
    match ℓ with
    | VCore (LUnloaded n) =>
        match step (vcore vs) (LUnloaded n) with
        | Some γ' => Some (mkV γ' (vupd (fview vs) n (unloading_view (vcore vs) n)))
        | None => None
        end
    | VCore ℓ =>
        match step (vcore vs) ℓ with
        | Some γ' => Some (mkV γ' (fview vs))
        | None => None
        end
    | VClear n =>
        if clearable (vcore vs) (fview vs) n then
          match step (vcore vs) (OReset n) with
          | Some γ' => Some (mkV γ' (fview vs))
          | None => None
          end
        else None
    end.

  Fixpoint vrun_labels (vs : VState) (ls : list VLabel) : option VState :=
    match ls with
    | [] => Some vs
    | ℓ :: ls' => match vstep vs ℓ with Some vs' => vrun_labels vs' ls' | None => None end
    end.

  (** ** Correspondence with the core *)
  Definition vlabel (ℓ : VLabel) : Label :=
    match ℓ with VCore ℓ => ℓ | VClear n => OReset n end.

  Lemma vstep_core (vs vs' : VState) ℓ :
    vstep vs ℓ = Some vs' -> step (vcore vs) (vlabel ℓ) = Some (vcore vs').
  Proof.
    destruct ℓ as [ℓ|n]; cbn [vstep vlabel].
    - destruct ℓ; destruct (step (vcore vs) _); try discriminate; intros [= <-]; reflexivity.
    - destruct (clearable _ _ n); [|discriminate].
      destruct (step (vcore vs) (OReset n)); [intros [= <-]; reflexivity | discriminate].
  Qed.

  Theorem vrun_core (vs0 vs : VState) ls :
    vrun_labels vs0 ls = Some vs ->
    run_labels K_eq_dec Σ prog (vcore vs0) (map vlabel ls) = Some (vcore vs).
  Proof.
    revert vs0; induction ls as [|ℓ ls IH]; cbn; intros vs0 H.
    - injection H as <-; reflexivity.
    - destruct (vstep vs0 ℓ) as [vs1|] eqn:Hs; [|discriminate].
      rewrite (vstep_core vs0 vs1 ℓ Hs); exact (IH vs1 H).
  Qed.

  Corollary vwf_reachable (vs : VState) ls :
    vrun_labels vinit ls = Some vs -> WF K_eq_dec Σ prog (vcore vs).
  Proof.
    intros H; exact (wf_reachable K_eq_dec Σ prog _ _ (vrun_core _ _ ls H)).
  Qed.

  (** A core lifecycle label goes through unchanged on the core state. *)
  Lemma vstep_lifecycle_back (vs : VState) n ℓ γ' :
    In ℓ (lifecycle_labels n) -> step (vcore vs) ℓ = Some γ' ->
    exists vs', vstep vs (VCore ℓ) = Some vs'.
  Proof.
    intros Hin H; cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [vstep]; rewrite H; eauto|]).
    destruct Hin.
  Qed.

  (** ** Where failures come from *)

  (** A fiber that is Inactive with an error after a core step was so
      before, or the step was [L-Unloaded] on it. *)
  Lemma load_step_failed (γ : State) n f P acc w m fm z :
    fibers Σ (load_step K_eq_dec Σ prog γ n f P acc w) m = Some fm ->
    life Σ fm = Inactive Σ (Some z) -> m <> n /\ fibers Σ γ m = Some fm.
  Proof.
    intros Hm Hl.
    assert (R : forall γ1 l, fibers Σ (set_life Σ γ1 n f l) m = Some fm ->
                (forall z', l <> Inactive Σ (Some z')) ->
                (forall x, fibers Σ γ1 x = fibers Σ γ x \/
                           (x = next Σ γ /\ exists c p, fibers Σ γ1 x =
                              Some (mkFiber Σ c p false (Inactive Σ None)))) ->
                m <> n /\ fibers Σ γ m = Some fm).
    { intros γ1 l H Hnl Hf; rewrite fibers_set_life in H.
      destruct (Nat.eqb_spec m n) as [->|Hmn].
      - injection H as <-; cbn in Hl; exfalso; exact (Hnl z Hl).
      - split; [exact Hmn|].
        destruct (Hf m) as [E|(_ & c & p & E)]; rewrite E in H; [exact H|].
        injection H as <-; cbn in Hl; discriminate. }
    assert (Same : forall γ1, fibers Σ γ1 = fibers Σ γ ->
                   forall x, fibers Σ γ1 x = fibers Σ γ x \/
                     (x = next Σ γ /\ exists c p, fibers Σ γ1 x =
                        Some (mkFiber Σ c p false (Inactive Σ None)))).
    { intros γ1 E x; left; rewrite E; reflexivity. }
    destruct P as [| |k a κ|k s P'|c P']; cbn [load_step] in Hm.
    - eapply R; [exact Hm | discriminate | apply Same; reflexivity].
    - eapply R; [exact Hm | discriminate | apply Same; reflexivity].
    - repeat match type of Hm with
             | context [match ?x with _ => _ end] => destruct x
             end;
        (eapply R; [exact Hm | discriminate | apply Same; reflexivity]).
    - repeat match type of Hm with
             | context [match ?x with _ => _ end] => destruct x
             end;
        (eapply R; [exact Hm | discriminate | apply Same; reflexivity]).
    - destruct (conflict K_eq_dec Σ prog γ c).
      + eapply R; [exact Hm | discriminate | apply Same; reflexivity].
      + eapply R; [exact Hm | discriminate |].
        intros x; cbn; unfold fupd.
        destruct (Nat.eqb_spec x (next Σ γ)) as [->|]; [right; split; eauto | left; reflexivity].
  Qed.

  Lemma failed_after (γ γ' : State) ℓ m fm z :
    step γ ℓ = Some γ' -> fibers Σ γ' m = Some fm -> life Σ fm = Inactive Σ (Some z) ->
    (exists f, fibers Σ γ m = Some f /\ life Σ f = Inactive Σ (Some z)) \/ ℓ = LUnloaded m.
  Proof.
    intros H Hm Hl.
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [step] in H.
    - (* OInsert *)
      destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      cbn in Hm; unfold fupd in Hm; destruct (Nat.eqb_spec m (next Σ γ)).
      + injection Hm as <-; cbn in Hl; discriminate.
      + left; eauto.
    - (* ODispose *)
      destruct (fibers Σ γ n) as [fn|] eqn:Hn; [|discriminate]; injection H as <-.
      unfold set_fiber, with_fibers, fupd in Hm; cbn in Hm.
      destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; cbn in Hl; left; eauto.
      + left; eauto.
    - (* OReset *)
      destruct (fibers Σ γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life Σ fn) as [[z'|]| | |]; try discriminate; injection H as <-.
      rewrite fibers_set_life in Hm; destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; cbn in Hl; discriminate.
      + left; eauto.
    - (* LBegin *)
      destruct (fibers Σ γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life Σ fn) as [[z'|]| | |]; try discriminate.
      destruct (target γ n); [|discriminate]; injection H as <-.
      rewrite fibers_set_life in Hm; destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; cbn in Hl; discriminate.
      + left; eauto.
    - (* LStep *)
      destruct (fibers Σ γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life Σ fn) as [|P acc w| |]; try discriminate.
      destruct (may_step K_eq_dec Σ prog γ n P w); [|discriminate]; injection H as <-.
      destruct (load_step_failed γ n fn P acc w m fm z Hm Hl) as [_ H]; left; eauto.
    - (* LDivert *)
      destruct (fibers Σ γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life Σ fn) as [|P acc w| |]; try discriminate.
      destruct (target_is γ n w); [discriminate|]; injection H as <-.
      rewrite fibers_set_life in Hm; destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; cbn in Hl; discriminate.
      + left; eauto.
    - (* LLeave *)
      destruct (fibers Σ γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life Σ fn) as [| |acc w|]; try discriminate.
      destruct (target_is γ n w); [discriminate|]; injection H as <-.
      rewrite fibers_set_life in Hm; destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; cbn in Hl; discriminate.
      + left; eauto.
    - (* LUndo *)
      destruct (fibers Σ γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life Σ fn) as [| | |[|u acc] w z']; try discriminate.
      destruct (held Σ γ n (u :: acc)); [discriminate|].
      unfold undo_step in H.
      repeat match type of H with
             | context [match ?x with _ => _ end] => destruct x
             end; try discriminate;
        injection H as <-; rewrite fibers_set_life in Hm;
        (destruct (Nat.eqb_spec m n) as [->|];
         [injection Hm as <-; cbn in Hl; discriminate | left; eauto]).
    - (* LRetireChild *)
      destruct (fibers Σ γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life Σ fn) as [| | |[|[| |m'] acc] w z']; try discriminate.
      destruct (fibers Σ γ m') as [g|] eqn:Hg; [|discriminate].
      destruct (held Σ γ n (USpawn Σ m' :: acc) || disposed Σ g); [discriminate|].
      injection H as <-; unfold set_fiber, with_fibers, fupd in Hm; cbn in Hm.
      destruct (Nat.eqb_spec m m') as [->|].
      + injection Hm as <-; cbn in Hl; left; eauto.
      + left; eauto.
    - (* LUnloaded *)
      destruct (fibers Σ γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life Σ fn) as [| | |[|u acc] w z']; try discriminate; injection H as <-.
      rewrite fibers_set_life in Hm; destruct (Nat.eqb_spec m n) as [->|];
        [right; reflexivity | left; eauto].
    - (* LRemove *)
      destruct (fibers Σ γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life Σ fn); try discriminate.
      destruct (disposed Σ fn && negb (has_child Σ γ n)); [|discriminate]; injection H as <-.
      cbn in Hm; unfold fupd in Hm; destruct (Nat.eqb_spec m n); [discriminate | left; eauto].
    - (* OReact *)
      destruct (fibers Σ γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life Σ fn) as [| |acc w|]; try discriminate.
      destruct (nth_error (reacts Σ (prog (comp Σ fn))) i) as [c|]; [|discriminate].
      destruct (disposed Σ fn || conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      rewrite fibers_set_life in Hm; destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; cbn in Hl; discriminate.
      + cbn in Hm; unfold fupd in Hm; destruct (Nat.eqb_spec m (next Σ γ)).
        * injection Hm as <-; cbn in Hl; discriminate.
        * left; eauto.
    - (* ORestart *)
      fold (step γ (ORestart n)) in H.
      apply restart_shape in H as (fn & acc & w & Hn & _ & _ & ->).
      rewrite fibers_set_life in Hm; destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; cbn in Hl; discriminate.
      + left; eauto.
  Qed.

  (** ** Every failed fiber has a recorded view *)
  Definition VInv (vs : VState) : Prop :=
    forall n f z, fibers Σ (vcore vs) n = Some f -> life Σ f = Inactive Σ (Some z) ->
      exists w, fview vs n = Some w.

  Lemma unloaded_view (γ γ' : State) n :
    step γ (LUnloaded n) = Some γ' -> exists w, unloading_view γ n = Some w.
  Proof.
    cbn [step]; unfold unloading_view.
    destruct (fibers Σ γ n) as [fn|]; [|discriminate].
    destruct (life Σ fn) as [| | |[|u acc] w z]; try discriminate; eauto.
  Qed.

  Lemma vstep_fview (vs vs' : VState) ℓ :
    vstep vs ℓ = Some vs' ->
    fview vs' = match ℓ with
                | VCore (LUnloaded n) => vupd (fview vs) n (unloading_view (vcore vs) n)
                | _ => fview vs
                end.
  Proof.
    destruct ℓ as [ℓ|n]; cbn [vstep].
    - destruct ℓ; destruct (step (vcore vs) _); try discriminate; intros [= <-]; reflexivity.
    - destruct (clearable _ _ n); [|discriminate].
      destruct (step (vcore vs) (OReset n)); [intros [= <-]; reflexivity | discriminate].
  Qed.

  Theorem vinv_step (vs vs' : VState) ℓ : VInv vs -> vstep vs ℓ = Some vs' -> VInv vs'.
  Proof.
    intros I H m fm z Hm Hl.
    pose proof (vstep_core vs vs' ℓ H) as Hs.
    pose proof (vstep_fview vs vs' ℓ H) as HF.
    destruct (failed_after _ _ _ m fm z Hs Hm Hl) as [(f & Hf & Hfl)|HU].
    - destruct (I m f z Hf Hfl) as [w Hw].
      destruct ℓ as [[c|n|n|n|n|n|n|n|n|n|n|n i|n]|n]; rewrite HF; eauto.
      (* L-Unloaded n with n <> m: n was Unloading, m was failed *)
      unfold vupd; destruct (Nat.eqb_spec m n) as [->|]; [|eauto].
      cbn [vlabel step] in Hs; rewrite Hf, Hfl in Hs; discriminate.
    - destruct ℓ as [ℓ|n]; cbn [vlabel] in HU; [|discriminate]; subst ℓ.
      rewrite HF; unfold vupd; rewrite Nat.eqb_refl.
      exact (unloaded_view _ _ m Hs).
  Qed.

  Corollary vinv_reachable (vs : VState) ls : vrun_labels vinit ls = Some vs -> VInv vs.
  Proof.
    assert (G : forall vs0 ls vs, VInv vs0 -> vrun_labels vs0 ls = Some vs -> VInv vs).
    { intros vs0 ls0; revert vs0; induction ls0 as [|ℓ ls0 IH]; cbn; intros vs0 vs1 I0 H.
      - injection H as <-; exact I0.
      - destruct (vstep vs0 ℓ) as [vs0'|] eqn:Hs; [|discriminate].
        exact (IH vs0' vs1 (vinv_step vs0 vs0' ℓ I0 Hs) H). }
    apply G; intros n f z Hn; discriminate.
  Qed.

  (** ** Quiet states *)
  Definition vquiet (vs : VState) : Prop :=
    (forall n ℓ, In ℓ (lifecycle_labels n) -> vstep vs (VCore ℓ) = None) /\
    (forall n, vstep vs (VClear n) = None).

  Lemma target_is_true (γ : State) n w : target_is γ n w = true -> target γ n = Some w.
  Proof.
    unfold target_is; destruct (target γ n) as [w'|]; [|discriminate].
    destruct (view_eq_dec K_eq_dec w w') as [->|]; [reflexivity | discriminate].
  Qed.

  (** At a quiet reachable state the core state is settled, and every failed
      fiber failed under the view that is its target now. *)
  Theorem vquiet_current (Hwf : well_founded (fun c' c => Above Σ prog c c')) (vs : VState) ls :
    vrun_labels vinit ls = Some vs -> vquiet vs ->
    settled Σ prog (vcore vs) /\
    forall n f z, fibers Σ (vcore vs) n = Some f -> life Σ f = Inactive Σ (Some z) ->
      exists w, fview vs n = Some w /\ target (vcore vs) n = Some w.
  Proof.
    intros H [QL QC]; split.
    - destruct (progress_reachable K_eq_dec Σ prog Hwf _ _ (vrun_core _ _ ls H))
        as [S|(n & ℓ & γ' & Hin & Hs)]; [exact S|].
      destruct (vstep_lifecycle_back vs n ℓ γ' Hin Hs) as [vs' Hv].
      rewrite (QL n ℓ Hin) in Hv; discriminate.
    - intros n f z Hn Hl.
      destruct (vinv_reachable vs ls H n f z Hn Hl) as [w Hw].
      exists w; split; [exact Hw|].
      apply target_is_true.
      destruct (target_is (vcore vs) n w) eqn:Ht; [reflexivity|exfalso].
      pose proof (QC n) as Q; cbn [vstep] in Q.
      unfold clearable in Q; rewrite Hn, Hw, Hl, Ht in Q; cbn in Q.
      cbn [step] in Q; rewrite Hn, Hl in Q; discriminate.
  Qed.
End ViewFail.

(** ** A failure that outlives its reason *)

From Cordis Require Import Services.Registry Examples.Basic.

(** Component 0 provides [tools] with name 7 already taken; component 2
    provides it empty; component 1 is [Basic.consumer], which registers
    name 7. Under component 0 the consumer fails ([EOp]); under component 2
    it succeeds. *)
Definition reg7 : St ΣR := fun x => if Nat.eqb x 7 then Some 0 else None.

Definition provider7 : @Component nat ΣR nat :=
  mkComponent [] [tools] (PProvide (Σ := ΣR) tools reg7 PDone) [].

Definition progVF (c : nat) : @Component nat ΣR nat :=
  match c with 0 => provider7 | 1 => consumer | _ => provider end.

Definition runVF := run_labels Nat.eq_dec ΣR progVF.
Definition stepVF := step Nat.eq_dec ΣR progVF.
Definition vrunVF := vrun_labels Nat.eq_dec ΣR progVF.

(** The consumer's lifecycle tag and error, the new provider's tag (it has
    the name [p]), and the tool registered under 7. *)
Definition errVF (γ : @State nat ΣR nat) (n : nat) : option (option Err) :=
  match fibers ΣR γ n with
  | Some f => match life ΣR f with Inactive _ z => Some z | _ => None end
  | None => None
  end.

Definition obsVF (p : nat) (γ : option (@State nat ΣR nat)) :=
  match γ with
  | Some γ => Some (tag γ 1, errVF γ 1, tag γ p, tool γ 7)
  | None => None
  end.

(** Schedule A: the consumer loads under component 0 and fails; then the
    orchestrator replaces component 0 by component 2. *)
Definition schedA : list (@Label nat) :=
  [OInsert 0; OInsert 1;
   LBegin 0; LStep 0; LStep 0;
   LBegin 1; LStep 1; LUnloaded 1;
   ODispose 0; LLeave 0; LUndo 0; LUnloaded 0; LRemove 0;
   OInsert 2; LBegin 4; LStep 4; LStep 4].

(** Schedule B: the same orchestration inputs, in the same order; component 0
    is disposed before it loads, and the consumer first loads under
    component 2. *)
Definition schedB : list (@Label nat) :=
  [OInsert 0; OInsert 1;
   ODispose 0; LRemove 0;
   OInsert 2; LBegin 2; LStep 2; LStep 2;
   LBegin 1; LStep 1; LStep 1].

(** In the core the two end differently, and both are quiet for the
    consumer: in A it stays failed although component 2 is Active. *)
Example core_diverges :
  (obsVF 4 (runVF S0 schedA), obsVF 2 (runVF S0 schedB)) =
  (Some (Some 0, Some (Some EOp), Some 2, Some None),
   Some (Some 2, None, Some 2, Some (Some 42))).
Proof. reflexivity. Qed.

Example core_stuck :
  match runVF S0 schedA with Some γ => stepVF γ (LBegin 1) | None => Some S0 end = None.
Proof. reflexivity. Qed.

(** With failures scoped to their view, schedule A goes on: the consumer's
    failure was under component 0's provision, its target now resolves to
    component 2's, so the failure is cleared and it loads like in B. *)
Example view_agrees :
  obsVF 4 (option_map (vcore ΣR)
             (vrunVF (vinit ΣR) (map VCore schedA ++
                                 [VClear 1; VCore (LBegin 1); VCore (LStep 1); VCore (LStep 1)])))
  = Some (Some 2, None, Some 2, Some (Some 42)).
Proof. reflexivity. Qed.
