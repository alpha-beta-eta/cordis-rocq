(** * Extension 1: optional dependencies (docs/EXTENSIONS.md, section 1)

    A component may declare keys it uses when they are there but does not
    wait for ([xopt]). Its startup program is chosen by which of them are
    present when it begins loading ([xbody T], [T] the presence test), and
    a present optional key enters its view, so the program may operate on
    it. When the set of present optional keys changes, in either direction,
    the fiber reloads; otherwise the final state would depend on when a
    provider happened to appear.

    The extension is not a new calculus. A fiber's component is a pair
    [(c, S)]: the base component and the optional keys present when it
    began loading. The core table [prog'] reads [(c, S)] as the base
    component with [S] appended to its dependencies and the variant
    [xbody c (∈ S)] as its program. Then every extended step is
    - a core step of [prog'], or
    - [X-Begin]: re-choosing [S] for an Inactive fiber, then the core
      [L-Begin]; or
    - a reload because the present set changed: the core [O-Restart].
    ([xstep_core]). Re-choosing [S] for an Inactive fiber keeps the core
    invariant [WF] ([wf_recomp]), so the core [preservation] gives safety
    for every extended execution ([xwf_reachable]); with no optional key
    anywhere the extended step is the core step ([xstep_conservative]).

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service Calculus Preservation.
Import ListNotations.

Section Optional.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type}.

  (** ** Components with optional dependencies *)
  Record XComponent : Type := mkX {
    xdeps : list K;                        (* required *)
    xopt : list K;                         (* optional *)
    xprovs : list K;
    xbody : (K -> bool) -> @Prog K Σ C;    (* by presence of the optional keys *)
    xreacts : list C
  }.

  Context (xprog : C -> XComponent).

  (** A fiber's component: the base component and the optional keys
      present when it began loading. *)
  Definition C' : Type := (C * list K)%type.

  Local Notation Prog' := (@Prog K Σ C').
  Local Notation State := (@State K Σ C').
  Local Notation Fiber := (@Fiber K Σ C').
  Local Notation Label := (@Label C').
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation fparent := (Calculus.parent Σ).
  Local Notation disposed := (Calculus.disposed Σ).

  (** Spawned components start with no optional key chosen; [X-Begin]
      chooses. *)
  Fixpoint lift (P : @Prog K Σ C) : Prog' :=
    match P with
    | PDone => PDone
    | PFail => PFail
    | POp k a κ => POp k a (fun o => lift (κ o))
    | PProvide k s Q => PProvide k s (lift Q)
    | PSpawn c Q => PSpawn (c, []) (lift Q)
    end.

  (** Only declared optional keys count, so a pair [(c, S)] that no
      execution builds still has [c]'s dependencies. *)
  Definition prog' (x : C') : @Component K Σ C' :=
    let xc := xprog (fst x) in
    mkComponent (xdeps xc ++ filter (fun k => kmem K_eq_dec k (xopt xc)) (snd x)) (xprovs xc)
                (lift (xbody xc (fun k => kmem K_eq_dec k (snd x))))
                (map (fun c => (c, [])) (xreacts xc)).

  Local Notation step := (step K_eq_dec Σ prog').
  Local Notation target := (target Σ prog').
  Local Notation WF := (WF K_eq_dec Σ prog').

  (** ** Presence *)
  Definition is_visible (γ : State) (k : K) : bool :=
    match visible Σ γ k with Some _ => true | None => false end.

  (** The optional keys of [c] whose provider is Active, in declared order. *)
  Definition present (γ : State) (c : C) : list K := filter (is_visible γ) (xopt (xprog c)).

  (** The presence chosen when [f] began loading is still the presence now. *)
  Definition fresh (γ : State) (f : Fiber) : bool :=
    if list_eq_dec K_eq_dec (present γ (fst (fcomp f))) (snd (fcomp f)) then true else false.

  (** The extended target: ⊥ also when the presence has changed. *)
  Definition xtarget (γ : State) (n : nat) : option (@View K) :=
    match fibers γ n with
    | Some f => if fresh γ f then target γ n else None
    | None => None
    end.

  (** Re-choose the presence of fiber [n]. *)
  Definition recomp (γ : State) (n : nat) (f : Fiber) : State :=
    set_fiber Σ γ n (mkFiber Σ (fst (fcomp f), present γ (fst (fcomp f)))
                             (fparent f) (disposed f) (life f)).

  (** ** Rules *)

  (** Labels name base components; an inserted fiber starts with no
      optional key chosen. *)
  Definition xlab (ℓ : @Calculus.Label C) : Label :=
    match ℓ with
    | OInsert c => OInsert (c, [])
    | ODispose n => ODispose n
    | OReset n => OReset n
    | LBegin n => LBegin n
    | LStep n => LStep n
    | LDivert n => LDivert n
    | LLeave n => LLeave n
    | LUndo n => LUndo n
    | LRetireChild n => LRetireChild n
    | LUnloaded n => LUnloaded n
    | LRemove n => LRemove n
    | OReact n i => OReact n i
    | ORestart n => ORestart n
    end.

  (** - [X-Begin n]: an Inactive fiber chooses the present optional keys,
        then begins as in the core.
      - [X-Step n]: the core step, while the presence is unchanged.
      - [X-Divert n], [X-Leave n]: the core rule, or, when the presence has
        changed though the core target has not, the same move to Unloading.
      - every other label: the core rule. *)
  Definition xstep (γ : State) (ℓ : @Calculus.Label C) : option State :=
    match ℓ with
    | LBegin n =>
        match fibers γ n with
        | Some f =>
            match life f with
            | Inactive _ None => step (recomp γ n f) (LBegin n)
            | _ => None
            end
        | None => None
        end
    | LStep n =>
        match fibers γ n with
        | Some f => if fresh γ f then step γ (LStep n) else None
        | None => None
        end
    | LDivert n =>
        match fibers γ n with
        | Some f =>
            if fresh γ f then step γ (LDivert n)
            else match life f with
                 | Loading _ _ acc w => Some (set_life Σ γ n f (Unloading Σ acc w None))
                 | _ => None
                 end
        | None => None
        end
    | LLeave n =>
        match fibers γ n with
        | Some f =>
            if fresh γ f then step γ (LLeave n)
            else match life f with
                 | Active _ acc w => Some (set_life Σ γ n f (Unloading Σ acc w None))
                 | _ => None
                 end
        | None => None
        end
    | _ => step γ (xlab ℓ)
    end.

  Fixpoint xrun (γ : State) (ls : list (@Calculus.Label C)) : option State :=
    match ls with
    | [] => Some γ
    | ℓ :: ls' => match xstep γ ℓ with Some γ' => xrun γ' ls' | None => None end
    end.

  Definition XReachable (γ : State) : Prop := exists ls, xrun (@init K Σ C') ls = Some γ.

  (** ** Correspondence with the core *)

  Lemma target_disposed (γ : State) n f :
    fibers γ n = Some f -> disposed f = true -> target γ n = None.
  Proof. intros Hn Hd; unfold Calculus.target; rewrite Hn, Hd; reflexivity. Qed.

  (** Every extended step is a core step of [prog'], a core [L-Begin]
      after re-choosing presence, or a core [O-Restart]. *)
  Theorem xstep_core (γ γ' : State) ℓ :
    xstep γ ℓ = Some γ' ->
    step γ (xlab ℓ) = Some γ' \/
    (exists n f, ℓ = LBegin n /\ fibers γ n = Some f /\ life f = Inactive Σ None /\
                 step (recomp γ n f) (LBegin n) = Some γ') \/
    (exists n, step γ (ORestart n) = Some γ').
  Proof.
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [xstep xlab]; intros H;
      try (left; exact H).
    - (* LBegin *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate.
      right; left; exists n, f; auto.
    - (* LStep *)
      destruct (fibers γ n) as [f|]; [|discriminate].
      destruct (fresh γ f); [left; exact H | discriminate].
    - (* LDivert *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (fresh γ f); [left; exact H|].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      injection H as <-.
      destruct (disposed f) eqn:Hd.
      + left; cbn [Calculus.step]; rewrite Hn, Hl.
        unfold target_is; rewrite (target_disposed γ n f Hn Hd); reflexivity.
      + right; right; exists n; cbn [Calculus.step]; rewrite Hn, Hd, Hl; reflexivity.
    - (* LLeave *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (fresh γ f); [left; exact H|].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      injection H as <-.
      destruct (disposed f) eqn:Hd.
      + left; cbn [Calculus.step]; rewrite Hn, Hl.
        unfold target_is; rewrite (target_disposed γ n f Hn Hd); reflexivity.
      + right; right; exists n; cbn [Calculus.step]; rewrite Hn, Hd, Hl; reflexivity.
  Qed.

  (** Conversely, every core step at a fiber whose presence is unchanged
      is an extended step; [X-Begin] is the core [L-Begin] once the
      presence is re-chosen. *)
  Theorem xstep_fresh (γ : State) ℓ n f :
    fibers γ n = Some f -> fresh γ f = true ->
    (ℓ = LStep n \/ ℓ = LDivert n \/ ℓ = LLeave n) ->
    xstep γ ℓ = step γ (xlab ℓ).
  Proof.
    intros Hn Hf Hl; destruct Hl as [E|[E|E]]; subst ℓ; cbn [xstep xlab];
      rewrite Hn, Hf; reflexivity.
  Qed.

  (** Conservativity: when no component has an optional key, re-choosing
      presence changes nothing, and the extended step is the core step of
      [prog'] at every state whose fibers have chosen no optional key. *)
  Definition NoOpt : Prop := forall c, xopt (xprog c) = [].

  Definition Plain (γ : State) : Prop := forall n f, fibers γ n = Some f -> snd (fcomp f) = [].

  Lemma fresh_plain (γ : State) f : NoOpt -> snd (fcomp f) = [] -> fresh γ f = true.
  Proof.
    intros N E; unfold fresh, present; destruct f as [[c S] q d l]; cbn in *; subst S.
    rewrite N; cbn; reflexivity.
  Qed.

  Lemma recomp_plain (γ : State) n f :
    NoOpt -> fibers γ n = Some f -> snd (fcomp f) = [] -> recomp γ n f = γ.
  Proof.
    intros N Hn E; unfold recomp, present; rewrite N; cbn.
    destruct γ as [nx F B ol il]; cbn in *; unfold set_fiber, with_fibers; cbn.
    f_equal; apply functional_extensionality; intros m.
    unfold fupd; destruct (Nat.eqb_spec m n) as [->|]; [|reflexivity].
    rewrite Hn; destruct f as [[c S] q d l]; cbn in *; subst S; reflexivity.
  Qed.

  Theorem xstep_conservative (γ : State) ℓ :
    NoOpt -> Plain γ -> xstep γ ℓ = step γ (xlab ℓ).
  Proof.
    intros N Pl.
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [xstep xlab]; try reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn.
      + destruct (life f) as [[z|]| | |] eqn:Hl;
          try (cbn [Calculus.step]; rewrite Hn, Hl; reflexivity).
        rewrite (recomp_plain γ n f N Hn (Pl n f Hn)); reflexivity.
      + cbn [Calculus.step]; rewrite Hn; reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn.
      + rewrite (fresh_plain γ f N (Pl n f Hn)); reflexivity.
      + cbn [Calculus.step]; rewrite Hn; reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn.
      + rewrite (fresh_plain γ f N (Pl n f Hn)); reflexivity.
      + cbn [Calculus.step]; rewrite Hn; reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn.
      + rewrite (fresh_plain γ f N (Pl n f Hn)); reflexivity.
      + cbn [Calculus.step]; rewrite Hn; reflexivity.
  Qed.

  (** ** Safety: [WF] holds along every extended execution *)

  (** Re-choosing the presence of an Inactive fiber keeps [WF]: [WF] reads
      a fiber's dependencies only while it is installed, and its provided
      keys do not depend on the presence. *)
  Lemma wf_recomp (γ : State) n f :
    WF γ -> fibers γ n = Some f -> is_installed Σ (life f) = false -> WF (recomp γ n f).
  Proof.
    intros W Hn Hi.
    set (f' := mkFiber Σ (fst (fcomp f), present γ (fst (fcomp f))) (fparent f) (disposed f) (life f)).
    assert (Hf : forall m fm, fibers (recomp γ n f) m = Some fm ->
                 (m = n /\ fm = f') \/ (m <> n /\ fibers γ m = Some fm)).
    { intros m fm H; exact (fibers_set_fiber_inv Σ γ n f' m fm H). }
    assert (Hback : forall m fm, fibers (recomp γ n f) m = Some fm ->
                    exists fm0, fibers γ m = Some fm0 /\ life fm = life fm0 /\
                      fparent fm = fparent fm0 /\
                      fprovs Σ prog' fm = fprovs Σ prog' fm0 /\
                      (is_installed Σ (life fm0) = true -> fm = fm0)).
    { intros m fm H; destruct (Hf m fm H) as [[-> ->]|[_ H']].
      - exists f; split; [exact Hn|]; split; [reflexivity|]; split; [reflexivity|].
        split; [reflexivity|]; intros I; rewrite Hi in I; discriminate.
      - exists fm; split; [exact H'|]; split; [reflexivity|]; split; [reflexivity|].
        split; [reflexivity|]; intros _; reflexivity. }
    assert (Hfwd : forall m fm0, fibers γ m = Some fm0 -> is_installed Σ (life fm0) = true ->
                   fibers (recomp γ n f) m = Some fm0).
    { intros m fm0 H0 Hi0; unfold recomp, set_fiber; cbn; unfold fupd.
      destruct (Nat.eqb_spec m n) as [->|]; [congruence | exact H0]. }
    destruct W as [Wn Wp Ws Wpar Wd Wv Wk Wb Wu Wuu]; split; cbn [Calculus.next Calculus.binds recomp set_fiber with_fibers] in *.
    - intros m fm H; destruct (Hback m fm H) as (fm0 & H0 & _); eauto.
    - exact Wp.
    - intros m fm m' H I; destruct (Hback m fm H) as (fm0 & H0 & El & _); rewrite El in I; eauto.
    - intros m fm q H Hq; destruct (Hback m fm H) as (fm0 & H0 & _ & Ep & _); rewrite Ep in Hq.
      destruct (Wpar m fm0 q H0 Hq) as (fq & Hq0 & Iq & Uq).
      exists fq; split; [exact (Hfwd q fq Hq0 Iq) | auto].
    - intros m m' fm fm' Hne H H'.
      destruct (Hback m fm H) as (fm0 & H0 & _ & _ & Ep & _).
      destruct (Hback m' fm' H') as (fm0' & H0' & _ & _ & Ep' & _).
      rewrite Ep, Ep'; eauto.
    - intros m fm k p H I; destruct (Hback m fm H) as (fm0 & H0 & El & _); rewrite El in I; eauto.
    - intros m fm H I; destruct (Hback m fm H) as (fm0 & H0 & El & _ & _ & Eq).
      rewrite El in I; rewrite (Eq I); eauto.
    - intros k b Hb; destruct (Wb k b Hb) as (fo & Ho & Io & Ko & Uo).
      exists fo; repeat split; auto.
    - intros m fm k p H I; destruct (Hback m fm H) as (fm0 & H0 & El & _); rewrite El in I; eauto.
    - intros m fm H; destruct (Hback m fm H) as (fm0 & H0 & El & _).
      pose proof (Wuu m fm0 H0) as U; rewrite El; exact U.
  Qed.

  Theorem xpreservation (γ γ' : State) ℓ : WF γ -> xstep γ ℓ = Some γ' -> WF γ'.
  Proof.
    intros W H.
    destruct (xstep_core γ γ' ℓ H) as [S|[(n & f & _ & Hn & Hl & S)|(n & S)]].
    - exact (preservation K_eq_dec Σ prog' γ γ' _ W S).
    - apply (preservation K_eq_dec Σ prog' (recomp γ n f) γ' (LBegin n)); [|exact S].
      apply wf_recomp; auto; rewrite Hl; reflexivity.
    - exact (preservation K_eq_dec Σ prog' γ γ' _ W S).
  Qed.

  (** Tier 0 of the summary theorem, for the extension: every extended
      execution stays well formed, so the core ordering theorems
      ([Ordering.provider_outlives], [withdraw_waits], [unload_waits], ...) hold at every
      state it reaches. *)
  Theorem xwf_reachable (γ : State) : XReachable γ -> WF γ.
  Proof.
    intros [ls H].
    assert (G : forall γ0, WF γ0 -> xrun γ0 ls = Some γ -> WF γ).
    { clear H; induction ls as [|ℓ ls IH]; cbn; intros γ0 W0 H0.
      - injection H0 as <-; exact W0.
      - destruct (xstep γ0 ℓ) as [γ1|] eqn:Hs; [|discriminate].
        exact (IH γ1 (xpreservation γ0 γ1 ℓ W0 Hs) H0). }
    exact (G _ (wf_init K_eq_dec Σ prog') H).
  Qed.
End Optional.
