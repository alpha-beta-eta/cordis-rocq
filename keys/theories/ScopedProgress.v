(** * Hygienic keys: no deadlock

    Counterpart of [Progress.quiet_settled]: at an extended state where no
    extended lifecycle rule applies, every fiber is settled
    ([kquiet_settled]):
    - an Inactive fiber with an error is not disposed;
    - an Inactive fiber without one is not disposed and would get no target
      by choosing its selection ([bt = None]); the reason is an exported
      dependency without a unique candidate (none, or a tie, reported by
      [tied]) or a dependency key that is not visible ([bt_none_reason]);
    - an Active fiber's target is its view and its selection is current;
    - no fiber is Loading or Unloading.

    The core theorem cannot be applied through a table as in
    [Ext/OptProgress.v]: X-Begin may be blocked where the core [L-Begin]
    would fire (a stale selection still resolves), so the extended state
    need not be quiet in the core sense. The proof follows the core's
    instead, with the induction along ranks ([KAbove]).

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia Wf_nat.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Recovery Progress.
From CordisKeys Require Import Scoped ScopedSafety ScopedTerm.
Import ListNotations.

Section ScopedProgress.
  Context {N : Type} (N_eq_dec : forall x y : N, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (C_eq_dec : forall x y : C, {x = y} + {x <> y}).
  Context (xprog : C -> @XComponent N Σ C).

  Local Notation XC := (@XC N C).
  Local Notation Key := (@Key N).
  Local Notation State := (@State Key Σ XC).
  Local Notation Fiber := (@Fiber Key Σ XC).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation disposed := (Calculus.disposed Σ).
  Local Notation fparent := (Calculus.parent Σ).
  Local Notation kdec := (key_eq_dec N_eq_dec).
  Local Notation prog' := (prog' N_eq_dec Σ xprog).
  Local Notation step := (step kdec Σ prog').
  Local Notation kstep := (kstep N_eq_dec Σ xprog).
  Local Notation recomp := (recomp N_eq_dec Σ xprog).
  Local Notation fresh := (fresh N_eq_dec Σ xprog).
  Local Notation select := (select N_eq_dec Σ xprog).
  Local Notation all_selected := (all_selected N_eq_dec Σ xprog).
  Local Notation choose := (choose N_eq_dec Σ xprog).
  Local Notation globals := (globals Σ xprog).
  Local Notation target := (target Σ prog').
  Local Notation bt := (bt N_eq_dec Σ xprog).
  Local Notation rcomp := (rcomp N_eq_dec Σ xprog).
  Local Notation KInv := (KInv N_eq_dec Σ xprog).

  Variable xrank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', KAbove Σ xprog c c' -> xrank c < xrank c'.
  Hypothesis Hbnd : forall c, xrank c <= Rb.
  (** A parent declares every exported name its children depend on. *)
  Hypothesis kSub : forall c c', KSpawns Σ xprog c c' -> forall y, In y (globals c') -> In y (globals c).

  Local Notation frank f := (xrank (base (fcomp f))).

  Definition kquiet (γ : State) : Prop :=
    forall n ℓ, In ℓ (@lifecycle_labels C n) -> kstep γ ℓ = None.

  Definition ksettled_fiber (γ : State) n (f : Fiber) : Prop :=
    match life f with
    | Inactive _ (Some _) => disposed f = false
    | Inactive _ None => disposed f = false /\ bt γ n = None
    | Active _ _ w => target γ n = Some w /\ fresh γ f = true
    | _ => False
    end.

  Definition ksettled (γ : State) : Prop :=
    forall n f, fibers γ n = Some f -> ksettled_fiber γ n f.

  (** A child of a fiber whose selection is current has a current
      selection too: it inherited it, and its parent declares all its
      exported names. *)
  Lemma child_fresh (γ : State) m fm q fq :
    KInv γ -> fibers γ m = Some fm -> fparent fm = Some q -> fibers γ q = Some fq -> fresh γ fq = true ->
    fresh γ fm = true.
  Proof.
    intros [W _ _ X S0] Hm Hp Hq Fq.
    destruct (wf_parent kdec Σ prog' γ W m fm q Hm Hp) as (fq0 & Hq0 & _ & Hu).
    rewrite Hq in Hq0; injection Hq0 as <-.
    pose proof (X q fq m fm Hq Hu Hm) as Ks.
    pose proof (si_child _ _ _ _ S0 m fm q fq Hm Hp Hq) as Ei.
    unfold Scoped.fresh in Fq |- *; apply andb_true_iff in Fq as [Aq Eq].
    destruct (list_eq_dec (ns_eq_dec N_eq_dec) (sel (fcomp fq)) (choose γ (base (fcomp fq)))) as [Eq'|];
      [|discriminate].
    assert (Hsel : forall y, In y (globals (base (fcomp fm))) -> In y (globals (base (fcomp fq))))
      by (intros y; apply kSub; exact Ks).
    apply andb_true_iff; split.
    - unfold Scoped.all_selected in Aq |- *; rewrite forallb_forall in Aq |- *.
      intros y Hy; apply Aq, Hsel, Hy.
    - assert (E : sel (fcomp fm) = choose γ (base (fcomp fm))).
      { rewrite Ei; unfold Scoped.inherit; unfold Scoped.choose; apply map_ext_in; intros y Hy.
        unfold Scoped.assoc_or; rewrite Eq'; unfold Scoped.choose.
        rewrite (assoc_map N_eq_dec _ _ y (Hsel y Hy)); reflexivity. }
      destruct (list_eq_dec _ _ _) as [_|Q']; [reflexivity | contradiction].
  Qed.

  (** ** Stuck extended states are settled *)
  Theorem kquiet_settled (γ : State) : KInv γ -> kquiet γ -> ksettled γ.
  Proof.
    intros KI Q; pose proof KI as [W _ PU SP _].
    assert (NoLoad : forall m fm P acc w, fibers γ m = Some fm ->
              life fm = Loading Σ P acc w -> False).
    { intros m fm P acc w Hm Hl.
      pose proof (Q m (LStep m) ltac:(cbn; tauto)) as E1.
      pose proof (Q m (LDivert m) ltac:(cbn; tauto)) as E2.
      cbn [Scoped.kstep] in E1, E2; rewrite Hm in E1, E2.
      destruct (fresh γ fm).
      - cbn [Calculus.step] in E1, E2; rewrite Hm, Hl in E1, E2.
        destruct P; cbn [may_step] in E1; try discriminate;
          destruct (target_is kdec Σ prog' γ m w); discriminate.
      - rewrite Hl in E2; discriminate. }
    assert (NoLeave : forall m fm acc w, fibers γ m = Some fm ->
              life fm = Active Σ acc w -> target γ m = Some w /\ fresh γ fm = true).
    { intros m fm acc w Hm Hl.
      pose proof (Q m (LLeave m) ltac:(cbn; tauto)) as E.
      cbn [Scoped.kstep] in E; rewrite Hm in E.
      destruct (fresh γ fm) eqn:F; [|rewrite Hl in E; discriminate].
      cbn [Calculus.step] in E; rewrite Hm, Hl in E.
      destruct (target_is kdec Σ prog' γ m w) eqn:Et; [|discriminate].
      apply (target_is_spec kdec Σ prog') in Et; auto. }
    assert (Hlc : forall n ℓ, In ℓ (@lifecycle_labels C n) -> In ℓ (@lifecycle_labels C n)) by auto.
    assert (QU : forall n, step γ (LUndo n) = None /\ step γ (LRetireChild n) = None /\
                           step γ (LUnloaded n) = None /\ step γ (LRemove n) = None).
    { intros n; repeat split;
        [exact (Q n (LUndo n) ltac:(cbn; tauto)) | exact (Q n (LRetireChild n) ltac:(cbn; tauto))
        | exact (Q n (LUnloaded n) ltac:(cbn; tauto)) | exact (Q n (LRemove n) ltac:(cbn; tauto))]. }
    (* No fiber is Unloading, by induction along ranks (downwards from [Rb]). *)
    assert (NoU : forall d n f, Rb - frank f = d -> fibers γ n = Some f ->
              forall acc w z, life f <> Unloading Σ acc w z).
    { intros d; induction d as [d IH] using (well_founded_induction lt_wf).
      intros n f Ed Hn acc w z Hl.
      destruct acc as [|u acc].
      { pose proof (proj1 (proj2 (proj2 (QU n)))) as E.
        cbn [Calculus.step] in E; rewrite Hn, Hl in E; discriminate. }
      pose proof (proj1 (QU n)) as E.
      cbn [Calculus.step] in E; rewrite Hn, Hl in E.
      assert (Blocked : forall m fm, fibers γ m = Some fm -> frank f < frank fm ->
                target γ m = None -> is_installed Σ (life fm) = true -> False).
      { intros m fm Hm HA Ht Hi.
        destruct (life fm) as [z'|P acc' w'|acc' w'|acc' w' z'] eqn:Hlm.
        - discriminate.
        - exact (NoLoad m fm P acc' w' Hm Hlm).
        - destruct (NoLeave m fm acc' w' Hm Hlm) as [Ht' _]; congruence.
        - pose proof (Hbnd (base (fcomp fm))).
          exact (IH (Rb - frank fm) ltac:(lia) m fm eq_refl Hm acc' w' z' Hlm). }
      assert (NoRelied : forall k p, In (UProv Σ k p) (u :: acc) ->
                relied Σ γ n p = true -> False).
      { intros k p Hu0 Hr.
        unfold relied in Hr; apply existsb_exists in Hr as (m & _ & Hm).
        apply andb_true_iff in Hm as [Hmn Hres].
        apply negb_true_iff, Nat.eqb_neq in Hmn.
        unfold resolves in Hres.
        destruct (fibers γ m) as [fm|] eqn:Hfm; [|discriminate].
        apply andb_true_iff in Hres as [Hinst Hex].
        apply existsb_exists in Hex as ([k' p'] & Hin' & Hp'); cbn in Hp'.
        apply Nat.eqb_eq in Hp'; subst p'.
        assert (Hu : In (UProv Σ k p) (acc_of Σ (life f))) by (rewrite Hl; exact Hu0).
        destruct (wf_uprov kdec Σ prog' γ W n f k p Hn Hu) as (b0 & Hb0 & Hpb0 & Hob0).
        destruct (wf_view kdec Σ prog' γ W m fm k' p Hfm Hin') as (b1 & Hb1 & Hpb1 & _).
        assert (Hkk : k' = k) by (apply (PU k' k b1 b0 Hb1 Hb0); congruence).
        subst k'.
        assert (Hkd : In k (deps Σ (prog' (fcomp fm)))).
        { pose proof (wf_view_keys kdec Σ prog' γ W m fm Hfm Hinst) as Hk.
          unfold fdeps in Hk; rewrite <- Hk; apply in_map_iff; exists (k, p); auto. }
        apply (Blocked m fm Hfm); [| |exact Hinst].
        + apply Hrank; left; exists (snd k); split; [|exact (deps_keyof N_eq_dec Σ xprog _ k Hkd)].
          destruct (wf_bind kdec Σ prog' γ W k b0 Hb0) as (fo & Ho & _ & Hko & _).
          rewrite Hob0, Hn in Ho; injection Ho as <-.
          exact (provs_name N_eq_dec Σ xprog _ k Hko).
        + apply (target_none Σ prog' γ m fm k Hfm Hkd).
          unfold visible; rewrite Hb0, Hob0, Hn, Hl; reflexivity. }
      assert (Hh : held Σ γ n (u :: acc) = false).
      { destruct (held Σ γ n (u :: acc)) eqn:Hh; [|reflexivity].
        exfalso; unfold held in Hh; apply existsb_exists in Hh as (u' & Hin & Hu').
        destruct u' as [k p t g|k p|m]; try discriminate.
        exact (NoRelied k p Hin Hu'). }
      rewrite Hh in E.
      destruct u as [k p t g|k p|m]; cbn [undo_step] in E.
      - destruct (binds γ k) as [b|]; [destruct (Nat.eqb (pid Σ b) p)|]; discriminate.
      - destruct (relied Σ γ n p) eqn:Hr.
        + exact (NoRelied k p (or_introl eq_refl) Hr).
        + destruct (binds γ k) as [b|]; [destruct (Nat.eqb (pid Σ b) p)|]; discriminate.
      - destruct (fibers γ m) as [fm|] eqn:Hfm; [|discriminate].
        pose proof (proj1 (proj2 (QU n))) as E4.
        cbn [Calculus.step] in E4; rewrite Hn, Hl, Hfm, Hh in E4; cbn [orb] in E4.
        destruct (disposed fm) eqn:Hd; [|discriminate].
        assert (HA : frank f < frank fm).
        { apply Hrank; right.
          apply (SP n f m fm Hn); [rewrite Hl; left; reflexivity | exact Hfm]. }
        destruct (is_installed Σ (life fm)) eqn:Hi.
        + apply (Blocked m fm Hfm HA); [|exact Hi].
          unfold Calculus.target; rewrite Hfm, Hd; reflexivity.
        + destruct (life fm) as [z'| | |] eqn:Hlm; try discriminate.
          pose proof (proj2 (proj2 (proj2 (QU m)))) as E5.
          cbn [Calculus.step] in E5; rewrite Hfm, Hlm, Hd in E5.
          rewrite (has_child_inactive kdec Σ prog' γ m fm W Hfm) in E5 by (rewrite Hlm; reflexivity).
          discriminate. }
    intros n f Hn; unfold ksettled_fiber.
    assert (Hdisp : (exists z, life f = Inactive Σ z) -> disposed f = false).
    { intros [z Hl]; destruct (disposed f) eqn:Hd; [|reflexivity].
      pose proof (proj2 (proj2 (proj2 (QU n)))) as E.
      cbn [Calculus.step] in E; rewrite Hn, Hl, Hd in E.
      rewrite (has_child_inactive kdec Σ prog' γ n f W Hn) in E by (rewrite Hl; reflexivity).
      discriminate. }
    destruct (life f) as [[e|]|P acc w|acc w|acc w z] eqn:Hl.
    - exact (Hdisp (ex_intro _ _ eq_refl)).
    - split; [exact (Hdisp (ex_intro _ _ eq_refl))|].
      pose proof (Q n (LBegin n) ltac:(cbn; tauto)) as E.
      cbn [Scoped.kstep] in E; rewrite Hn, Hl in E.
      destruct (fparent f) as [q|] eqn:Hp.
      { (* a child: its parent is Active and current, so it is current too *)
        destruct (wf_parent kdec Σ prog' γ W n f q Hn Hp) as (fq & Hq & Iq & _).
        assert (Fq : fresh γ fq = true).
        { destruct (life fq) as [zq|Pq accq wq|accq wq|accq wq zq] eqn:Lq; try discriminate Iq.
          - exfalso; exact (NoLoad q fq Pq accq wq Hq Lq).
          - exact (proj2 (NoLeave q fq accq wq Hq Lq)).
          - exfalso; exact (NoU _ q fq eq_refl Hq accq wq zq Lq). }
        pose proof (child_fresh γ n f q fq KI Hn Hp Hq Fq) as Ff.
        rewrite Ff in E; cbn [Calculus.step] in E; rewrite Hn, Hl in E.
        rewrite (bt_fresh N_eq_dec Σ xprog γ n f Hn Ff).
        destruct (target γ n); [discriminate | reflexivity]. }
      destruct (all_selected γ (base (fcomp f))) eqn:A.
      + rewrite <- (bt_recomp N_eq_dec Σ xprog γ n f Hn A).
        cbn [Calculus.step] in E.
        unfold Scoped.recomp in E at 1; rewrite fibers_refiber, Nat.eqb_refl in E.
        cbn [Calculus.life] in E; rewrite Hl in E.
        destruct (target (recomp γ n f) n); [discriminate | reflexivity].
      + unfold ScopedTerm.bt; rewrite Hn, A; destruct (disposed f); reflexivity.
    - exfalso; exact (NoLoad n f P acc w Hn Hl).
    - exact (NoLeave n f acc w Hn Hl).
    - exact (NoU _ n f eq_refl Hn acc w z Hl).
  Qed.

  (** ** Why an Inactive fiber gets no target *)

  Lemma top_attained (cs : list (Scope * nat)) :
    cs <> [] -> exists c, In c cs /\ snd c = fold_right (fun c m => Nat.max (snd c) m) 0 cs.
  Proof.
    induction cs as [|c cs IH]; [contradiction|]; intros _; cbn.
    destruct cs as [|c' cs'].
    - exists c; split; [left; reflexivity | cbn; lia].
    - destruct (IH ltac:(discriminate)) as (c0 & Hin & E).
      destruct (Nat.le_ge_cases (snd c) (fold_right (fun c m => Nat.max (snd c) m) 0 (c' :: cs'))).
      + exists c0; split; [right; exact Hin | lia].
      + exists c; split; [left; reflexivity | lia].
  Qed.

  (** An exported name is unresolved because it has no candidate, or
      because the highest priority is tied. *)
  Lemma select_none (γ : State) y :
    select γ y = None -> candidates N_eq_dec Σ xprog γ y = [] \/ tied N_eq_dec Σ xprog γ y = true.
  Proof.
    unfold Scoped.select, Scoped.tied; intros E.
    remember (candidates N_eq_dec Σ xprog γ y) as cs eqn:Hcs; clear Hcs.
    destruct cs as [|c0 cs0]; [left; reflexivity|right].
    destruct (top_attained (c0 :: cs0) ltac:(discriminate)) as (c & Hin & Ec).
    assert (Hf : In c (filter (fun c => Nat.eqb (snd c) (fold_right (fun c m => Nat.max (snd c) m) 0 (c0 :: cs0))) (c0 :: cs0)))
      by (apply filter_In; split; [exact Hin | apply Nat.eqb_eq; exact Ec]).
    destruct (filter (fun c => Nat.eqb (snd c) (fold_right (fun c m => Nat.max (snd c) m) 0 (c0 :: cs0))) (c0 :: cs0))
      as [|[s p] [|c2 l]].
    - destruct Hf.
    - discriminate E.
    - cbn; reflexivity.
  Qed.

  Lemma resolve_none_ex (γ : State) ks :
    resolve Σ γ ks = None -> exists k, In k ks /\ visible Σ γ k = None.
  Proof.
    induction ks as [|k ks IH]; cbn; [discriminate|].
    destruct (visible Σ γ k) eqn:Hv; [|intros _; exists k; auto].
    destruct (resolve Σ γ ks); [discriminate|].
    intros _; destruct (IH eq_refl) as (k' & ? & ?); exists k'; auto.
  Qed.

  (** A settled Inactive fiber waits because an exported dependency has no
      candidate or is tied, or because a dependency key is not visible. *)
  Theorem bt_none_reason (γ : State) n f :
    fibers γ n = Some f -> disposed f = false -> bt γ n = None ->
    (exists y, In y (globals (base (fcomp f))) /\
       (candidates N_eq_dec Σ xprog γ y = [] \/ tied N_eq_dec Σ xprog γ y = true)) \/
    (exists k, In k (deps Σ (prog' (rcomp γ (fcomp f)))) /\ visible Σ γ k = None).
  Proof.
    intros Hn Hd; unfold ScopedTerm.bt; rewrite Hn, Hd.
    destruct (all_selected γ (base (fcomp f))) eqn:A.
    - intros E; right; exact (resolve_none_ex γ _ E).
    - intros _; left.
      unfold Scoped.all_selected in A.
      apply Bool.not_true_iff_false in A.
      destruct (existsb (fun y => negb (Scoped.selected N_eq_dec Σ xprog γ y)) (globals (base (fcomp f)))) eqn:Ex.
      + apply existsb_exists in Ex as (y & Hy & Ey).
        exists y; split; [exact Hy|]; apply select_none.
        unfold Scoped.selected in Ey; destruct (select γ y); [discriminate | reflexivity].
      + exfalso; apply A; apply forallb_forall; intros y Hy.
        destruct (Scoped.selected N_eq_dec Σ xprog γ y) eqn:Es; [reflexivity|].
        assert (existsb (fun y => negb (Scoped.selected N_eq_dec Σ xprog γ y)) (globals (base (fcomp f))) = true)
          by (apply existsb_exists; exists y; rewrite Es; auto).
        congruence.
  Qed.

  (** ** Along extended executions *)
  Lemma kinv_step (γ γ' : State) ℓ : KInv γ -> kstep γ ℓ = Some γ' -> KInv γ'.
  Proof.
    intros I H.
    pose proof (si_kstep N_eq_dec Σ xprog γ γ' ℓ (ki_wf _ _ _ _ I) (ki_si _ _ _ _ I) H) as S'.
    assert (Core : forall γ0, KInv γ0 -> forall ℓ0, step γ0 ℓ0 = Some γ' -> KInv γ').
    { intros γ0 I0 ℓ0 St; destruct (kinv_core4 N_eq_dec Σ C_eq_dec xprog γ0 γ' ℓ0 I0 St) as (W' & P' & U' & X').
      split; auto. }
    destruct (kstep_core N_eq_dec Σ xprog γ γ' ℓ H)
      as [St|[(m & f & _ & Hm & Hl & _ & Hp & St)|[(m & St)|(m & i & f & _ & Hm & St)]]].
    - exact (Core γ I _ St).
    - exact (Core _ (kinv_recomp N_eq_dec Σ xprog γ m f I Hm Hl Hp) _ St).
    - exact (Core γ I _ St).
    - destruct (life f) as [| |acc w|] eqn:Hl;
        try (cbn [Calculus.step] in St; unfold Scoped.retick in St; rewrite fibers_refiber, Nat.eqb_refl in St;
             cbn [Calculus.life] in St; rewrite Hl in St; discriminate St).
      exact (Core _ (kinv_retick N_eq_dec Σ xprog γ m f acc w I Hm Hl) _ St).
  Qed.

  Theorem kinv_reachable (γ : State) : KReachable N_eq_dec Σ xprog γ -> KInv γ.
  Proof.
    intros [ls H].
    assert (G : forall γ0, KInv γ0 -> krun N_eq_dec Σ xprog γ0 ls = Some γ -> KInv γ).
    { clear H; induction ls as [|ℓ ls IH]; cbn; intros γ0 I0 H0.
      - injection H0 as <-; exact I0.
      - destruct (kstep γ0 ℓ) as [γ1|] eqn:Hs; [|discriminate].
        exact (IH γ1 (kinv_step γ0 γ1 ℓ I0 Hs) H0). }
    exact (G _ (kinv_init N_eq_dec Σ xprog) H).
  Qed.

  Corollary kquiet_settled_reachable (γ : State) :
    KReachable N_eq_dec Σ xprog γ -> kquiet γ -> ksettled γ.
  Proof. intros R; exact (kquiet_settled γ (kinv_reachable γ R)). Qed.
End ScopedProgress.
