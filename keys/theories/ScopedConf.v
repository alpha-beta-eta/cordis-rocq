(** * Hygienic keys: confluence of control states

    Counterpart of [Confluence.control_confluence] (components that spawn
    nothing). From a common state, two extended executions of lifecycle
    steps that end quiet with no fiber failed leave
    - the same fibers present, with the same base components, scopes and
      private environments;
    - the same of them Active;
    - every key bound by the same fiber;
    - the same candidates for every exported name, in the same order, so
      the same resolution and the same ties ([select], [tied]);
    - every Active fiber with the same selection.

    The proof follows [Ext/OptConfluence.v] for the invariant and the
    domain, and replaces the fixpoint equation: at a quiet state with no
    failure a fiber is Active iff choosing its selection would give it a
    target ([act_bt], from [ScopedProgress.kquiet_settled]). That target
    reads only the visibility of keys named by the fiber's dependencies,
    whose providers have lower rank, and the candidates for its exported
    dependencies, which have lower rank too. So activity agrees between the
    two final states by induction on the rank, and then everything else
    follows.

    The core analysis of settled states ([Confluence.active_iff],
    [owner_iff]) does not apply as it stands: at a quiet extended state an
    Inactive fiber may still resolve its stale selection, so the state need
    not be settled in the core sense. Only [active_binds] is reused.

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia Wf_nat.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Recovery
  Progress Termination Confluence.
From CordisKeys Require Import Scoped ScopedSafety ScopedTerm ScopedProgress.
Import ListNotations.

Section ScopedConf.
  Context {N : Type} (N_eq_dec : forall x y : N, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (xprog : C -> @XComponent N Σ C).

  Local Notation XC := (@XC N C).
  Local Notation Key := (@Key N).
  Local Notation State := (@State Key Σ XC).
  Local Notation Fiber := (@Fiber Key Σ XC).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation disposed := (Calculus.disposed Σ).
  Local Notation is_active := (is_active Σ).
  Local Notation owner := (owner Σ).
  Local Notation kdec := (key_eq_dec N_eq_dec).
  Local Notation prog' := (prog' N_eq_dec Σ xprog).
  Local Notation lift := (lift N_eq_dec Σ xprog).
  Local Notation step := (step kdec Σ prog').
  Local Notation kstep := (kstep N_eq_dec Σ xprog).
  Local Notation recomp := (recomp N_eq_dec Σ xprog).
  Local Notation fresh := (fresh N_eq_dec Σ xprog).
  Local Notation select := (select N_eq_dec Σ xprog).
  Local Notation candidate := (candidate N_eq_dec Σ xprog).
  Local Notation candidates := (candidates N_eq_dec Σ xprog).
  Local Notation choose := (choose N_eq_dec Σ xprog).
  Local Notation all_selected := (all_selected N_eq_dec Σ xprog).
  Local Notation globals := (globals Σ xprog).
  Local Notation target := (target Σ prog').
  Local Notation bt := (bt N_eq_dec Σ xprog).
  Local Notation rcomp := (rcomp N_eq_dec Σ xprog).
  Local Notation KInv := (KInv N_eq_dec Σ xprog).
  Local Notation SI := (SI N_eq_dec Σ xprog).
  Local Notation WF := (WF kdec Σ prog').
  Local Notation kquiet := (kquiet N_eq_dec Σ xprog).
  Local Notation ksettled := (ksettled N_eq_dec Σ xprog).
  Local Notation xdeps c := (xdeps Σ (xprog c)).
  Local Notation xprovs c := (xprovs Σ xprog c).
  Local Notation dnames c := (map dname (xdeps c)).

  (** ** Hypotheses, on base components *)
  Variable Kb : nat.
  Hypothesis kHK : forall c, Termination.Bounded Σ Kb (xbody Σ (xprog c)).
  Variable xrank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', KAbove Σ xprog c c' -> xrank c < xrank c'.
  Hypothesis Hbnd : forall c, xrank c <= Rb.
  Hypothesis kNoSpawn : forall c c', ~ SpawnIn Σ c' (xbody Σ (xprog c)).
  (** Every path to [Done] provides every name the component may provide. *)
  Hypothesis kTotal : forall c y, In y (xprovs c) -> AllDoneProv Σ y (xbody Σ (xprog c)).
  (** A parent declares every exported name its children depend on. *)
  Hypothesis kSub : forall c c', KSpawns Σ xprog c c' -> forall y, In y (globals c') -> In y (globals c).

  Local Notation frank f := (xrank (base (fcomp f))).

  (** ** The core hypotheses for [prog'] *)
  Lemma adp_lift (x : XC) j y (P : @Prog N Σ C) :
    AllDoneProv Σ y P -> AllDoneProv Σ (scope x, y) (lift x j P).
  Proof.
    intros H; revert j; induction H; intros j; cbn [Scoped.lift]; constructor; auto.
  Qed.

  Lemma HK' : forall x, Termination.Bounded Σ Kb (body Σ (prog' x)).
  Proof. intros x; cbn [Scoped.prog' body]; apply bounded_lift, kHK. Qed.

  Lemma NoSpawn' : forall x y, ~ SpawnIn Σ y (body Σ (prog' x)).
  Proof.
    intros x y H; cbn [Scoped.prog' body] in H.
    exact (kNoSpawn _ _ (spawnin_lift N_eq_dec Σ xprog _ _ _ _ H)).
  Qed.

  Lemma Total' : forall x k, In k (provs Σ (prog' x)) -> AllDoneProv Σ k (body Σ (prog' x)).
  Proof.
    intros x k Hk; cbn [Scoped.prog' provs body] in *.
    apply in_map_iff in Hk as (y & <- & Hy); apply adp_lift, kTotal; exact Hy.
  Qed.

  Lemma Hrank' : forall x y, Above Σ prog' x y -> xrank (base x) < xrank (base y).
  Proof.
    intros x y [(k & Hp & Hd)|[Hs|Hr]]; apply Hrank.
    - left; exists (snd k); split.
      + cbn [Scoped.prog' provs] in Hp; apply in_map_iff in Hp as (y0 & <- & Hy0); exact Hy0.
      + exact (deps_keyof N_eq_dec Σ xprog _ k Hd).
    - exfalso; exact (NoSpawn' x y Hs).
    - right; right; cbn [Scoped.prog' reacts] in Hr; exact (handlers_in N_eq_dec Σ xprog _ _ _ _ Hr).
  Qed.

  Local Notation CInv := (CInv kdec Σ prog' Kb).
  Local Notation cinv_step := (cinv_step kdec Σ prog' Kb HK' NoSpawn' Total').
  Local Notation lstep_static :=
    (lstep_static kdec Σ prog' Kb (fun x => xrank (base x)) Hrank' NoSpawn').

  Definition KCInv (γ : State) : Prop := CInv γ /\ SI γ.

  Lemma kinv_of (γ : State) : KCInv γ -> KInv γ.
  Proof.
    intros [[[W P [U _] _ _] _ NS] S]; split; [exact W | exact P | exact U | | exact S].
    intros x fx m fm Hx Hu; destruct (NS x fx m Hx Hu).
  Qed.

  Lemma fibers_recomp (γ : State) n f m :
    fibers (recomp γ n f) m =
    if Nat.eqb m n then Some (mkFiber Σ (rcomp γ (fcomp f)) (Calculus.parent Σ f) (disposed f) (life f))
    else fibers γ m.
  Proof. reflexivity. Qed.

  (** ** Choosing a selection keeps [CInv] *)
  Lemma cinv_recomp (γ : State) n f :
    KCInv γ -> fibers γ n = Some f -> life f = Inactive Σ None -> Calculus.parent Σ f = None -> CInv (recomp γ n f).
  Proof.
    intros KI Hn Hl Hp.
    pose proof (kinv_of γ KI) as KI'.
    destruct KI as [[[W P [U Sp] LB SO] PI NS] S].
    destruct (kinv_recomp N_eq_dec Σ xprog γ n f KI' Hn Hl Hp) as [W' P' U' _ _].
    assert (Hb : forall m fm, fibers (recomp γ n f) m = Some fm ->
                 (m = n /\ life fm = Inactive Σ None) \/ (m <> n /\ fibers γ m = Some fm)).
    { intros m fm H; rewrite fibers_recomp in H.
      destruct (Nat.eqb_spec m n) as [->|Hne]; [injection H as <-; left; auto|right; auto]. }
    assert (Hacc : forall m fm, fibers (recomp γ n f) m = Some fm ->
                   exists fm0, fibers γ m = Some fm0 /\ life fm = life fm0 /\
                               Calculus.parent Σ fm = Calculus.parent Σ fm0).
    { intros m fm H; rewrite fibers_recomp in H.
      destruct (Nat.eqb_spec m n) as [->|]; [injection H as <-; exists f; auto|eauto]. }
    split; [split|..].
    - exact W'.
    - exact P'.
    - split; [exact U'|].
      intros x fx m fm Hx Hu; destruct (Hacc x fx Hx) as (fx0 & Hx0 & E & _).
      rewrite E in Hu; destruct (NS x fx0 m Hx0 Hu).
    - intros m fm P0 acc w Hm Hlm; destruct (Hb m fm Hm) as [[_ E]|[_ Hm0]].
      + rewrite E in Hlm; discriminate.
      + exact (LB m fm P0 acc w Hm0 Hlm).
    - intros x fx m fm Hx Hu; destruct (Hacc x fx Hx) as (fx0 & Hx0 & E & _).
      rewrite E in Hu; destruct (NS x fx0 m Hx0 Hu).
    - intros m fm Hm; destruct (Hb m fm Hm) as [[_ E]|[_ Hm0]].
      + unfold PIF; rewrite E; exact I.
      + exact (PI m fm Hm0).
    - intros x fx m Hx Hu; destruct (Hacc x fx Hx) as (fx0 & Hx0 & E & _).
      rewrite E in Hu; exact (NS x fx0 m Hx0 Hu).
  Qed.

  (** ** Fibers, base components, scopes and environments stay put *)
  Definition KStatic (γ0 γ : State) : Prop :=
    (forall m fm, fibers γ m = Some fm ->
       exists f0, fibers γ0 m = Some f0 /\ base (fcomp fm) = base (fcomp f0) /\
                  scope (fcomp fm) = scope (fcomp f0) /\ env (fcomp fm) = env (fcomp f0) /\
                  disposed fm = disposed f0) /\
    (forall m f0, fibers γ0 m = Some f0 -> disposed f0 = false -> exists fm, fibers γ m = Some fm).

  Lemma kstatic_refl (γ : State) : KStatic γ γ.
  Proof. split; [intros m fm H; exists fm; auto | intros m f0 H _; eauto]. Qed.

  Lemma kstatic_trans (γ0 γ1 γ2 : State) : KStatic γ0 γ1 -> KStatic γ1 γ2 -> KStatic γ0 γ2.
  Proof.
    intros [S1 S2] [T1 T2]; split.
    - intros m fm H; destruct (T1 m fm H) as (f1 & H1 & Hb1 & Hs1 & He1 & Hd1).
      destruct (S1 m f1 H1) as (f0 & H0 & Hb0 & Hs0 & He0 & Hd0).
      exists f0; split; [exact H0 | repeat split; congruence].
    - intros m f0 H0 Hd; destruct (S2 m f0 H0 Hd) as [f1 H1].
      destruct (S1 m f1 H1) as (f0' & H0' & _ & _ & _ & Hd1).
      rewrite H0 in H0'; injection H0' as <-.
      apply (T2 m f1 H1); congruence.
  Qed.

  Lemma static_k (γ0 γ : State) : Static Σ γ0 γ -> KStatic γ0 γ.
  Proof.
    intros [S1 S2]; split; [|exact S2].
    intros m fm H; destruct (S1 m fm H) as (f0 & H0 & Hc & Hd); exists f0; rewrite Hc; auto.
  Qed.

  Lemma kstatic_recomp (γ : State) n f : fibers γ n = Some f -> KStatic γ (recomp γ n f).
  Proof.
    intros Hn; split.
    - intros m fm H; rewrite fibers_recomp in H.
      destruct (Nat.eqb_spec m n) as [->|]; [injection H as <-; exists f; auto|exists fm; auto].
    - intros m f0 H _; rewrite fibers_recomp.
      destruct (Nat.eqb_spec m n); eauto.
  Qed.

  Lemma kstatic_restart (γ γ' : State) n : step γ (ORestart n) = Some γ' -> KStatic γ γ'.
  Proof.
    intros H; destruct (restart_shape kdec Σ prog' γ γ' n H) as (f & acc & w & Hn & _ & _ & ->).
    split.
    - intros m fm Hm; cbn [set_life set_fiber with_fibers Calculus.fibers] in Hm; unfold fupd in Hm.
      destruct (Nat.eqb_spec m n) as [->|]; [injection Hm as <-; exists f; auto|exists fm; auto].
    - intros m f0 H0 _; cbn [set_life set_fiber with_fibers Calculus.fibers]; unfold fupd.
      destruct (Nat.eqb_spec m n); eauto.
  Qed.

  (** ** Extended lifecycle runs *)
  Inductive KLRun : State -> State -> Prop :=
  | klr_nil γ : KLRun γ γ
  | klr_cons γ n ℓ γ1 γ2 : In ℓ (@lifecycle_labels C n) -> kstep γ ℓ = Some γ1 -> KLRun γ1 γ2 ->
                           KLRun γ γ2.

  Lemma kstep_cinv (γ γ' : State) n ℓ :
    KCInv γ -> In ℓ (@lifecycle_labels C n) -> kstep γ ℓ = Some γ' -> KCInv γ' /\ KStatic γ γ'.
  Proof.
    intros I Hin H.
    pose proof (t_wf _ _ _ _ _ (c_t _ _ _ _ _ (proj1 I))) as W.
    pose proof (si_kstep N_eq_dec Σ xprog γ γ' ℓ W (proj2 I) H) as S'.
    destruct (kstep_core N_eq_dec Σ xprog γ γ' ℓ H)
      as [St|[(m & f & _ & Hm & Hl & _ & Hp & St)|[(m & St)|(m & i & f & E & _)]]].
    - assert (Hlc : is_lifecycle (klab Σ xprog γ ℓ)).
      { exists n; cbn in Hin |- *.
        destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn; tauto. }
      split; [split; [exact (cinv_step γ γ' _ (lifecycle_not_react _ Hlc) (proj1 I) St) | exact S']|].
      exact (static_k γ γ' (lstep_static γ γ' _ (proj1 I) Hlc St)).
    - pose proof (cinv_recomp γ m f I Hm Hl Hp) as Ir.
      assert (Hlc : is_lifecycle (@LBegin XC m)) by (exists m; cbn; auto).
      split; [split; [exact (cinv_step _ γ' _ (lifecycle_not_react _ Hlc) Ir St) | exact S']|].
      exact (kstatic_trans _ _ _ (kstatic_recomp γ m f Hm)
                           (static_k _ _ (lstep_static _ γ' _ Ir Hlc St))).
    - assert (NR : forall a b, @ORestart XC m <> OReact a b) by (intros a b E; discriminate E).
      split; [split; [exact (cinv_step γ γ' _ NR (proj1 I) St) | exact S']|].
      exact (kstatic_restart γ γ' m St).
    - subst ℓ; exfalso; cbn in Hin; intuition discriminate.
  Qed.

  Lemma klrun_cinv (γ0 γ : State) : KCInv γ0 -> KLRun γ0 γ -> KCInv γ /\ KStatic γ0 γ.
  Proof.
    intros I0 R; induction R as [γ|γ n ℓ γ1 γ2 Hin Hs R IH].
    - split; [exact I0 | apply kstatic_refl].
    - destruct (kstep_cinv γ γ1 n ℓ I0 Hin Hs) as [I1 S1].
      destruct (IH I1) as [I2 S2]; split; [exact I2 | exact (kstatic_trans _ _ _ S1 S2)].
  Qed.

  (** ** Final states *)
  Lemma final_ksettled (γ : State) : KCInv γ -> kquiet γ -> ksettled γ.
  Proof. intros I Q; exact (kquiet_settled N_eq_dec Σ xprog xrank Rb Hrank Hbnd kSub γ (kinv_of γ I) Q). Qed.

  Lemma kshape (γ : State) n f :
    ksettled γ -> NoFailed Σ γ -> fibers γ n = Some f ->
    disposed f = false /\
    ((life f = Inactive Σ None /\ bt γ n = None) \/
     (exists acc w, life f = Active Σ acc w /\ target γ n = Some w /\ fresh γ f = true)).
  Proof.
    intros St NF Hn; pose proof (St n f Hn) as Sf; unfold ksettled_fiber in Sf.
    destruct (life f) as [[e|]|P acc w|acc w|acc w z] eqn:Hl.
    - exfalso; exact (NF n f e Hn Hl).
    - destruct Sf as [Hd Hb]; split; [exact Hd | left; auto].
    - destruct Sf.
    - destruct Sf as [Ht F]; split.
      + unfold Calculus.target in Ht; rewrite Hn in Ht; destruct (disposed f); [discriminate | reflexivity].
      + right; exists acc, w; auto.
    - destruct Sf.
  Qed.

  Lemma active_provides (γ : State) m fm k :
    KCInv γ -> fibers γ m = Some fm -> is_active (life fm) = true -> In k (provs Σ (prog' (fcomp fm))) ->
    exists b, binds γ k = Some b /\ owner b = m.
  Proof.
    intros I Hm Ha Hk; exact (active_binds kdec Σ prog' Kb γ m fm k (cinv_0 _ _ _ _ _ (proj1 I)) Hm Ha Hk).
  Qed.

  (** A key is visible iff an Active fiber may provide it. *)
  Lemma vis_k (γ : State) k :
    KCInv γ ->
    ((exists p, visible Σ γ k = Some p) <->
     exists m fm, fibers γ m = Some fm /\ is_active (life fm) = true /\ In k (provs Σ (prog' (fcomp fm)))).
  Proof.
    intros I; pose proof (t_wf _ _ _ _ _ (c_t _ _ _ _ _ (proj1 I))) as W; split.
    - intros [p Hv]; unfold visible in Hv.
      destruct (binds γ k) as [b|] eqn:Hb; [|discriminate].
      destruct (fibers γ (owner b)) as [fo|] eqn:Ho; [|discriminate].
      destruct (is_active (life fo)) eqn:Ha; [|discriminate].
      destruct (wf_bind kdec Σ prog' γ W k b Hb) as (fo' & Ho' & _ & Hko & _).
      rewrite Ho in Ho'; injection Ho' as <-.
      exists (owner b), fo; repeat split; auto; exact (kmem_In kdec k _ Hko).
    - intros (m & fm & Hm & Ha & Hk).
      destruct (active_provides γ m fm k I Hm Ha Hk) as (b & Hb & Ho).
      exists (pid Σ b); unfold visible; rewrite Hb, Ho, Hm, Ha; reflexivity.
  Qed.

  (** A key is bound by [m] iff [m] is Active and may provide it. *)
  Lemma owner_k (γ : State) k m :
    KCInv γ -> kquiet γ -> NoFailed Σ γ ->
    (option_map owner (binds γ k) = Some m <->
     exists fm, fibers γ m = Some fm /\ is_active (life fm) = true /\ In k (provs Σ (prog' (fcomp fm)))).
  Proof.
    intros I Q NF.
    pose proof (t_wf _ _ _ _ _ (c_t _ _ _ _ _ (proj1 I))) as W.
    pose proof (final_ksettled γ I Q) as St.
    split.
    - destruct (binds γ k) as [b|] eqn:Hb; cbn; [intros [= <-] | discriminate].
      destruct (wf_bind kdec Σ prog' γ W k b Hb) as (fo & Ho & Hio & Hko & _).
      exists fo; split; [exact Ho|]; split; [|exact (kmem_In kdec k _ Hko)].
      destruct (kshape γ _ fo St NF Ho) as [_ [[Hl _]|(acc & w & Hl & _)]];
        rewrite Hl in *; [discriminate | reflexivity].
    - intros (fm & Hm & Ha & Hk).
      destruct (active_provides γ m fm k I Hm Ha Hk) as (b & Hb & Ho).
      rewrite Hb; cbn; congruence.
  Qed.

  (** At a quiet state with no failure, a fiber is Active iff choosing its
      selection would give it a target. *)
  Lemma act_bt (γ : State) n f :
    KCInv γ -> kquiet γ -> NoFailed Σ γ -> fibers γ n = Some f ->
    (is_active (life f) = true <-> bt γ n <> None).
  Proof.
    intros I Q NF Hn.
    destruct (kshape γ n f (final_ksettled γ I Q) NF Hn) as [_ [[Hl Hb]|(acc & w & Hl & Ht & F)]].
    - rewrite Hl; split; [discriminate | intros E; contradiction].
    - rewrite Hl; split; [intros _ | reflexivity].
      rewrite (bt_fresh N_eq_dec Σ xprog γ n f Hn F), Ht; discriminate.
  Qed.

  Lemma provs_static (x1 x2 : XC) :
    base x1 = base x2 -> scope x1 = scope x2 -> provs Σ (prog' x1) = provs Σ (prog' x2).
  Proof. intros Eb Es; cbn [Scoped.prog' provs]; rewrite Eb, Es; reflexivity. Qed.

  Lemma deps_rcomp_static (γ1 γ2 : State) (x1 x2 : XC) :
    base x1 = base x2 -> env x1 = env x2 -> choose γ1 (base x1) = choose γ2 (base x2) ->
    deps Σ (prog' (rcomp γ1 x1)) = deps Σ (prog' (rcomp γ2 x2)).
  Proof.
    intros Eb Ee Ec; unfold ScopedTerm.rcomp; cbn [Scoped.prog' deps base].
    rewrite <- Eb; apply map_ext; intros [y|y]; unfold Scoped.dkey; cbn [env sel].
    - rewrite Ee; reflexivity.
    - rewrite Ec, Eb; reflexivity.
  Qed.

  Lemma resolve_some_iff (γ1 γ2 : State) ks :
    (forall k, In k ks -> ((exists p, visible Σ γ1 k = Some p) <-> (exists p, visible Σ γ2 k = Some p))) ->
    (resolve Σ γ1 ks <> None <-> resolve Σ γ2 ks <> None).
  Proof.
    induction ks as [|k ks IH]; intros H; cbn; [tauto|].
    pose proof (H k (or_introl eq_refl)) as Ek.
    specialize (IH (fun k' Hk' => H k' (or_intror Hk'))).
    destruct (visible Σ γ1 k) as [p1|] eqn:V1, (visible Σ γ2 k) as [p2|] eqn:V2.
    - destruct (resolve Σ γ1 ks) as [w1|], (resolve Σ γ2 ks) as [w2|].
      + split; intros _; discriminate.
      + exfalso; apply (proj1 IH); [discriminate | reflexivity].
      + exfalso; apply (proj2 IH); [discriminate | reflexivity].
      + tauto.
    - exfalso; destruct (proj1 Ek (ex_intro _ p1 eq_refl)) as [p E]; discriminate.
    - exfalso; destruct (proj2 Ek (ex_intro _ p2 eq_refl)) as [p E]; discriminate.
    - tauto.
  Qed.

  (** ** Control confluence *)
  Theorem kcontrol_confluence (γ0 γ1 γ2 : State) :
    KCInv γ0 -> KLRun γ0 γ1 -> KLRun γ0 γ2 ->
    kquiet γ1 -> kquiet γ2 -> NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    (forall n, (exists f, fibers γ1 n = Some f) <-> (exists f, fibers γ2 n = Some f)) /\
    (forall n f1 f2, fibers γ1 n = Some f1 -> fibers γ2 n = Some f2 ->
       base (fcomp f1) = base (fcomp f2) /\ scope (fcomp f1) = scope (fcomp f2) /\
       env (fcomp f1) = env (fcomp f2) /\ is_active (life f1) = is_active (life f2) /\
       (is_active (life f1) = true -> sel (fcomp f1) = sel (fcomp f2))) /\
    (forall k, option_map owner (binds γ1 k) = option_map owner (binds γ2 k)) /\
    (forall y, candidates γ1 y = candidates γ2 y).
  Proof.
    intros I0 R1 R2 Q1 Q2 NF1 NF2.
    destruct (klrun_cinv γ0 γ1 I0 R1) as [C1 [T1 U1]].
    destruct (klrun_cinv γ0 γ2 I0 R2) as [C2 [T2 U2]].
    pose proof (final_ksettled γ1 C1 Q1) as St1.
    pose proof (final_ksettled γ2 C2 Q2) as St2.
    pose proof (t_wf _ _ _ _ _ (c_t _ _ _ _ _ (proj1 C1))) as W1.
    pose proof (t_wf _ _ _ _ _ (c_t _ _ _ _ _ (proj1 C2))) as W2.
    (* the domain is fixed by the start state *)
    assert (Dom : forall n, (exists f, fibers γ1 n = Some f) <-> (exists f, fibers γ2 n = Some f)).
    { assert (Pres : forall γ, KStatic γ0 γ -> ksettled γ -> NoFailed Σ γ ->
                forall n, (exists f, fibers γ n = Some f) <->
                          exists f0, fibers γ0 n = Some f0 /\ disposed f0 = false).
      { intros γ [Ta Ub] St NF n; split.
        - intros [f Hf]; destruct (Ta n f Hf) as (f0 & H0 & _ & _ & _ & Hd).
          exists f0; split; [exact H0|].
          rewrite <- Hd; exact (proj1 (kshape γ n f St NF Hf)).
        - intros (f0 & H0 & Hd); exact (Ub n f0 H0 Hd). }
      intros n; rewrite (Pres γ1 (conj T1 U1) St1 NF1 n), (Pres γ2 (conj T2 U2) St2 NF2 n); reflexivity. }
    (* static data agree *)
    assert (Sta : forall n f1 f2, fibers γ1 n = Some f1 -> fibers γ2 n = Some f2 ->
              base (fcomp f1) = base (fcomp f2) /\ scope (fcomp f1) = scope (fcomp f2) /\
              env (fcomp f1) = env (fcomp f2) /\ disposed f1 = disposed f2).
    { intros n f1 f2 H1 H2.
      destruct (T1 n f1 H1) as (f0 & H0 & Hb1 & Hs1 & He1 & Hd1).
      destruct (T2 n f2 H2) as (f0' & H0' & Hb2 & Hs2 & He2 & Hd2).
      rewrite H0 in H0'; injection H0' as <-; repeat split; congruence. }
    (* visibility of a key from the activity of its providers *)
    assert (VisFrom : forall k,
              (forall m fm1 fm2, fibers γ1 m = Some fm1 -> fibers γ2 m = Some fm2 ->
                 In (snd k) (xprovs (base (fcomp fm1))) -> is_active (life fm1) = is_active (life fm2)) ->
              ((exists p, visible Σ γ1 k = Some p) <-> (exists p, visible Σ γ2 k = Some p))).
    { intros k HA; rewrite (vis_k γ1 k C1), (vis_k γ2 k C2).
      split; intros (m & fm & Hm & Ha & Hk).
      - destruct (proj1 (Dom m) (ex_intro _ fm Hm)) as [fm2 Hm2].
        destruct (Sta m fm fm2 Hm Hm2) as (Eb & Es & _ & _).
        assert (Hy : In (snd k) (xprovs (base (fcomp fm)))).
        { cbn [Scoped.prog' provs] in Hk; apply in_map_iff in Hk as (y & <- & Hy); exact Hy. }
        exists m, fm2; split; [exact Hm2|]; split; [rewrite <- (HA m fm fm2 Hm Hm2 Hy); exact Ha|].
        rewrite <- (provs_static _ _ Eb Es); exact Hk.
      - destruct (proj2 (Dom m) (ex_intro _ fm Hm)) as [fm1 Hm1].
        destruct (Sta m fm1 fm Hm1 Hm) as (Eb & Es & _ & _).
        assert (Hy : In (snd k) (xprovs (base (fcomp fm1)))).
        { rewrite <- (provs_static _ _ Eb Es) in Hk.
          cbn [Scoped.prog' provs] in Hk; apply in_map_iff in Hk as (y & <- & Hy); exact Hy. }
        exists m, fm1; split; [exact Hm1|]; split; [rewrite (HA m fm1 fm Hm1 Hm Hy); exact Ha|].
        rewrite (provs_static _ _ Eb Es); exact Hk. }
    (* candidates from visibility *)
    assert (CandFrom : forall y,
              (forall s, (exists p, visible Σ γ1 (s, y) = Some p) <-> (exists p, visible Σ γ2 (s, y) = Some p)) ->
              candidates γ1 y = candidates γ2 y).
    { intros y HV.
      rewrite (candidates_ext N_eq_dec Σ xprog γ1 y (next Σ γ1 + next Σ γ2) W1) by lia.
      rewrite (candidates_ext N_eq_dec Σ xprog γ2 y (next Σ γ1 + next Σ γ2) W2) by lia.
      apply omap_ext_in; intros m _; unfold Scoped.candidate.
      destruct (fibers γ1 m) as [fm1|] eqn:H1, (fibers γ2 m) as [fm2|] eqn:H2.
      - destruct (Sta m fm1 fm2 H1 H2) as (Eb & Es & _ & _); rewrite Eb, Es.
        destruct (nmem N_eq_dec y (xexports Σ (xprog (base (fcomp fm2))))); [|reflexivity].
        pose proof (HV (scope (fcomp fm2))) as E.
        destruct (visible Σ γ1 (scope (fcomp fm2), y)) as [p1|] eqn:V1,
                 (visible Σ γ2 (scope (fcomp fm2), y)) as [p2|] eqn:V2; try reflexivity.
        + exfalso; destruct (proj1 E (ex_intro _ p1 eq_refl)) as [p F]; discriminate.
        + exfalso; destruct (proj2 E (ex_intro _ p2 eq_refl)) as [p F]; discriminate.
      - exfalso; destruct (proj1 (Dom m) (ex_intro _ fm1 H1)) as [f F]; congruence.
      - exfalso; destruct (proj2 (Dom m) (ex_intro _ fm2 H2)) as [f F]; congruence.
      - reflexivity. }
    (* activity agrees, by induction on the rank *)
    assert (Act : forall r n f1 f2, fibers γ1 n = Some f1 -> fibers γ2 n = Some f2 ->
              frank f1 < r -> is_active (life f1) = is_active (life f2)).
    { induction r as [|r IH]; intros n f1 f2 H1 H2 Hr; [lia|].
      destruct (Sta n f1 f2 H1 H2) as (Eb & Es & Ee & Ed).
      (* keys named by [n]'s dependencies are equally visible *)
      assert (VisN : forall k, In (snd k) (dnames (base (fcomp f1))) ->
                ((exists p, visible Σ γ1 k = Some p) <-> (exists p, visible Σ γ2 k = Some p))).
      { intros k Hk; apply VisFrom; intros m fm1 fm2 Hm1 Hm2 Hp.
        apply (IH m fm1 fm2 Hm1 Hm2).
        assert (xrank (base (fcomp fm1)) < xrank (base (fcomp f1)))
          by (apply Hrank; left; exists (snd k); auto).
        lia. }
      assert (Sel : forall y, In y (globals (base (fcomp f1))) -> select γ2 y = select γ1 y).
      { intros y Hy.
        assert (Hyd : In y (dnames (base (fcomp f1)))) by exact (globals_dname Σ xprog _ _ Hy).
        unfold Scoped.select; rewrite (CandFrom y); [reflexivity|].
        intros s; exact (VisN (s, y) Hyd). }
      assert (Ebt : bt γ1 n <> None <-> bt γ2 n <> None).
      { unfold ScopedTerm.bt; rewrite H1, H2, <- Ed.
        destruct (disposed f1); [tauto|].
        rewrite <- Eb, (all_selected_ext N_eq_dec Σ xprog γ1 γ2 _ Sel).
        destruct (all_selected γ1 (base (fcomp f1))); [|tauto].
        rewrite <- (deps_rcomp_static γ1 γ2 (fcomp f1) (fcomp f2) Eb Ee).
        - apply resolve_some_iff; intros k Hk.
          apply VisN; exact (deps_keyof N_eq_dec Σ xprog _ k Hk).
        - rewrite <- Eb; symmetry; exact (choose_ext N_eq_dec Σ xprog γ1 γ2 _ Sel). }
      pose proof (act_bt γ1 n f1 C1 Q1 NF1 H1) as A1.
      pose proof (act_bt γ2 n f2 C2 Q2 NF2 H2) as A2.
      destruct (is_active (life f1)), (is_active (life f2)); try reflexivity; exfalso.
      - discriminate (proj2 A2 (proj1 Ebt (proj1 A1 eq_refl))).
      - discriminate (proj2 A1 (proj2 Ebt (proj1 A2 eq_refl))). }
    assert (ActAll : forall n f1 f2, fibers γ1 n = Some f1 -> fibers γ2 n = Some f2 ->
              is_active (life f1) = is_active (life f2))
      by (intros n f1 f2 H1 H2; exact (Act (S (frank f1)) n f1 f2 H1 H2 ltac:(lia))).
    assert (Vis : forall k, (exists p, visible Σ γ1 k = Some p) <-> (exists p, visible Σ γ2 k = Some p))
      by (intros k; apply VisFrom; intros m fm1 fm2 Hm1 Hm2 _; exact (ActAll m fm1 fm2 Hm1 Hm2)).
    assert (Cand : forall y, candidates γ1 y = candidates γ2 y)
      by (intros y; apply CandFrom; intros s; apply Vis).
    assert (SelAll : forall y, select γ1 y = select γ2 y)
      by (intros y; unfold Scoped.select; rewrite Cand; reflexivity).
    split; [exact Dom|]; split; [|split; [|exact Cand]].
    - intros n f1 f2 H1 H2.
      destruct (Sta n f1 f2 H1 H2) as (Eb & Es & Ee & _).
      pose proof (ActAll n f1 f2 H1 H2) as Ea.
      split; [exact Eb|]; split; [exact Es|]; split; [exact Ee|]; split; [exact Ea|].
      intros A1.
      destruct (kshape γ1 n f1 St1 NF1 H1) as [_ [[Hl _]|(acc1 & w1 & Hl1 & _ & F1)]];
        [rewrite Hl in A1; discriminate|].
      assert (A2 : is_active (life f2) = true) by congruence.
      destruct (kshape γ2 n f2 St2 NF2 H2) as [_ [[Hl _]|(acc2 & w2 & Hl2 & _ & F2)]];
        [rewrite Hl in A2; discriminate|].
      unfold Scoped.fresh in F1, F2; apply andb_true_iff in F1 as [_ F1]; apply andb_true_iff in F2 as [_ F2].
      destruct (list_eq_dec (ns_eq_dec N_eq_dec) (sel (fcomp f1)) (choose γ1 (base (fcomp f1)))) as [E1|]; [|discriminate].
      destruct (list_eq_dec (ns_eq_dec N_eq_dec) (sel (fcomp f2)) (choose γ2 (base (fcomp f2)))) as [E2|]; [|discriminate].
      rewrite E1, E2, <- Eb; unfold Scoped.choose; apply map_ext; intros y; rewrite SelAll; reflexivity.
    - intros k.
      assert (O : forall m, option_map owner (binds γ1 k) = Some m <->
                            option_map owner (binds γ2 k) = Some m).
      { intros m; rewrite (owner_k γ1 k m C1 Q1 NF1), (owner_k γ2 k m C2 Q2 NF2).
        split; intros (fm & Hm & Ha & Hp).
        - destruct (proj1 (Dom m) (ex_intro _ fm Hm)) as [fm2 Hm2].
          destruct (Sta m fm fm2 Hm Hm2) as (Eb & Es & _ & _).
          exists fm2; split; [exact Hm2|]; split; [rewrite <- (ActAll m fm fm2 Hm Hm2); exact Ha|].
          rewrite <- (provs_static _ _ Eb Es); exact Hp.
        - destruct (proj2 (Dom m) (ex_intro _ fm Hm)) as [fm1 Hm1].
          destruct (Sta m fm1 fm Hm1 Hm) as (Eb & Es & _ & _).
          exists fm1; split; [exact Hm1|]; split; [rewrite (ActAll m fm1 fm Hm1 Hm); exact Ha|].
          rewrite (provs_static _ _ Eb Es); exact Hp. }
      destruct (option_map owner (binds γ1 k)) as [m1|] eqn:O1,
               (option_map owner (binds γ2 k)) as [m2|] eqn:O2; try reflexivity.
      + pose proof (proj1 (O m1) eq_refl) as E; congruence.
      + pose proof (proj1 (O m1) eq_refl) as E; congruence.
      + pose proof (proj2 (O m2) eq_refl) as E; congruence.
  Qed.

  (** The same resolution, and the same conflicts reported. *)
  Corollary kselect_confluence (γ0 γ1 γ2 : State) :
    KCInv γ0 -> KLRun γ0 γ1 -> KLRun γ0 γ2 ->
    kquiet γ1 -> kquiet γ2 -> NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    forall y, select γ1 y = select γ2 y /\ tied N_eq_dec Σ xprog γ1 y = tied N_eq_dec Σ xprog γ2 y.
  Proof.
    intros I0 R1 R2 Q1 Q2 NF1 NF2 y.
    destruct (kcontrol_confluence γ0 γ1 γ2 I0 R1 R2 Q1 Q2 NF1 NF2) as (_ & _ & _ & Cand).
    unfold Scoped.select, Scoped.tied; rewrite (Cand y); auto.
  Qed.
End ScopedConf.
