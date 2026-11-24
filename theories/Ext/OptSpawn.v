(** * Extension 1: confluence with spawn, for optional dependencies

    Counterpart of [SpawnConf.spawn_confluence]: two extended lifecycle
    executions from a common state that end quiet with no fiber failed
    agree up to renaming ([xspawn_confluence]): canonical names name every
    fiber once, the same names occur with the same components and
    activity, corresponding fibers own each key, and each key's service
    states are ≃.

    Restriction: a component that may be spawned, or run as a handler,
    declares no optional dependency ([NoOptChild]); only inserted (root)
    components do. The reason: the core's trace invariant ([Episode.Corr])
    checks a spawned child's exact component, so re-choosing a child's
    presence would break it. Under the restriction a child's component is
    always [(c, [])] and re-choosing its presence changes nothing
    ([recomp_child]); re-choosing a root's presence keeps every core
    invariant ([RF2], [rf2_pinv], [rf2_sl]).

    What the proof adds to the core's:
    - Final states are normalised ([norm], as in [OptState.v]): every
      Inactive fiber takes the final presence, so that every fiber's
      presence is current ([Fresh]).
    - The core's rank induction ([SpawnConf.corr_step]) is redone with one
      change: two corresponding roots are known to have the same base
      component only; that they have the same presence follows from the
      correspondence at lower ranks, because each optional key is provided
      by a fiber of lower rank ([present_corr]). Everything else, including
      [SpawnConf.corr_pair] and the final comparison of service states, is
      the core's. *)

From Stdlib Require Import List PeanoNat Bool Lia RelationClasses Permutation Sorted Wf_nat.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering
  Recovery Progress Termination Confluence StateInv Episode StateConf SpawnConf Dynamic.
From Cordis Require Import Ext.Optional Ext.OptProgress Ext.OptConfluence Ext.OptState.
Import ListNotations.

Section OptSpawn.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (C_eq_dec : forall x y : C, {x = y} + {x <> y}).
  Context (xprog : C -> @XComponent K Σ C).

  Local Notation CC := (@Optional.C' K C).
  Local Notation State := (@State K Σ CC).
  Local Notation Fiber := (@Fiber K Σ CC).
  Local Notation S := (St Σ).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation fparent := (Calculus.parent Σ).
  Local Notation disposed := (Calculus.disposed Σ).
  Local Notation is_active := (is_active Σ).
  Local Notation is_installed := (is_installed Σ).
  Local Notation acc_of := (acc_of Σ).
  Local Notation owner := (owner Σ).
  Local Notation bst := (bst Σ).
  Local Notation prog' := (prog' K_eq_dec Σ xprog).
  Local Notation step := (step K_eq_dec Σ prog').
  Local Notation xstep := (xstep K_eq_dec Σ xprog).
  Local Notation recomp := (recomp Σ xprog).
  Local Notation present := (present Σ xprog).
  Local Notation WF := (WF K_eq_dec Σ prog').
  Local Notation xdeps c := (xdeps Σ (xprog c)).
  Local Notation xopt c := (xopt Σ (xprog c)).
  Local Notation xprovs c := (xprovs Σ (xprog c)).

  (** ** Hypotheses *)
  Variable Kb : nat.
  Hypothesis xHK : forall c T, Bounded Σ Kb (xbody Σ (xprog c) T).
  Variable xrank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', XAbove Σ xprog c c' -> xrank c < xrank c'.
  Hypothesis Hbnd : forall c, xrank c <= Rb.
  Hypothesis xTotal : forall c T k, In k (xprovs c) -> AllDoneProv Σ k (xbody Σ (xprog c) T).
  (** Children have no optional dependency. *)
  Hypothesis NoOptChild : forall c c', XSpawns Σ xprog c c' -> xopt c' = [].

  Hypothesis Hwb : forall a t, WellBehaved (Σ := Σ) a t.
  Hypothesis HUI : forall (a : Op Σ) (t : nat) (s1 s2 s1' s2' : S) (g1 g2 : S -> S) (o1 o2 : Out Σ),
    run a t s1 = Some (s1', g1, o1) -> run a t s2 = Some (s2', g2, o2) -> fun_eq (Σ := Σ) g1 g2.
  Hypothesis HTI : forall (a : Op Σ) (t t' : nat) (s : S),
    match run a t s, run a t' s with
    | None, None => True
    | Some (s1, _, o1), Some (s2, _, o2) => @st_eq Σ s1 s2 /\ o1 = o2
    | _, _ => False
    end.
  Hypothesis HRI : forall (k : K) (a b : Op Σ) (ta tb : nat) (g : S -> S),
    CoPair Σ prog' k a b -> ta <> tb -> yields (Σ := Σ) a ta g ->
    forall x, After (CoPair Σ prog' k a) a ta x -> shifted_ok (Σ := Σ) g (run b tb x) (run b tb (g x)).
  Hypothesis HCom : forall (k : K) (a b : Op Σ) (ta tb : nat), CoPair Σ prog' k a b -> ta <> tb ->
    Commute (Σ := Σ) a ta b tb.

  Local Notation rank' := (fun x : CC => xrank (fst x)).

  Lemma spawnin_lift_snd (y : CC) (P : @Prog K Σ C) : SpawnIn Σ y (lift Σ P) -> snd y = [].
  Proof.
    induction P as [| |k a κ IH|k s Q IH|c Q IH]; cbn; intros H; inversion H; subst; eauto.
  Qed.

  Lemma Hrank2 : forall x y, Above Σ prog' x y -> rank' x < rank' y.
  Proof.
    intros x y [(k & Hp & Hd)|[Hs|Hr]]; apply Hrank.
    - left; exists k; split; [exact Hp|].
      unfold Optional.prog' in Hd; cbn [deps] in Hd.
      apply in_app_or in Hd as [Hd|Hd]; [left; exact Hd|].
      right; apply filter_In in Hd as [_ Hd].
      unfold kmem, keqb in Hd; apply existsb_exists in Hd as (k' & Hk' & E).
      destruct (K_eq_dec k k') as [->|]; [exact Hk' | discriminate].
    - right; left; unfold Optional.prog' in Hs; cbn [body] in Hs.
      eexists; exact (spawnin_lift Σ _ _ Hs).
    - right; right; unfold Optional.prog' in Hr; cbn [reacts] in Hr.
      apply in_map_iff in Hr as (c & <- & Hc); exact Hc.
  Qed.

  Local Notation HK' := (HK' K_eq_dec Σ xprog Kb xHK).
  Local Notation Total' := (Total' K_eq_dec Σ xprog xTotal).
  Local Notation PInv := (PInv K_eq_dec Σ prog' Kb).
  Local Notation SInv := (SInv K_eq_dec Σ prog' Kb).
  Local Notation TInv := (TInv K_eq_dec Σ prog' Kb).
  Local Notation pinv_step :=
    (pinv_step K_eq_dec Σ prog' Kb HK' rank' Hrank2 Total' Hwb HUI HTI HRI HCom).
  Local Notation FinalS := (FinalS K_eq_dec Σ prog' Kb).

  Lemma pinv_tinv (γ : State) : PInv γ -> TInv γ.
  Proof. intros P; exact (c0_t _ _ _ _ _ (s_c _ _ _ _ _ (p_s _ _ _ _ _ P))). Qed.

  (** ** Children are plain *)
  Lemma child_plain (γ : State) m fm q :
    TInv γ -> fibers γ m = Some fm -> fparent fm = Some q ->
    snd (fcomp fm) = [] /\ xopt (fst (fcomp fm)) = [].
  Proof.
    intros [W _ [_ Sp] _ _] Hm Hq.
    destruct (wf_parent K_eq_dec Σ prog' γ W m fm q Hm Hq) as (fq & Hfq & _ & Hu).
    destruct (Sp q fq m fm Hfq Hu Hm) as [Hs|Hr].
    - unfold Optional.prog' in Hs; cbn [body] in Hs.
      split; [exact (spawnin_lift_snd _ _ Hs)|].
      apply (NoOptChild (fst (fcomp fq))); left; eexists; exact (spawnin_lift Σ _ _ Hs).
    - unfold Optional.prog' in Hr; cbn [reacts] in Hr.
      apply in_map_iff in Hr as (c & <- & Hc); split; [reflexivity|].
      apply (NoOptChild (fst (fcomp fq))); right; exact Hc.
  Qed.

  Lemma fiber_eta (f : Fiber) : f = @mkFiber K Σ CC (fcomp f) (fparent f) (disposed f) (life f).
  Proof. destruct f; reflexivity. Qed.

  Lemma plain_same (γ : State) f :
    snd (fcomp f) = [] -> xopt (fst (fcomp f)) = [] ->
    @mkFiber K Σ CC (fst (fcomp f), present γ (fst (fcomp f))) (fparent f) (disposed f) (life f) = f.
  Proof.
    destruct f as [[c s] q d l]; cbn; intros E1 E2; subst s.
    unfold Optional.present; rewrite E2; reflexivity.
  Qed.

  (** Re-choosing a child's presence changes nothing. *)
  Lemma recomp_child (γ : State) n f q :
    TInv γ -> fibers γ n = Some f -> fparent f = Some q -> recomp γ n f = γ.
  Proof.
    intros T Hn Hq; destruct (child_plain γ n f q T Hn Hq) as [E1 E2].
    unfold Optional.recomp.
    match goal with |- set_fiber _ _ _ ?g = _ => replace g with f by (symmetry; exact (plain_same γ f E1 E2)) end.
    destruct γ as [nx F B ol il]; unfold set_fiber, with_fibers; cbn in *; f_equal.
    apply functional_extensionality; intros m; unfold fupd.
    destruct (Nat.eqb_spec m n) as [->|]; [exact (eq_sym Hn) | reflexivity].
  Qed.

  (** ** Changing the components of Inactive roots *)
  Definition RF2 (γ : State) (F : nat -> option Fiber) : Prop :=
    RF Σ γ F /\
    (forall m fm fm0, F m = Some fm -> fibers γ m = Some fm0 -> fparent fm0 <> None -> fm = fm0).

  Lemma acc_installed (l : @Life K Σ CC) u : In u (acc_of l) -> is_installed l = true.
  Proof. destruct l; cbn; [intros []|reflexivity..]. Qed.

  Lemma rf2_tinv (γ : State) F : TInv γ -> RF2 γ F -> TInv (with_fibers Σ γ F).
  Proof.
    intros [W [PF PT] [U Sp] LB SO] [R E2]; pose proof R as [R1 R2].
    (* a fiber holding a spawn item is installed, so unchanged; so is its child *)
    assert (Hpar : forall x fx m, F x = Some fx -> In (USpawn Σ m) (acc_of (life fx)) ->
              fibers γ x = Some fx /\
              forall fm, F m = Some fm -> fibers γ m = Some fm /\ fparent fm = Some x).
    { intros x fx m Hx Hu.
      destruct (R1 x fx Hx) as (fx0 & Hx0 & El & _ & _ & _ & Ei).
      assert (Ins : is_installed (life fx0) = true) by (rewrite El in Hu; exact (acc_installed _ _ Hu)).
      pose proof (Ei Ins) as Efx; subst fx; split; [exact Hx0|].
      intros fm Hm; destruct (R1 m fm Hm) as (fm0 & Hm0 & _ & Ep & _).
      pose proof (SO x fx0 m fm0 Hx0 Hu Hm0) as Hp0.
      rewrite (E2 m fm fm0 Hm Hm0 ltac:(rewrite Hp0; discriminate)); auto. }
    split.
    - exact (rf_wf K_eq_dec Σ xprog γ F W R).
    - split.
      + intros m fm H; destruct (R1 m fm H) as (fm0 & H0 & El & _ & _ & _ & E).
        destruct (is_installed (life fm0)) eqn:Hi.
        * rewrite (E eq_refl); exact (PF m fm0 H0).
        * destruct (life fm0) as [z| | |] eqn:L; try discriminate.
          exact (ProvF_inactive Σ prog' _ fm z El).
      + intros m1 m2 f1 f2 k1 p1 g1 k2 p2 g2 t Hne H1 H2 I1 I2.
        destruct (R1 m1 f1 H1) as (f1' & H1' & E1 & _), (R1 m2 f2 H2) as (f2' & H2' & Ee & _).
        rewrite E1 in I1; rewrite Ee in I2; exact (PT m1 m2 f1' f2' k1 p1 g1 k2 p2 g2 t Hne H1' H2' I1 I2).
    - split; [exact U|].
      intros x fx m fm Hx Hu Hm; destruct (Hpar x fx m Hx Hu) as [Hx0 Hc].
      destruct (Hc fm Hm) as [Hm0 _]; exact (Sp x fx m fm Hx0 Hu Hm0).
    - intros m fm P acc w H Hl; destruct (R1 m fm H) as (fm0 & H0 & El & _).
      rewrite El in Hl; exact (LB m fm0 P acc w H0 Hl).
    - intros x fx m fm Hx Hu Hm; destruct (Hpar x fx m Hx Hu) as [_ Hc].
      exact (proj2 (Hc fm Hm)).
  Qed.

  Lemma rf2_pinv (γ : State) F : PInv γ -> RF2 γ F -> PInv (with_fibers Σ γ F).
  Proof.
    intros [[[T PI] SG SI] EP] R2; pose proof R2 as [R E2]; pose proof R as [R1 R0].
    pose proof (rf2_tinv γ F T R2) as T'.
    pose proof T as [_ _ _ _ SO].
    split; [split; [split|..]|].
    - exact T'.
    - intros m fm H; destruct (R1 m fm H) as (fm0 & H0 & El & _ & _ & _ & E).
      destruct (is_installed (life fm0)) eqn:Hi.
      + rewrite (E eq_refl); exact (PI m fm0 H0).
      + unfold PIF; rewrite El; destruct (life fm0); try discriminate; exact Logic.I.
    - intros m fm H; destruct (R1 m fm H) as (fm0 & H0 & El & _ & _ & _ & E).
      destruct (is_installed (life fm0)) eqn:Hi.
      + rewrite (E eq_refl); exact (SG m fm0 H0).
      + unfold GF, uacc; rewrite El; destruct (life fm0); try discriminate; cbn.
        split; [constructor | intros k p t g []].
    - intros k b Hb; destruct (SI k b Hb) as (s0 & L & s & Hi & [Hs HL] & Rp & E).
      exists s0, L, s; split; [exact Hi|]; split; [split; [exact Hs|]|split; [exact Rp | exact E]].
      intros a t; rewrite (HL a t); cbn [Calculus.oplog with_fibers].
      rewrite (rf_item Σ γ F k (pid Σ b) t R); reflexivity.
    - intros m fm H; destruct (R1 m fm H) as (fm0 & H0 & El & _ & _ & _ & E).
      destruct (is_installed (life fm0)) eqn:Hi.
      + rewrite (E eq_refl); pose proof (EP m fm0 H0) as Ep.
        assert (Hcorr : forall c w acc evs, acc = acc_of (life fm0) ->
                  Corr K_eq_dec Σ prog' γ c w acc evs ->
                  Corr K_eq_dec Σ prog' (with_fibers Σ γ F) c w acc evs).
        { intros c w acc evs Ea Co; apply (corr_mono K_eq_dec Σ prog' γ _ c w acc evs Co);
            [intros; reflexivity | intros; reflexivity|].
          intros x Hx fm' Hm'; cbn [Calculus.fibers with_fibers] in Hm'.
          destruct (R1 x fm' Hm') as (fx0 & Hx0 & _).
          rewrite Ea in Hx; pose proof (SO m fm0 x fx0 H0 Hx Hx0) as Hp.
          rewrite (E2 x fm' fx0 Hm' Hx0 ltac:(rewrite Hp; discriminate)); eauto. }
        unfold epl in *; destruct (life fm0) as [|P acc w|acc w|] eqn:L; try exact Logic.I;
          destruct Ep as (evs & Tr0 & Co); exists evs; split; try exact Tr0;
          apply Hcorr; auto.
      + unfold epl; rewrite El; destruct (life fm0); try discriminate; exact Logic.I.
  Qed.

  Lemma rf2_sl (γ : State) F : SLInv Σ γ -> RF2 γ F -> SLInv Σ (with_fibers Σ γ F).
  Proof.
    intros SL [R _]; pose proof R as [R1 R2].
    split; cbn [Calculus.fibers with_fibers].
    - intros n f m H Hin; destruct (R1 n f H) as (f0 & H0 & El & _).
      rewrite El in Hin |- *; destruct (sl_live _ _ SL n f0 m H0 Hin) as [Hh|(fm0 & Hm0 & Hd)];
        [left; exact Hh | right].
      destruct (R2 m fm0 Hm0) as [fm Hm]; destruct (R1 m fm Hm) as (fm0' & Hm0' & _ & _ & Ed & _).
      rewrite Hm0 in Hm0'; injection Hm0' as <-; exists fm; split; [exact Hm | congruence].
    - intros n f H; destruct (R1 n f H) as (f0 & H0 & El & _); rewrite El; exact (sl_nodup _ _ SL n f0 H0).
    - intros m fm q H Hq; destruct (R1 m fm H) as (fm0 & H0 & _ & Ep & _).
      rewrite Ep in Hq; exact (sl_par _ _ SL m fm0 q H0 Hq).
  Qed.

  Lemma rf2_recomp_root (γ : State) n f :
    fibers γ n = Some f -> is_installed (life f) = false -> fparent f = None ->
    RF2 γ (Calculus.fibers Σ (recomp γ n f)).
  Proof.
    intros Hn Hi Hp; split; [exact (rf_recomp Σ xprog γ n f Hn Hi)|].
    intros m fm fm0 H H0 Hp0; rewrite fibers_recomp in H.
    destruct (Nat.eqb_spec m n) as [->|]; [rewrite Hn in H0; injection H0 as <-; congruence|].
    congruence.
  Qed.

  (** ** Base-level root keeping *)
  Definition XRootKeep (γ γ' : State) : Prop :=
    (forall m f', fibers γ' m = Some f' -> fparent f' = None ->
       exists f, fibers γ m = Some f /\ fparent f = None /\ fst (fcomp f) = fst (fcomp f') /\
                 disposed f = disposed f') /\
    (forall m f, fibers γ m = Some f -> fparent f = None -> disposed f = false ->
       exists f', fibers γ' m = Some f' /\ fparent f' = None /\ disposed f' = false).

  Lemma xrk_refl (γ : State) : XRootKeep γ γ.
  Proof. split; intros m f H P; [exists f; auto | intros D; exists f; auto]. Qed.

  Lemma xrk_trans (γ1 γ2 γ3 : State) : XRootKeep γ1 γ2 -> XRootKeep γ2 γ3 -> XRootKeep γ1 γ3.
  Proof.
    intros [A1 B1] [A2 B2]; split.
    - intros m f3 H3 P3; destruct (A2 m f3 H3 P3) as (f2 & H2 & P2 & C2 & D2).
      destruct (A1 m f2 H2 P2) as (f1 & H1 & P1 & C1 & D1); exists f1; repeat split; congruence.
    - intros m f1 H1 P1 D1; destruct (B1 m f1 H1 P1 D1) as (f2 & H2 & P2 & D2); exact (B2 m f2 H2 P2 D2).
  Qed.

  Lemma xrk_of (γ γ' : State) : RootKeep Σ γ γ' -> XRootKeep γ γ'.
  Proof.
    intros [A B]; split; [|exact B].
    intros m f' H P; destruct (A m f' H P) as (f & Hf & Pf & Cf & Df); exists f; rewrite Cf; auto.
  Qed.

  Lemma xrk_rf (γ : State) F : RF Σ γ F -> XRootKeep γ (with_fibers Σ γ F).
  Proof.
    intros [R1 R2]; split; cbn [Calculus.fibers with_fibers].
    - intros m f' H P; destruct (R1 m f' H) as (f & Hf & _ & Ep & Ed & Ec & _).
      exists f; repeat split; congruence.
    - intros m f Hf P D; destruct (R2 m f Hf) as [f' H].
      destruct (R1 m f' H) as (f0 & H0 & _ & Ep & Ed & _); rewrite Hf in H0; injection H0 as <-.
      exists f'; repeat split; congruence.
  Qed.

  Lemma xrk_restart (γ γ' : State) n : step γ (ORestart n) = Some γ' -> XRootKeep γ γ'.
  Proof.
    intros H; destruct (restart_shape K_eq_dec Σ prog' γ γ' n H) as (f & acc & w & Hn & _ & _ & ->).
    split.
    - intros m fm Hm P; cbn [set_life set_fiber with_fibers Calculus.fibers] in Hm; unfold fupd in Hm.
      destruct (Nat.eqb_spec m n) as [->|]; [injection Hm as <-; exists f; auto|exists fm; auto].
    - intros m f0 H0 P D; cbn [set_life set_fiber with_fibers Calculus.fibers]; unfold fupd.
      destruct (Nat.eqb_spec m n) as [->|]; [rewrite Hn in H0; injection H0 as <-; cbn; eauto|eauto].
  Qed.

  (** ** Extended runs keep [PInv], [SLInv], and the roots *)
  Lemma xstep_inv (γ γ' : State) n ℓ :
    PInv γ -> SLInv Σ γ -> In ℓ (@lifecycle_labels C n) -> xstep γ ℓ = Some γ' ->
    PInv γ' /\ SLInv Σ γ' /\ XRootKeep γ γ'.
  Proof.
    intros P SL Hin H.
    destruct (xstep_core K_eq_dec Σ xprog γ γ' ℓ H) as [St|[(m & f & _ & Hm & Hl & St)|(m & St)]].
    - pose proof (@xlab_lifecycle K C n ℓ Hin) as Hlc.
      split; [exact (pinv_step γ γ' _ (lifecycle_not_react _ Hlc) P St)|].
      split; [exact (sl_step K_eq_dec Σ prog' Kb γ γ' _ P SL Hlc St)|].
      exact (xrk_of _ _ (rk_step K_eq_dec Σ prog' Kb γ γ' _ P Hlc St)).
    - assert (Hlc : is_lifecycle (@LBegin CC m)) by (exists m; cbn; auto).
      assert (Hi : is_installed (life f) = false) by (rewrite Hl; reflexivity).
      destruct (fparent f) as [q|] eqn:Hp.
      + rewrite (recomp_child γ m f q (pinv_tinv γ P) Hm Hp) in St.
        split; [exact (pinv_step γ γ' _ (lifecycle_not_react _ Hlc) P St)|].
        split; [exact (sl_step K_eq_dec Σ prog' Kb γ γ' _ P SL Hlc St)|].
        exact (xrk_of _ _ (rk_step K_eq_dec Σ prog' Kb γ γ' _ P Hlc St)).
      + pose proof (rf2_recomp_root γ m f Hm Hi Hp) as R2.
        pose proof (rf2_pinv γ _ P R2) as Pr; pose proof (rf2_sl γ _ SL R2) as SLr.
        pose proof (xrk_rf γ _ (proj1 R2)) as Kr.
        rewrite <- recomp_with in Pr, SLr, Kr.
        split; [exact (pinv_step _ γ' _ (lifecycle_not_react _ Hlc) Pr St)|].
        split; [exact (sl_step K_eq_dec Σ prog' Kb _ γ' _ Pr SLr Hlc St)|].
        exact (xrk_trans _ _ _ Kr (xrk_of _ _ (rk_step K_eq_dec Σ prog' Kb _ γ' _ Pr Hlc St))).
    - assert (NR : forall a b, @ORestart CC m <> OReact a b) by (intros a b E; discriminate E).
      split; [exact (pinv_step γ γ' _ NR P St)|].
      split; [exact (sl_restart K_eq_dec Σ prog' γ γ' m SL St)|].
      exact (xrk_restart γ γ' m St).
  Qed.

  Lemma xlrun_inv (γ0 γ : State) :
    PInv γ0 -> SLInv Σ γ0 -> XLRun K_eq_dec Σ xprog γ0 γ ->
    PInv γ /\ SLInv Σ γ /\ XRootKeep γ0 γ.
  Proof.
    intros P0 S0 R; induction R as [γ|γ n ℓ γ1 γ2 Hin Hs R IH].
    - split; [exact P0 | split; [exact S0 | apply xrk_refl]].
    - destruct (xstep_inv γ γ1 n ℓ P0 S0 Hin Hs) as (P1 & S1 & K1).
      destruct (IH P1 S1) as (P2 & S2 & K2); split; [exact P2 | split; [exact S2 | exact (xrk_trans _ _ _ K1 K2)]].
  Qed.

  (** ** Final states, normalised *)
  Local Notation norm := (norm Σ xprog).
  Local Notation nfib := (nfib Σ xprog).
  Local Notation Final := (Final K_eq_dec Σ prog' Kb).

  Lemma rf2_norm (γ : State) : TInv γ -> RF2 γ (fun m => option_map (nfib γ) (fibers γ m)).
  Proof.
    intros T; split; [exact (rf_norm Σ xprog γ)|].
    intros m fm fm0 H H0 Hp; rewrite H0 in H; cbn in H; injection H as <-.
    destruct (fparent fm0) as [q|] eqn:Eq; [|contradiction].
    destruct (child_plain γ m fm0 q T H0 Eq) as [E1 E2].
    unfold OptState.nfib; destruct (is_installed (life fm0)); [reflexivity|].
    exact (plain_same γ fm0 E1 E2).
  Qed.

  Lemma spawns_base (γ : State) : TInv γ -> XSpawnProv Σ xprog γ.
  Proof.
    intros [_ _ [_ Sp] _ _] x f m fm Hx Hu Hm.
    destruct (Sp x f m fm Hx Hu Hm) as [Hs|Hr].
    - left; unfold Optional.prog' in Hs; cbn [body] in Hs; eexists; exact (spawnin_lift Σ _ _ Hs).
    - right; unfold Optional.prog' in Hr; cbn [reacts] in Hr.
      apply in_map_iff in Hr as (c & <- & Hc); exact Hc.
  Qed.

  Lemma xinv_tinv (γ : State) : TInv γ -> XInv K_eq_dec Σ xprog γ.
  Proof.
    intros T; pose proof T as [W P [U _] _ _]; split; auto; exact (spawns_base γ T).
  Qed.

  Lemma nfib_life (γ : State) f : life (nfib γ f) = life f.
  Proof. unfold OptState.nfib; destruct (is_installed (life f)); reflexivity. Qed.

  Lemma nfib_disposed (γ : State) f : disposed (nfib γ f) = disposed f.
  Proof. unfold OptState.nfib; destruct (is_installed (life f)); reflexivity. Qed.

  Lemma final_norm2 (γ : State) :
    PInv γ -> SLInv Σ γ -> xquiet K_eq_dec Σ xprog γ -> NoFailed Σ γ -> FinalS (norm γ).
  Proof.
    intros P SL Q NF.
    pose proof (pinv_tinv γ P) as T.
    destruct (xquiet_settled K_eq_dec Σ C_eq_dec xprog xrank Rb Hrank Hbnd γ (xinv_tinv γ T) Q) as [St _].
    split; [|exact (rf2_sl γ _ SL (rf2_norm γ T))].
    split; [exact (rf2_pinv γ _ P (rf2_norm γ T))|]; split.
    - intros n fm H; unfold OptState.norm in H; cbn [Calculus.fibers with_fibers] in H.
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate]; cbn in H; injection H as <-.
      pose proof (St n f Hn) as Sf; unfold settled_fiber in *.
      rewrite nfib_life, nfib_disposed, (target_norm K_eq_dec Σ xprog γ n f Hn).
      destruct (life f) as [[z|]|P0 acc w|acc w|acc w z] eqn:Hl; try exact Sf.
      + destruct Sf as [Hd _]; split; [exact Hd|]; rewrite Hd.
        unfold OptState.nfib; rewrite Hl; cbn [is_installed Calculus.comp].
        pose proof (Q n (LBegin n) ltac:(cbn; auto)) as Hq.
        cbn [Optional.xstep] in Hq; rewrite Hn, Hl in Hq; cbn [Calculus.step] in Hq.
        rewrite fibers_recomp, Nat.eqb_refl in Hq; cbn [Calculus.life] in Hq; rewrite Hl in Hq.
        unfold Calculus.target in Hq; rewrite fibers_recomp, Nat.eqb_refl in Hq.
        cbn [Calculus.disposed Calculus.comp] in Hq; rewrite Hd in Hq.
        rewrite (resolve_ext Σ _ γ _ (fun k => visible_recomp Σ xprog γ n f k Hn)) in Hq.
        destruct (resolve Σ γ _); [discriminate Hq | reflexivity].
      + unfold Calculus.target in Sf; rewrite Hn in Sf.
        unfold OptState.nfib; rewrite Hl; cbn [is_installed]; exact Sf.
    - intros n fm e H; unfold OptState.norm in H; cbn [Calculus.fibers with_fibers] in H.
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate]; cbn in H; injection H as <-.
      rewrite nfib_life; exact (NF n f e Hn).
  Qed.

  (** Every fiber's presence is current. *)
  Definition Fresh (γ : State) : Prop :=
    forall n f, fibers γ n = Some f -> snd (fcomp f) = present γ (fst (fcomp f)).

  Lemma present_norm (γ : State) c : present (norm γ) c = present γ c.
  Proof.
    unfold Optional.present; apply filter_ext; intros k; unfold is_visible, OptState.norm.
    rewrite (visible_rf Σ γ _ k (rf_norm Σ xprog γ)); reflexivity.
  Qed.

  Lemma fresh_norm (γ : State) :
    PInv γ -> xquiet K_eq_dec Σ xprog γ -> NoFailed Σ γ -> Fresh (norm γ).
  Proof.
    intros P Q NF n fm H.
    pose proof (pinv_tinv γ P) as T.
    destruct (xquiet_settled K_eq_dec Σ C_eq_dec xprog xrank Rb Hrank Hbnd γ (xinv_tinv γ T) Q) as [St Fr].
    rewrite present_norm.
    unfold OptState.norm in H; cbn [Calculus.fibers with_fibers] in H.
    destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate]; cbn in H; injection H as <-.
    destruct (settled_shape Σ prog' γ n f St NF Hn) as [_ [[Hl _]|(acc & w & Hl & _)]];
      unfold OptState.nfib; rewrite Hl; cbn [is_installed].
    - reflexivity.
    - pose proof (Fr n f acc w Hn Hl) as F; unfold Optional.fresh in F.
      destruct (list_eq_dec K_eq_dec (present γ (fst (fcomp f))) (snd (fcomp f))) as [E|];
        [symmetry; exact E | discriminate].
  Qed.

  (** ** Presence follows the correspondence at lower ranks *)
  Lemma vis_active (γ : State) k :
    CInv0 K_eq_dec Σ prog' Kb γ ->
    (is_visible Σ γ k = true <->
     exists m fm, fibers γ m = Some fm /\ is_active (life fm) = true /\ In k (provs Σ (prog' (fcomp fm)))).
  Proof.
    intros CI; pose proof (t_wf K_eq_dec Σ prog' Kb γ (c0_t _ _ _ _ _ CI)) as W.
    unfold is_visible, visible; split.
    - destruct (binds γ k) as [b|] eqn:Hb; [|discriminate].
      destruct (fibers γ (owner b)) as [fo|] eqn:Ho; [|discriminate].
      destruct (is_active (life fo)) eqn:Ha; [|discriminate]; intros _.
      destruct (wf_bind K_eq_dec Σ prog' γ W k b Hb) as (fo' & Ho' & _ & Hk & _).
      rewrite Ho in Ho'; injection Ho' as <-.
      exists (owner b), fo; repeat split; auto; exact (kmem_In K_eq_dec k _ Hk).
    - intros (m & fm & Hm & Ha & Hk).
      destruct (active_binds K_eq_dec Σ prog' Kb γ m fm k CI Hm Ha Hk) as (b & Hb & Ho).
      rewrite Hb, Ho, Hm, Ha; reflexivity.
  Qed.

  Local Notation Corresp := (Corresp K_eq_dec Σ prog' rank').

  Lemma vis_transfer la lb (γa γb : State) r c k :
    FinalS γa -> FinalS γb -> Corresp la lb γa γb r -> xrank c <= r -> In k (xopt c) ->
    is_visible Σ γa k = true -> is_visible Σ γb k = true.
  Proof.
    intros Fa Fb Cab Hr Hk Va.
    pose proof (p_s _ _ _ _ _ (proj1 (proj1 Fa))) as SIa; pose proof (p_s _ _ _ _ _ (proj1 (proj1 Fb))) as SIb.
    apply (vis_active γa k (s_c _ _ _ _ _ SIa)) in Va as (m & fm & Hm & Ham & Hp).
    assert (Hlt : rank' (fcomp fm) < r).
    { assert (HA : XAbove Σ xprog (fst (fcomp fm)) c) by (left; exists k; split; [exact Hp | right; exact Hk]).
      pose proof (Hrank _ _ HA); cbn; lia. }
    destruct (cn_total K_eq_dec Σ prog' Kb la γa m fm SIa (proj2 Fa) Hm) as [y Hy].
    destruct (Cab y m fm Hy Hm Hlt) as (nb & fb & _ & Hb & Hc & Hact & _).
    apply (vis_active γb k (s_c _ _ _ _ _ SIb)); exists nb, fb; rewrite Hc, Hact; auto.
  Qed.

  Lemma present_corr la lb (γa γb : State) r c :
    FinalS γa -> FinalS γb -> Corresp la lb γa γb r -> Corresp lb la γb γa r -> xrank c <= r ->
    present γa c = present γb c.
  Proof.
    intros Fa Fb Cab Cba Hr; unfold Optional.present; apply filter_ext_in; intros k Hk.
    destruct (is_visible Σ γa k) eqn:Va, (is_visible Σ γb k) eqn:Vb; try reflexivity.
    - rewrite (vis_transfer la lb γa γb r c k Fa Fb Cab Hr Hk Va) in Vb; discriminate.
    - rewrite (vis_transfer lb la γb γa r c k Fb Fa Cba Hr Hk Vb) in Va; discriminate.
  Qed.

  (** ** The rank induction, with roots matched by base component *)
  Definition RootsMatchX (la lb : nat -> nat) (γa γb : State) : Prop :=
    forall n fa, fibers γa n = Some fa -> fparent fa = None ->
      exists nb fb, fibers γb nb = Some fb /\ fparent fb = None /\ lb nb = la n /\
                    fst (fcomp fb) = fst (fcomp fa).

  Lemma corr_stepX la lb (γa γb : State) r :
    FinalS γa -> FinalS γb -> Fresh γa -> Fresh γb -> RootsMatchX la lb γa γb ->
    Corresp la lb γa γb r -> Corresp lb la γb γa r -> Corresp la lb γa γb (Datatypes.S r).
  Proof.
    intros Fa Fb Fra Frb RM IHab IHba x na fa CNa Ha Hr.
    assert (Hr' : rank' (fcomp fa) <= r) by (cbn in Hr |- *; lia).
    pose proof (p_s _ _ _ _ _ (proj1 (proj1 Fb))) as SIb.
    assert (Find : exists nb fb, CN Σ lb γb nb x /\ fibers γb nb = Some fb /\ fcomp fb = fcomp fa).
    { inversion CNa as [n f Hn Hp|n f p fp y j Hn Hp Hfp Hy Hj]; subst; rewrite Ha in Hn; injection Hn as <-.
      - destruct (RM na fa Ha Hp) as (nb & fb & Hfb & Hpb & Hl & Hcb).
        exists nb, fb; split; [rewrite <- Hl; exact (cn_root Σ lb γb nb fb Hfb Hpb)|]; split; [exact Hfb|].
        pose proof (Fra na fa Ha) as Ea; pose proof (Frb nb fb Hfb) as Eb.
        destruct (fcomp fa) as [ca sa], (fcomp fb) as [cb sb]; cbn in *; subst cb sa sb.
        f_equal; symmetry; exact (present_corr la lb γa γb r ca Fa Fb IHab IHba Hr').
      - destruct (final_fiber K_eq_dec Σ prog' Kb γa p fp (proj1 Fa) Hfp) as [E|(accp & wp & evp & Lp & Tp & Cp)].
        { unfold SpawnAt in Hj; rewrite E in Hj; cbn in Hj; destruct j; discriminate. }
        unfold SpawnAt in Hj; rewrite Lp in Hj; cbn [acc_of] in Hj.
        destruct (f2_nth _ _ _ j na (f2_rev _ _ _ (corr_f2 _ _ _ _ _ _ _ _ Cp)) Hj) as (c' & Hc' & Hca).
        pose proof (Hca fa Ha) as Ec.
        assert (Hsp : SpawnIn Σ c' (body Σ (prog' (fcomp fp)))).
        { apply (tr_spawnin K_eq_dec Σ prog' _ _ _ _ c' Tp); apply (proj2 (in_rev _ _)); exact (nth_error_In _ _ Hc'). }
        assert (Hrp : rank' (fcomp fp) < r).
        { pose proof (Hrank2 (fcomp fp) c' (or_intror (or_introl Hsp))); rewrite <- Ec in *; lia. }
        destruct (IHab y p fp Hy Hfp Hrp) as (pb & fpb & CNpb & Hfpb & Hcpb & Hapb & Hevp).
        rewrite Lp in Hapb; cbn in Hapb.
        destruct (final_fiber K_eq_dec Σ prog' Kb γb pb fpb (proj1 Fb) Hfpb) as [E|(accpb & wpb & evpb & Lpb & Tpb & Cpb)];
          [rewrite E in Hapb; discriminate|].
        pose proof (Hevp accp wp evp accpb wpb evpb Lp Lpb Tp Cp Tpb Cpb) as Eev.
        rewrite Eev in Hc'.
        destruct (f2_nth_r _ _ _ j c' (f2_rev _ _ _ (corr_f2 _ _ _ _ _ _ _ _ Cpb)) Hc') as (nb & Hnb & Hcb).
        assert (Inb : In nb (spawns Σ (acc_of (life fpb)))).
        { rewrite Lpb; apply (proj2 (in_rev _ _)); exact (nth_error_In _ _ Hnb). }
        destruct (sl_live _ _ (proj2 Fb) pb fpb nb Hfpb Inb) as [(a1 & w1 & z1 & E)|(fb & Hfb & _)];
          [rewrite Lpb in E; discriminate|].
        pose proof (t_so K_eq_dec Σ prog' Kb γb (c0_t K_eq_dec Σ prog' Kb γb (s_c _ _ _ _ _ SIb)) pb fpb nb fb Hfpb
                      (proj1 (in_spawns _ _ _) Inb) Hfb) as Hpar.
        exists nb, fb; split; [|split; [exact Hfb | rewrite (Hcb fb Hfb); exact (eq_sym Ec)]].
        apply (cn_child Σ lb γb nb fb pb fpb y j Hfb Hpar Hfpb CNpb); unfold SpawnAt; rewrite Lpb; exact Hnb. }
    destruct Find as (nb & fb & CNb & Hb & Hc).
    destruct (corr_pair K_eq_dec Σ prog' Kb rank' Hrank2 Hwb la lb γa γb r na fa nb fb Fa Fb IHab IHba Ha Hb Hc Hr')
      as [Hact Htr].
    exists nb, fb; auto.
  Qed.

  Lemma corresp_allX l1 l2 (γ1 γ2 : State) :
    FinalS γ1 -> FinalS γ2 -> Fresh γ1 -> Fresh γ2 ->
    RootsMatchX l1 l2 γ1 γ2 -> RootsMatchX l2 l1 γ2 γ1 ->
    forall r, Corresp l1 l2 γ1 γ2 r /\ Corresp l2 l1 γ2 γ1 r.
  Proof.
    intros F1 F2 Fr1 Fr2 R12 R21 r; induction r as [|r [IH12 IH21]].
    - split; intros x na fa _ _ Hr; lia.
    - split; [exact (corr_stepX l1 l2 γ1 γ2 r F1 F2 Fr1 Fr2 R12 IH12 IH21)
             | exact (corr_stepX l2 l1 γ2 γ1 r F2 F1 Fr2 Fr1 R21 IH21 IH12)].
  Qed.

  (** ** Two final states with matching roots agree up to renaming *)
  Local Notation CoPair_sym := (Recovery.CoPair_sym Σ prog').

  Theorem final_agreeX l1 l2 (γ1 γ2 : State) :
    FinalS γ1 -> FinalS γ2 -> Fresh γ1 -> Fresh γ2 -> RootInj Σ l1 γ1 -> RootInj Σ l2 γ2 ->
    RootsMatchX l1 l2 γ1 γ2 -> RootsMatchX l2 l1 γ2 γ1 ->
    AgreeL Σ l1 l2 γ1 γ2.
  Proof.
    intros F1 F2 Fr1 Fr2 RI1 RI2 RM12 RM21; unfold AgreeL.
    pose proof (proj2 F1) as S1; pose proof (proj2 F2) as S2.
    pose proof (proj1 (proj1 F1)) as P1; pose proof (proj1 (proj1 F2)) as P2.
    destruct (corresp_allX l1 l2 γ1 γ2 F1 F2 Fr1 Fr2 RM12 RM21 (Datatypes.S Rb)) as [C12 C21].
    assert (Hr : forall c : CC, rank' c < Datatypes.S Rb) by (intros c; pose proof (Hbnd (fst c)); cbn; lia).
    pose proof (p_s _ _ _ _ _ P1) as SI1; pose proof (p_s _ _ _ _ _ P2) as SI2.
    pose proof (sinv_wf _ _ _ _ _ SI1) as W1; pose proof (sinv_wf _ _ _ _ _ SI2) as W2.
    assert (Own : forall la lb (γa γb : State) (Fa : FinalS γa) (Fb : FinalS γb),
              Corresp la lb γa γb (Datatypes.S Rb) ->
              forall k ba x, binds γa k = Some ba -> CN Σ la γa (owner ba) x ->
              exists bb, binds γb k = Some bb /\ CN Σ lb γb (owner bb) x).
    { intros la lb γa γb Fa Fb Cab k ba x Hba Hx.
      pose proof (p_s _ _ _ _ _ (proj1 (proj1 Fa))) as SIa; pose proof (p_s _ _ _ _ _ (proj1 (proj1 Fb))) as SIb.
      destruct (wf_bind K_eq_dec Σ prog' γa (sinv_wf _ _ _ _ _ SIa) k ba Hba) as (fo & Hfo & _ & Hkp & Hup).
      destruct (final_fiber K_eq_dec Σ prog' Kb γa _ fo (proj1 Fa) Hfo) as [E|(acc & w & evs & Lo & _ & _)];
        [rewrite E in Hup; destruct Hup|].
      destruct (Cab x _ fo Hx Hfo (Hr _)) as (ob & fob & CNb & Hfob & Hc & Ha & _).
      rewrite Lo in Ha; cbn in Ha.
      assert (Hkb : In k (provs Σ (prog' (fcomp fob)))) by (rewrite Hc; exact (kmem_In K_eq_dec k _ Hkp)).
      pose proof (proj2 (owner_iff K_eq_dec Σ prog' Kb γb k ob (s_c _ _ _ _ _ SIb) (proj1 (proj2 (proj1 Fb)))
                           (proj2 (proj2 (proj1 Fb)))) (ex_intro _ fob (conj Hfob (conj Ha Hkb)))) as E.
      destruct (binds γb k) as [bb|]; [|discriminate]; injection E as E.
      exists bb; split; [reflexivity | rewrite E; exact CNb]. }
    split; [intros n f H; exact (cn_total K_eq_dec Σ prog' Kb l1 γ1 n f SI1 S1 H)|].
    split; [intros n f H; exact (cn_total K_eq_dec Σ prog' Kb l2 γ2 n f SI2 S2 H)|].
    split; [intros n x x'; exact (cn_fun Σ l1 γ1 n x x' S1)|].
    split; [intros n x x'; exact (cn_fun Σ l2 γ2 n x x' S2)|].
    split.
    { intros x n1 f1 Hx H1; destruct (C12 x n1 f1 Hx H1 (Hr _)) as (n2 & f2 & A & B & C' & D & _).
      exists n2, f2; auto. }
    split.
    { intros x n2 f2 Hx H2; destruct (C21 x n2 f2 Hx H2 (Hr _)) as (n1 & f1 & A & B & C' & D & _).
      exists n1, f1; auto. }
    split; [exact (Own l1 l2 γ1 γ2 F1 F2 C12)|].
    split; [exact (Own l2 l1 γ2 γ1 F2 F1 C21)|].
    intros k b1 b2 Hb1 Hb2.
    destruct (s_inv _ _ _ _ _ SI1 k b1 Hb1) as (s01 & L1 & s1 & Hi1 & PL1 & Rp1 & E1).
    destruct (s_inv _ _ _ _ _ SI2 k b2 Hb2) as (s02 & L2 & s2 & Hi2 & PL2 & Rp2 & E2).
    destruct (wf_bind K_eq_dec Σ prog' γ1 W1 k b1 Hb1) as (fo1 & Hfo1 & _ & _ & Hup1).
    destruct (wf_bind K_eq_dec Σ prog' γ2 W2 k b2 Hb2) as (fo2 & Hfo2 & _ & _ & Hup2).
    destruct (cn_total K_eq_dec Σ prog' Kb l1 γ1 _ fo1 SI1 S1 Hfo1) as [x Hx].
    destruct (Own l1 l2 γ1 γ2 F1 F2 C12 k b1 x Hb1 Hx) as (b2' & Hb2' & Hx2).
    rewrite Hb2 in Hb2'; injection Hb2' as <-.
    destruct (C12 x _ fo1 Hx Hfo1 (Hr _)) as (o2 & fo2' & CN2 & Hfo2' & Hc0 & Ha0 & Htr).
    rewrite <- (cn_inj Σ l2 γ2 _ _ x RI2 Hx2 CN2) in Hfo2'; rewrite Hfo2 in Hfo2'; injection Hfo2' as <-.
    destruct (final_fiber K_eq_dec Σ prog' Kb γ1 _ fo1 (proj1 F1) Hfo1) as [E|(acc1 & w1 & evs1 & L1' & T1 & C1)];
      [rewrite E in Hup1; destruct Hup1|].
    destruct (final_fiber K_eq_dec Σ prog' Kb γ2 _ fo2 (proj1 F2) Hfo2) as [E|(acc2 & w2 & evs2 & L2' & T2 & C2)];
      [rewrite E in Hup2; destruct Hup2|].
    pose proof (Htr acc1 w1 evs1 acc2 w2 evs2 L1' L2' T1 C1 T2 C2) as Eev.
    pose proof (wf_uprov_unique K_eq_dec Σ prog' γ1 W1 _ fo1 Hfo1) as U1; rewrite L1' in U1, Hup1.
    pose proof (wf_uprov_unique K_eq_dec Σ prog' γ2 W2 _ fo2 Hfo2) as U2; rewrite L2' in U2, Hup2.
    destruct (corr_find K_eq_dec Σ prog' γ1 _ w1 acc1 evs1 k (pid Σ b1) C1 U1 Hup1) as (s1' & Hi1' & Hf1).
    destruct (corr_find K_eq_dec Σ prog' γ2 _ w2 acc2 evs2 k (pid Σ b2) C2 U2 Hup2) as (s2' & Hi2' & Hf2).
    assert (s02 = s01) by (rewrite Eev in Hf1; congruence); subst s02.
    destruct (final_blocks K_eq_dec Σ prog' Kb Hwb HCom γ1 k b1 L1 (Calculus.next Σ γ1) s01 s1 (proj1 F1) (le_n _) Hb1 PL1 Rp1)
      as (x1 & X1 & Ex1).
    destruct (final_blocks K_eq_dec Σ prog' Kb Hwb HCom γ2 k b2 L2 (Calculus.next Σ γ2) s01 s2 (proj1 F2) (le_n _) Hb2 PL2 Rp2)
      as (x2 & X2 & Ex2).
    assert (EM : Permutation (filter nonnil (map (map fst) (map (blockAt K_eq_dec Σ γ1 k) (seq 0 (Calculus.next Σ γ1)))))
                             (filter nonnil (map (map fst) (map (blockAt K_eq_dec Σ γ2 k) (seq 0 (Calculus.next Σ γ2)))))).
    { rewrite !map_map.
      apply (perm_bij_blocks _ _ (fun a b => exists x, CN Σ l1 γ1 a x /\ CN Σ l2 γ2 b x));
        [apply seq_NoDup | apply seq_NoDup | | | | |].
      - intros a _; unfold blockAt, itemsAt; destruct (fibers γ1 a) as [fa|] eqn:Ha; [|left; reflexivity].
        right; destruct (cn_total K_eq_dec Σ prog' Kb l1 γ1 a fa SI1 S1 Ha) as [y Hy].
        destruct (C12 y a fa Hy Ha (Hr _)) as (b & fb & Hyb & Hb & _).
        exists b; split; [apply in_seq; pose proof (wf_names K_eq_dec Σ prog' γ2 W2 b fb Hb); lia | exists y; auto].
      - intros b _; unfold blockAt, itemsAt; destruct (fibers γ2 b) as [fb|] eqn:Hb; [|left; reflexivity].
        right; destruct (cn_total K_eq_dec Σ prog' Kb l2 γ2 b fb SI2 S2 Hb) as [y Hy].
        destruct (C21 y b fb Hy Hb (Hr _)) as (a & fa & Hya & Ha & _).
        exists a; split; [apply in_seq; pose proof (wf_names K_eq_dec Σ prog' γ1 W1 a fa Ha); lia | exists y; auto].
      - intros a b b' (y & Ha & Hb) (y' & Ha' & Hb').
        rewrite (cn_fun Σ l1 γ1 a y y' S1 Ha Ha') in Hb; exact (cn_inj Σ l2 γ2 b b' y' RI2 Hb Hb').
      - intros a a' b (y & Ha & Hb) (y' & Ha' & Hb').
        rewrite (cn_fun Σ l2 γ2 b y y' S2 Hb Hb') in Ha; exact (cn_inj Σ l1 γ1 a a' y' RI1 Ha Ha').
      - intros a b (y & Ha & Hb).
        destruct (cn_present Σ l1 γ1 a y Ha) as [fa Hfa]; destruct (cn_present Σ l2 γ2 b y Hb) as [fb Hfb].
        destruct (C12 y a fa Ha Hfa (Hr _)) as (b' & fb' & Hb' & Hfb' & _ & Hact & Htr').
        rewrite <- (cn_inj Σ l2 γ2 _ _ y RI2 Hb Hb') in Hfb'; rewrite Hfb in Hfb'; injection Hfb' as <-.
        unfold blockAt, itemsAt; rewrite Hfa, Hfb, !map_rev; f_equal.
        destruct (final_fiber K_eq_dec Σ prog' Kb γ1 a fa (proj1 F1) Hfa) as [Ea|(acca & wa & evsa & La & Ta & Ca)];
          destruct (final_fiber K_eq_dec Σ prog' Kb γ2 b fb (proj1 F2) Hfb) as [Eb|(accb & wb & evsb & Lb & Tb & Cb)].
        + unfold uacc; rewrite Ea, Eb; reflexivity.
        + rewrite Ea, Lb in Hact; discriminate.
        + rewrite La, Eb in Hact; discriminate.
        + unfold uacc; rewrite La, Lb; cbn [acc_of].
          rewrite (corr_ops K_eq_dec Σ prog' γ1 _ _ _ _ k Ca), (corr_ops K_eq_dec Σ prog' γ2 _ _ _ _ k Cb); f_equal.
          exact (Htr' acca wa evsa accb wb evsb La Lb Ta Ca Tb Cb). }
    pose proof (replay_blocks (CoPair Σ prog' k) Hwb HTI (CoPair_sym k) (HCom k) _ _ s01 x1 x2
                  (blocks_cross K_eq_dec Σ prog' Kb γ1 k _ SI1 (seq_NoDup _ _)) EM X1 X2) as Es.
    transitivity s1; [exact E1|]; transitivity x1; [exact Ex1|]; transitivity x2; [exact Es|].
    transitivity s2; symmetry; assumption.
  Qed.

  (** ** Confluence with spawn *)
  Lemma roots_matchX (γ0 γ1 γ2 : State) :
    XRootKeep γ0 γ1 -> XRootKeep γ0 γ2 -> Final γ1 ->
    RootsMatchX (fun n => n) (fun n => n) γ1 γ2.
  Proof.
    intros [A1 _] [A2 B2] F1 n fa Ha Hp.
    destruct (A1 n fa Ha Hp) as (f0 & H0 & P0 & C0 & D0).
    destruct (settled_shape Σ prog' γ1 n fa (proj1 (proj2 F1)) (proj2 (proj2 F1)) Ha) as [Hd _].
    destruct (B2 n f0 H0 P0 ltac:(congruence)) as (fb & Hb & Pb & _).
    destruct (A2 n fb Hb Pb) as (f0' & H0' & _ & C0' & _).
    rewrite H0 in H0'; injection H0' as <-.
    exists n, fb; split; [exact Hb|]; split; [exact Pb | split; [reflexivity | congruence]].
  Qed.

  (** Two extended lifecycle runs from a common state, ending quiet with no
      failure, agree up to renaming once the stale presence of their
      Inactive fibers is normalised ([norm] changes nothing else: the
      bindings, parents, lives and base components stay as they are). *)
  Theorem xspawn_confluence (γ0 γ1 γ2 : State) :
    PInv γ0 -> SLInv Σ γ0 ->
    XLRun K_eq_dec Σ xprog γ0 γ1 -> XLRun K_eq_dec Σ xprog γ0 γ2 ->
    xquiet K_eq_dec Σ xprog γ1 -> xquiet K_eq_dec Σ xprog γ2 ->
    NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    Agree Σ (norm γ1) (norm γ2).
  Proof.
    intros P0 S0 R1 R2 Q1 Q2 NF1 NF2.
    destruct (xlrun_inv γ0 γ1 P0 S0 R1) as (P1 & S1 & K1).
    destruct (xlrun_inv γ0 γ2 P0 S0 R2) as (P2 & S2 & K2).
    pose proof (final_norm2 γ1 P1 S1 Q1 NF1) as F1; pose proof (final_norm2 γ2 P2 S2 Q2 NF2) as F2.
    pose proof (fresh_norm γ1 P1 Q1 NF1) as Fr1; pose proof (fresh_norm γ2 P2 Q2 NF2) as Fr2.
    pose proof (xrk_trans _ _ _ K1 (xrk_rf γ1 _ (rf_norm Σ xprog γ1))) as K1'.
    pose proof (xrk_trans _ _ _ K2 (xrk_rf γ2 _ (rf_norm Σ xprog γ2))) as K2'.
    assert (RI : forall γ : State, RootInj Σ (fun n => n) γ) by (intros γ n n' f f' _ _ _ _ E; exact E).
    exact (final_agreeX _ _ (norm γ1) (norm γ2) F1 F2 Fr1 Fr2 (RI _) (RI _)
             (roots_matchX γ0 _ _ K1' K2' (proj1 F1)) (roots_matchX γ0 _ _ K2' K1' (proj1 F2))).
  Qed.
End OptSpawn.
