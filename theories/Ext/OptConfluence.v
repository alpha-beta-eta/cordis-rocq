(** * Extension 1: confluence of control states with optional dependencies

    Counterpart of [Confluence.control_confluence] (components that spawn
    nothing). From a common state, two extended executions of lifecycle
    steps that end quiet with no fiber failed leave
    - the same fibers present, with the same base components;
    - the same of them Active;
    - every key provided by the same fiber;
    - every Active fiber running the same variant: its chosen presence is
      the same set of optional keys in both.

    The last point is what optional dependencies add. It follows from the
    others: at a quiet extended state an Active fiber's presence is current
    ([OptProgress.xquiet_settled]), and current presence is read off which
    keys are bound by Active fibers.

    The proof reuses the core's analysis of settled states
    ([Confluence.active_iff], [owner_iff], [settled_shape]) for the table
    [prog'], and the core invariant [CInv] and [lstep_static] for the core
    steps an extended run is made of ([xstep_core]). What is new:
    - [CInv] and the domain of fibers survive the two non-core moves
      (re-choosing presence, and the restart on a presence change);
    - activity is decided by the required dependencies alone, so the
      fixpoint equation is over base components, where the presence of an
      Inactive fiber (possibly stale) plays no part: a fiber whose required
      dependencies are all provided by Active fibers would be begun by
      [X-Begin], which is not possible at a quiet state. *)

From Stdlib Require Import List PeanoNat Bool Lia Wf_nat.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Recovery
  Progress Termination Confluence.
From Cordis Require Import Ext.Optional Ext.OptProgress.
Import ListNotations.

Section OptConfluence.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (C_eq_dec : forall x y : C, {x = y} + {x <> y}).
  Context (xprog : C -> @XComponent K Σ C).

  Local Notation CC := (@Optional.C' K C).
  Local Notation State := (@State K Σ CC).
  Local Notation Fiber := (@Fiber K Σ CC).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation disposed := (Calculus.disposed Σ).
  Local Notation is_active := (is_active Σ).
  Local Notation owner := (owner Σ).
  Local Notation acc_of := (acc_of Σ).
  Local Notation prog' := (prog' K_eq_dec Σ xprog).
  Local Notation step := (step K_eq_dec Σ prog').
  Local Notation xstep := (xstep K_eq_dec Σ xprog).
  Local Notation fresh := (fresh K_eq_dec Σ xprog).
  Local Notation recomp := (recomp Σ xprog).
  Local Notation present := (present Σ xprog).
  Local Notation xdeps c := (xdeps Σ (xprog c)).
  Local Notation xprovs c := (xprovs Σ (xprog c)).

  (** ** Hypotheses, on base components *)
  Variable Kb : nat.
  Hypothesis xHK : forall c T, Bounded Σ Kb (xbody Σ (xprog c) T).
  Variable xrank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', XAbove Σ xprog c c' -> xrank c < xrank c'.
  Hypothesis Hbnd : forall c, xrank c <= Rb.
  Hypothesis xNoSpawn : forall c T c', ~ SpawnIn Σ c' (xbody Σ (xprog c) T).
  (** Every variant provides every key the component may provide. *)
  Hypothesis xTotal : forall c T k, In k (xprovs c) -> AllDoneProv Σ k (xbody Σ (xprog c) T).

  (** ** The core hypotheses for [prog'] *)
  Lemma bounded_lift j (P : @Prog K Σ C) : Bounded Σ j P -> Bounded Σ j (lift Σ P).
  Proof.
    intros H; induction H; cbn; constructor; auto.
  Qed.

  Lemma adp_lift k (P : @Prog K Σ C) : AllDoneProv Σ k P -> AllDoneProv Σ k (lift Σ P).
  Proof.
    intros H; induction H; cbn; constructor; auto.
  Qed.

  Lemma HK' : forall x, Bounded Σ Kb (body Σ (prog' x)).
  Proof. intros x; apply bounded_lift, xHK. Qed.

  Lemma NoSpawn' : forall x y, ~ SpawnIn Σ y (body Σ (prog' x)).
  Proof.
    intros x y H; apply (xNoSpawn (fst x) (fun k => kmem K_eq_dec k (snd x)) (fst y)).
    exact (spawnin_lift Σ y _ H).
  Qed.

  Lemma Total' : forall x k, In k (provs Σ (prog' x)) -> AllDoneProv Σ k (body Σ (prog' x)).
  Proof. intros x k Hk; apply adp_lift, xTotal; exact Hk. Qed.

  Lemma Hrank' : forall x y, Above Σ prog' x y -> xrank (fst x) < xrank (fst y).
  Proof.
    intros x y [(k & Hp & Hd)|[Hs|Hr]]; apply Hrank.
    - left; exists k; split; [exact Hp|].
      unfold Optional.prog' in Hd; cbn [deps] in Hd.
      apply in_app_or in Hd as [Hd|Hd]; [left; exact Hd|].
      right; apply filter_In in Hd as [_ Hd].
      unfold kmem, keqb in Hd; apply existsb_exists in Hd as (k' & Hk' & E).
      destruct (K_eq_dec k k') as [->|]; [exact Hk' | discriminate].
    - exfalso; exact (NoSpawn' x y Hs).
    - right; right; unfold Optional.prog' in Hr; cbn [reacts] in Hr.
      apply in_map_iff in Hr as (c & <- & Hc); exact Hc.
  Qed.

  Local Notation CInv := (CInv K_eq_dec Σ prog' Kb).
  Local Notation cinv_step := (cinv_step K_eq_dec Σ prog' Kb HK' NoSpawn' Total').
  Local Notation lstep_static :=
    (lstep_static K_eq_dec Σ prog' Kb (fun x => xrank (fst x)) Hrank' NoSpawn').

  (** ** The two non-core moves keep [CInv] *)
  Lemma cinv_recomp (γ : State) n f :
    CInv γ -> fibers γ n = Some f -> life f = Inactive Σ None -> CInv (recomp γ n f).
  Proof.
    intros [[W P [U Sp] LB SO] PI NS] Hn Hl.
    assert (Hi : is_installed Σ (life f) = false) by (rewrite Hl; reflexivity).
    assert (Hb : forall m fm, fibers (recomp γ n f) m = Some fm ->
                 (m = n /\ life fm = Inactive Σ None) \/ (m <> n /\ fibers γ m = Some fm)).
    { intros m fm H; rewrite fibers_recomp in H.
      destruct (Nat.eqb_spec m n) as [->|Hne]; [injection H as <-; left; auto|right; auto]. }
    assert (Hacc : forall m fm, fibers (recomp γ n f) m = Some fm ->
                   exists fm0, fibers γ m = Some fm0 /\ life fm = life fm0).
    { intros m fm H; rewrite fibers_recomp in H.
      destruct (Nat.eqb_spec m n) as [->|]; [injection H as <-; exists f; auto|eauto]. }
    pose proof (xinv_recomp K_eq_dec Σ xprog γ n f
                  (Build_XInv K_eq_dec Σ xprog γ W P U
                     (fun x fx m fm Hx Hu Hm => False_ind _ (NS x fx m Hx Hu))) Hn Hi)
      as [W' P' U' _].
    split; [split|..].
    - exact W'.
    - exact P'.
    - split; [exact U'|].
      intros x fx m fm Hx Hu; destruct (Hacc x fx Hx) as (fx0 & Hx0 & E).
      rewrite E in Hu; destruct (NS x fx0 m Hx0 Hu).
    - intros m fm P0 acc w Hm Hlm; destruct (Hb m fm Hm) as [[_ E]|[_ Hm0]].
      + rewrite E in Hlm; discriminate.
      + exact (LB m fm P0 acc w Hm0 Hlm).
    - intros x fx m fm Hx Hu; destruct (Hacc x fx Hx) as (fx0 & Hx0 & E).
      rewrite E in Hu; destruct (NS x fx0 m Hx0 Hu).
    - intros m fm Hm; destruct (Hb m fm Hm) as [[_ E]|[_ Hm0]].
      + unfold PIF; rewrite E; exact I.
      + exact (PI m fm Hm0).
    - intros x fx m Hx Hu; destruct (Hacc x fx Hx) as (fx0 & Hx0 & E).
      rewrite E in Hu; exact (NS x fx0 m Hx0 Hu).
  Qed.

  (** ** Fibers and base components stay put *)
  Definition XStatic (γ0 γ : State) : Prop :=
    (forall m fm, fibers γ m = Some fm ->
       exists f0, fibers γ0 m = Some f0 /\ fst (fcomp fm) = fst (fcomp f0) /\
                  disposed fm = disposed f0) /\
    (forall m f0, fibers γ0 m = Some f0 -> disposed f0 = false -> exists fm, fibers γ m = Some fm).

  Lemma xstatic_refl (γ : State) : XStatic γ γ.
  Proof. split; [intros m fm H; exists fm; auto | intros m f0 H _; eauto]. Qed.

  Lemma xstatic_trans (γ0 γ1 γ2 : State) : XStatic γ0 γ1 -> XStatic γ1 γ2 -> XStatic γ0 γ2.
  Proof.
    intros [S1 S2] [T1 T2]; split.
    - intros m fm H; destruct (T1 m fm H) as (f1 & H1 & Hc1 & Hd1).
      destruct (S1 m f1 H1) as (f0 & H0 & Hc0 & Hd0).
      exists f0; split; [exact H0 | split; congruence].
    - intros m f0 H0 Hd; destruct (S2 m f0 H0 Hd) as [f1 H1].
      destruct (S1 m f1 H1) as (f0' & H0' & _ & Hd1).
      rewrite H0 in H0'; injection H0' as <-.
      apply (T2 m f1 H1); congruence.
  Qed.

  Lemma static_x (γ0 γ : State) : Static Σ γ0 γ -> XStatic γ0 γ.
  Proof.
    intros [S1 S2]; split; [|exact S2].
    intros m fm H; destruct (S1 m fm H) as (f0 & H0 & Hc & Hd); exists f0; rewrite Hc; auto.
  Qed.

  Lemma xstatic_recomp (γ : State) n f : fibers γ n = Some f -> XStatic γ (recomp γ n f).
  Proof.
    intros Hn; split.
    - intros m fm H; rewrite fibers_recomp in H.
      destruct (Nat.eqb_spec m n) as [->|]; [injection H as <-; exists f; auto|exists fm; auto].
    - intros m f0 H _; rewrite fibers_recomp.
      destruct (Nat.eqb_spec m n); [eauto|eauto].
  Qed.

  Lemma xstatic_restart (γ γ' : State) n : step γ (ORestart n) = Some γ' -> XStatic γ γ'.
  Proof.
    intros H; destruct (restart_shape K_eq_dec Σ prog' γ γ' n H) as (f & acc & w & Hn & _ & _ & ->).
    split.
    - intros m fm Hm; cbn [set_life set_fiber with_fibers Calculus.fibers] in Hm; unfold fupd in Hm.
      destruct (Nat.eqb_spec m n) as [->|]; [injection Hm as <-; exists f; auto|exists fm; auto].
    - intros m f0 H0 _; cbn [set_life set_fiber with_fibers Calculus.fibers]; unfold fupd.
      destruct (Nat.eqb_spec m n); eauto.
  Qed.

  (** ** Extended lifecycle runs *)
  Inductive XLRun : State -> State -> Prop :=
  | xlr_nil γ : XLRun γ γ
  | xlr_cons γ n ℓ γ1 γ2 : In ℓ (@lifecycle_labels C n) -> xstep γ ℓ = Some γ1 -> XLRun γ1 γ2 ->
                           XLRun γ γ2.

  Lemma xlab_lifecycle n ℓ : In ℓ (@lifecycle_labels C n) -> is_lifecycle (@xlab K C ℓ).
  Proof.
    intros Hin; exists n; cbn in Hin |- *.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn; tauto.
  Qed.

  Lemma not_react_lc n ℓ : In ℓ (@lifecycle_labels CC n) -> forall m i, ℓ <> OReact m i.
  Proof. intros Hin m i E; subst ℓ; cbn in Hin; intuition discriminate. Qed.

  Lemma xstep_cinv (γ γ' : State) n ℓ :
    CInv γ -> In ℓ (@lifecycle_labels C n) -> xstep γ ℓ = Some γ' -> CInv γ' /\ XStatic γ γ'.
  Proof.
    intros I Hin H.
    destruct (xstep_core K_eq_dec Σ xprog γ γ' ℓ H)
      as [S|[(m & f & _ & Hm & Hl & S)|(m & S)]].
    - pose proof (xlab_lifecycle n ℓ Hin) as Hlc.
      split; [exact (cinv_step γ γ' _ (lifecycle_not_react _ Hlc) I S)|].
      exact (static_x γ γ' (lstep_static γ γ' _ I Hlc S)).
    - pose proof (cinv_recomp γ m f I Hm Hl) as Ir.
      assert (Hlc : is_lifecycle (@LBegin CC m)) by (exists m; cbn; auto).
      split; [exact (cinv_step _ γ' _ (lifecycle_not_react _ Hlc) Ir S)|].
      exact (xstatic_trans _ _ _ (xstatic_recomp γ m f Hm)
                           (static_x _ _ (lstep_static _ γ' _ Ir Hlc S))).
    - assert (NR : forall a b, @ORestart CC m <> OReact a b) by (intros a b E; discriminate E).
      split; [exact (cinv_step γ γ' _ NR I S)|].
      exact (xstatic_restart γ γ' m S).
  Qed.

  Lemma xlrun_cinv (γ0 γ : State) : CInv γ0 -> XLRun γ0 γ -> CInv γ /\ XStatic γ0 γ.
  Proof.
    intros I0 R; induction R as [γ|γ n ℓ γ1 γ2 Hin Hs R IH].
    - split; [exact I0 | apply xstatic_refl].
    - destruct (xstep_cinv γ γ1 n ℓ I0 Hin Hs) as [I1 S1].
      destruct (IH I1) as [I2 S2]; split; [exact I2 | exact (xstatic_trans _ _ _ S1 S2)].
  Qed.

  (** ** Final states *)
  Lemma xinv_of (γ : State) : CInv γ -> XInv K_eq_dec Σ xprog γ.
  Proof.
    intros [[W P [U _] _ _] _ NS]; split; auto.
    intros x fx m fm Hx Hu; destruct (NS x fx m Hx Hu).
  Qed.

  Lemma final_settled (γ : State) :
    CInv γ -> xquiet K_eq_dec Σ xprog γ ->
    settled Σ prog' γ /\
    (forall n f acc w, fibers γ n = Some f -> life f = Active Σ acc w -> fresh γ f = true).
  Proof.
    intros I Q.
    exact (xquiet_settled K_eq_dec Σ C_eq_dec xprog xrank Rb
             (fun c c' H => Hrank c c' H) Hbnd γ (xinv_of γ I) Q).
  Qed.

  Lemma active_visible (γ : State) m fm k :
    CInv γ -> fibers γ m = Some fm -> is_active (life fm) = true -> In k (provs Σ (prog' (fcomp fm))) ->
    exists p, visible Σ γ k = Some p.
  Proof.
    intros I Hm Ha Hk.
    destruct (active_binds K_eq_dec Σ prog' Kb γ m fm k (cinv_0 _ _ _ _ _ I) Hm Ha Hk) as (b & Hb & Ho).
    exists (pid Σ b); unfold visible; rewrite Hb, Ho, Hm, Ha; reflexivity.
  Qed.

  (** At a quiet extended state with no failure, a fiber is Active iff
      every required dependency is provided by an Active fiber. *)
  Lemma xactive_iff (γ : State) n f :
    CInv γ -> xquiet K_eq_dec Σ xprog γ -> NoFailed Σ γ -> fibers γ n = Some f ->
    (is_active (life f) = true <->
     forall k, In k (xdeps (fst (fcomp f))) ->
       exists m fm, fibers γ m = Some fm /\ is_active (life fm) = true /\
                    In k (xprovs (fst (fcomp fm)))).
  Proof.
    intros I Q NF Hn.
    destruct (final_settled γ I Q) as [St _].
    pose proof (active_iff K_eq_dec Σ prog' Kb γ n f (cinv_0 _ _ _ _ _ I) St NF Hn) as A.
    split.
    - intros Ha k Hk; apply (proj1 A Ha k).
      unfold Optional.prog'; cbn [deps]; apply in_or_app; left; exact Hk.
    - intros Hall.
      destruct (settled_shape Σ prog' γ n f St NF Hn) as [Hd [[Hl _]|(acc & w & Hl & _)]];
        [exfalso|rewrite Hl; reflexivity].
      (* X-Begin would apply *)
      assert (Hv : forall k, In k (deps Σ (prog' (fst (fcomp f), present γ (fst (fcomp f))))) ->
                   exists p, visible Σ (recomp γ n f) k = Some p).
      { intros k Hk; rewrite (visible_recomp Σ xprog γ n f k Hn).
        unfold Optional.prog' in Hk; cbn [deps fst snd] in Hk.
        apply in_app_or in Hk as [Hk|Hk].
        - destruct (Hall k Hk) as (m & fm & Hm & Ha & Hp).
          exact (active_visible γ m fm k I Hm Ha Hp).
        - apply filter_In in Hk as [Hk _]; unfold Optional.present in Hk.
          apply filter_In in Hk as [_ Hk]; unfold is_visible in Hk.
          destruct (visible Σ γ k); [eauto | discriminate]. }
      destruct (resolve_some Σ (recomp γ n f) _ Hv) as [w Hw].
      pose proof (Q n (LBegin n) ltac:(cbn; auto)) as Hq.
      cbn [Optional.xstep] in Hq; rewrite Hn, Hl in Hq; cbn [Calculus.step] in Hq.
      rewrite fibers_recomp, Nat.eqb_refl in Hq; cbn [Calculus.life] in Hq; rewrite Hl in Hq.
      unfold Calculus.target in Hq; rewrite fibers_recomp, Nat.eqb_refl in Hq.
      cbn [Calculus.disposed Calculus.comp] in Hq.
      rewrite Hd, Hw in Hq; discriminate Hq.
  Qed.

  (** Presence at a quiet state is read off the bindings of Active fibers. *)
  Lemma visible_iff (γ : State) k :
    CInv γ -> xquiet K_eq_dec Σ xprog γ -> NoFailed Σ γ ->
    (is_visible Σ γ k = true <->
     exists m fm, option_map owner (binds γ k) = Some m /\ fibers γ m = Some fm /\
                  is_active (life fm) = true).
  Proof.
    intros I Q NF; unfold is_visible, visible; split.
    - destruct (binds γ k) as [b|]; [|discriminate].
      destruct (fibers γ (owner b)) as [fo|] eqn:Ho; [|discriminate].
      destruct (is_active (life fo)) eqn:Ha; [|discriminate].
      intros _; exists (owner b), fo; auto.
    - intros (m & fm & Hb & Hm & Ha).
      destruct (binds γ k) as [b|]; [|discriminate]; cbn in Hb; injection Hb as <-.
      rewrite Hm, Ha; reflexivity.
  Qed.

  (** ** The fixpoint over base components has one solution *)
  Lemma xfix_unique (D : nat -> Prop) (Cm : nat -> C -> Prop) (S1 S2 : nat -> Prop) :
    (forall n c, D n -> Cm n c ->
       (S1 n <-> forall k, In k (xdeps c) ->
          exists m c', D m /\ Cm m c' /\ S1 m /\ In k (xprovs c'))) ->
    (forall n c, D n -> Cm n c ->
       (S2 n <-> forall k, In k (xdeps c) ->
          exists m c', D m /\ Cm m c' /\ S2 m /\ In k (xprovs c'))) ->
    forall n c, D n -> Cm n c -> (S1 n <-> S2 n).
  Proof.
    intros H1 H2.
    assert (G : forall r n c, xrank c < r -> D n -> Cm n c -> (S1 n <-> S2 n)).
    { induction r as [|r IH]; intros n c Hr Hn Hc; [lia|].
      rewrite (H1 n c Hn Hc), (H2 n c Hn Hc).
      split; intros Hall k Hk; destruct (Hall k Hk) as (m & c' & Hm & Hc' & HS & Hp);
        exists m, c'; (split; [exact Hm | split; [exact Hc'|]]);
        (assert (Hlt : xrank c' < xrank c) by (apply Hrank; left; exists k; auto));
        (split; [|exact Hp]); apply (IH m c' ltac:(lia) Hm Hc'); exact HS. }
    intros n c; exact (G (S (xrank c)) n c (Nat.lt_succ_diag_r _)).
  Qed.

  (** ** Control confluence *)
  Theorem xcontrol_confluence (γ0 γ1 γ2 : State) :
    CInv γ0 -> XLRun γ0 γ1 -> XLRun γ0 γ2 ->
    xquiet K_eq_dec Σ xprog γ1 -> xquiet K_eq_dec Σ xprog γ2 ->
    NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    (forall n, (exists f, fibers γ1 n = Some f) <-> (exists f, fibers γ2 n = Some f)) /\
    (forall n f1 f2, fibers γ1 n = Some f1 -> fibers γ2 n = Some f2 ->
       fst (fcomp f1) = fst (fcomp f2) /\ is_active (life f1) = is_active (life f2) /\
       (is_active (life f1) = true -> fcomp f1 = fcomp f2)) /\
    (forall k, option_map owner (binds γ1 k) = option_map owner (binds γ2 k)) /\
    (forall c, present γ1 c = present γ2 c).
  Proof.
    intros I0 R1 R2 Q1 Q2 NF1 NF2.
    destruct (xlrun_cinv γ0 γ1 I0 R1) as [C1 [T1 U1]].
    destruct (xlrun_cinv γ0 γ2 I0 R2) as [C2 [T2 U2]].
    destruct (final_settled γ1 C1 Q1) as [St1 Fr1].
    destruct (final_settled γ2 C2 Q2) as [St2 Fr2].
    set (D := fun n => exists f0, fibers γ0 n = Some f0 /\ disposed f0 = false).
    set (Cm := fun n c => exists f0, fibers γ0 n = Some f0 /\ fst (fcomp f0) = c).
    assert (Pres : forall γ, XStatic γ0 γ -> settled Σ prog' γ -> NoFailed Σ γ ->
              forall n, (exists f, fibers γ n = Some f) <-> D n).
    { intros γ [Ta Ub] St NF n; split.
      - intros [f Hf]; destruct (Ta n f Hf) as (f0 & H0 & _ & Hd).
        exists f0; split; [exact H0|].
        rewrite <- Hd; exact (proj1 (settled_shape Σ prog' γ n f St NF Hf)).
      - intros (f0 & H0 & Hd); exact (Ub n f0 H0 Hd). }
    assert (Comp : forall γ, XStatic γ0 γ -> forall n f c, fibers γ n = Some f -> Cm n c ->
              fst (fcomp f) = c).
    { intros γ [Ta _] n f c Hf (f0 & H0 & Hc).
      destruct (Ta n f Hf) as (f0' & H0' & Hc' & _); congruence. }
    set (S1 := fun n => exists f, fibers γ1 n = Some f /\ is_active (life f) = true).
    set (S2 := fun n => exists f, fibers γ2 n = Some f /\ is_active (life f) = true).
    assert (Fix : forall γ (S : nat -> Prop), CInv γ -> XStatic γ0 γ ->
              xquiet K_eq_dec Σ xprog γ -> settled Σ prog' γ -> NoFailed Σ γ ->
              (forall n, S n <-> exists f, fibers γ n = Some f /\ is_active (life f) = true) ->
              forall n c, D n -> Cm n c ->
                (S n <-> forall k, In k (xdeps c) ->
                   exists m c', D m /\ Cm m c' /\ S m /\ In k (xprovs c'))).
    { intros γ S CI TS Q St NF HS n c Hn Hc.
      destruct (proj2 (Pres γ TS St NF n) Hn) as [f Hf].
      pose proof (Comp γ TS n f c Hf Hc) as Efc.
      rewrite HS; split.
      - intros (f' & Hf' & Ha); rewrite Hf in Hf'; injection Hf' as <-.
        intros k Hk; rewrite <- Efc in Hk.
        destruct (proj1 (xactive_iff γ n f CI Q NF Hf) Ha k Hk) as (m & fm & Hm & Ham & Hp).
        assert (Dm : D m) by (apply (Pres γ TS St NF m); eauto).
        destruct Dm as (f0 & H0 & Hd0).
        exists m, (fst (fcomp f0)); split; [exists f0; auto|]; split; [exists f0; auto|].
        split; [apply HS; eauto|].
        rewrite <- (Comp γ TS m fm (fst (fcomp f0)) Hm (ex_intro _ f0 (conj H0 eq_refl))); exact Hp.
      - intros Hall; exists f; split; [exact Hf|].
        apply (proj2 (xactive_iff γ n f CI Q NF Hf)).
        intros k Hk; rewrite Efc in Hk.
        destruct (Hall k Hk) as (m & c' & Hm & Hc' & HSm & Hp).
        apply HS in HSm; destruct HSm as (fm & Hfm & Ha).
        exists m, fm; repeat split; auto.
        rewrite (Comp γ TS m fm c' Hfm Hc'); exact Hp. }
    assert (Same : forall n c, D n -> Cm n c -> (S1 n <-> S2 n)).
    { apply xfix_unique.
      - apply (Fix γ1 S1 C1 (conj T1 U1) Q1 St1 NF1); intros; reflexivity.
      - apply (Fix γ2 S2 C2 (conj T2 U2) Q2 St2 NF2); intros; reflexivity. }
    assert (Same' : forall n, D n -> (S1 n <-> S2 n)).
    { intros n Hn; destruct Hn as (f0 & H0 & Hd0).
      apply (Same n (fst (fcomp f0))); [exists f0; auto | exists f0; auto]. }
    (* same fibers, same base components, same activity *)
    assert (Dom : forall n, (exists f, fibers γ1 n = Some f) <-> (exists f, fibers γ2 n = Some f)).
    { intros n; rewrite (Pres γ1 (conj T1 U1) St1 NF1 n), (Pres γ2 (conj T2 U2) St2 NF2 n).
      reflexivity. }
    assert (Act : forall n f1 f2, fibers γ1 n = Some f1 -> fibers γ2 n = Some f2 ->
              fst (fcomp f1) = fst (fcomp f2) /\ is_active (life f1) = is_active (life f2)).
    { intros n f1 f2 H1 H2.
      assert (Dn : D n) by (apply (Pres γ1 (conj T1 U1) St1 NF1); eauto).
      destruct (T1 n f1 H1) as (f0 & H0 & Hc1 & _).
      destruct (T2 n f2 H2) as (f0' & H0' & Hc2 & _).
      rewrite H0 in H0'; injection H0' as <-.
      split; [congruence|].
      pose proof (Same' n Dn) as E; unfold S1, S2 in E.
      destruct (is_active (life f1)) eqn:A1, (is_active (life f2)) eqn:A2; try reflexivity.
      - exfalso; destruct (proj1 E (ex_intro _ f1 (conj H1 A1))) as (f2' & H2' & A2').
        rewrite H2 in H2'; injection H2' as <-; congruence.
      - exfalso; destruct (proj2 E (ex_intro _ f2 (conj H2 A2))) as (f1' & H1' & A1').
        rewrite H1 in H1'; injection H1' as <-; congruence. }
    (* same owners *)
    assert (Own : forall k, option_map owner (binds γ1 k) = option_map owner (binds γ2 k)).
    { intros k.
      assert (O : forall m, option_map owner (binds γ1 k) = Some m <->
                            option_map owner (binds γ2 k) = Some m).
      { intros m.
        rewrite (owner_iff K_eq_dec Σ prog' Kb γ1 k m (cinv_0 _ _ _ _ _ C1) St1 NF1),
                (owner_iff K_eq_dec Σ prog' Kb γ2 k m (cinv_0 _ _ _ _ _ C2) St2 NF2).
        split; intros (fm & Hm & Ha & Hp).
        - assert (Hm2 : exists f, fibers γ2 m = Some f) by (apply Dom; eauto).
          destruct Hm2 as [fm2 Hm2]; destruct (Act m fm fm2 Hm Hm2) as [Ec Ea].
          exists fm2; split; [exact Hm2|]; split; [congruence|].
          unfold Optional.prog' in *; cbn [provs] in *; rewrite <- Ec; exact Hp.
        - assert (Hm1 : exists f, fibers γ1 m = Some f) by (apply Dom; eauto).
          destruct Hm1 as [fm1 Hm1]; destruct (Act m fm1 fm Hm1 Hm) as [Ec Ea].
          exists fm1; split; [exact Hm1|]; split; [congruence|].
          unfold Optional.prog' in *; cbn [provs] in *; rewrite Ec; exact Hp. }
      destruct (option_map owner (binds γ1 k)) as [m1|] eqn:O1,
               (option_map owner (binds γ2 k)) as [m2|] eqn:O2; try reflexivity.
      - pose proof (proj1 (O m1) eq_refl) as E; congruence.
      - pose proof (proj1 (O m1) eq_refl) as E; congruence.
      - pose proof (proj2 (O m2) eq_refl) as E; congruence. }
    (* same presence *)
    assert (Vis : forall k, is_visible Σ γ1 k = is_visible Σ γ2 k).
    { intros k.
      assert (E : is_visible Σ γ1 k = true <-> is_visible Σ γ2 k = true).
      { rewrite (visible_iff γ1 k C1 Q1 NF1), (visible_iff γ2 k C2 Q2 NF2), (Own k).
        split; intros (m & fm & Hb & Hm & Ha).
        - assert (Hm2 : exists f, fibers γ2 m = Some f) by (apply Dom; eauto).
          destruct Hm2 as [fm2 Hm2]; destruct (Act m fm fm2 Hm Hm2) as [_ Ea].
          exists m, fm2; split; [exact Hb|]; split; [exact Hm2 | congruence].
        - assert (Hm1 : exists f, fibers γ1 m = Some f) by (apply Dom; eauto).
          destruct Hm1 as [fm1 Hm1]; destruct (Act m fm1 fm Hm1 Hm) as [_ Ea].
          exists m, fm1; split; [exact Hb|]; split; [exact Hm1 | congruence]. }
      destruct (is_visible Σ γ1 k), (is_visible Σ γ2 k); try reflexivity;
        [symmetry|]; apply E; reflexivity. }
    assert (Pr : forall c, present γ1 c = present γ2 c).
    { intros c; unfold Optional.present; apply filter_ext; exact Vis. }
    split; [exact Dom|]; split; [|split; [exact Own | exact Pr]].
    intros n f1 f2 H1 H2; destruct (Act n f1 f2 H1 H2) as [Ec Ea].
    split; [exact Ec|]; split; [exact Ea|].
    intros A1.
    assert (A2 : is_active (life f2) = true) by congruence.
    destruct (life f1) as [| |acc1 w1|] eqn:L1; try discriminate.
    destruct (life f2) as [| |acc2 w2|] eqn:L2; try discriminate.
    pose proof (Fr1 n f1 acc1 w1 H1 L1) as F1; pose proof (Fr2 n f2 acc2 w2 H2 L2) as F2.
    unfold Optional.fresh in F1, F2.
    destruct (list_eq_dec K_eq_dec (present γ1 (fst (fcomp f1))) (snd (fcomp f1))) as [E1|];
      [|discriminate].
    destruct (list_eq_dec K_eq_dec (present γ2 (fst (fcomp f2))) (snd (fcomp f2))) as [E2|];
      [|discriminate].
    destruct (fcomp f1) as [c1 s1], (fcomp f2) as [c2 s2]; cbn in *.
    subst c2; rewrite <- E1, <- E2, Pr; reflexivity.
  Qed.
End OptConfluence.
