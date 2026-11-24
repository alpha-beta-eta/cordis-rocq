(** * Extension 1: no deadlock with optional dependencies

    The core progress theorem ([Progress.quiet_settled]) carries over: an
    extended state at which no extended lifecycle rule applies is settled
    in the core sense, and every Active fiber's presence is current.

    Two things need care.
    - The core asks [Inv2]: a child's component is one its parent's
      component may create. [X-Begin] re-chooses the presence of a child,
      so its component [(c, S)] is no longer literally the [(c, [])] its
      parent spawned. The base components still match ([XSpawnProv]). The
      core theorem is applied to a table [progG γ] that differs from
      [prog'] only in its handler lists, to which it adds the components of
      the children present in [γ]; no lifecycle rule reads handler lists, so
      [progG γ] and [prog'] take the same lifecycle steps.
    - The core asks that the relation "provides a key the other declares,
      or may spawn it" have no infinite ascending chain. Here a rank on base
      components rises along required and optional dependencies and along
      spawns ([XAbove]); optional edges are needed, or two components each
      optional on the other could reload each other forever. *)

From Stdlib Require Import List PeanoNat Bool Lia Wf_nat.
From Cordis Require Import Prelude Service Calculus Preservation Recovery Progress.
From Cordis Require Import Ext.Optional.
Import ListNotations.

Section OptProgress.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (C_eq_dec : forall x y : C, {x = y} + {x <> y}).
  Context (xprog : C -> @XComponent K Σ C).

  Local Notation CC := (@Optional.C' K C).
  Local Notation State := (@State K Σ CC).
  Local Notation Fiber := (@Fiber K Σ CC).
  Local Notation fibers := (fibers Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation acc_of := (acc_of Σ).
  Local Notation prog' := (prog' K_eq_dec Σ xprog).
  Local Notation step := (step K_eq_dec Σ prog').
  Local Notation WF := (WF K_eq_dec Σ prog').
  Local Notation xstep := (xstep K_eq_dec Σ xprog).
  Local Notation fresh := (fresh K_eq_dec Σ xprog).
  Local Notation recomp := (recomp Σ xprog).
  Local Notation present := (present Σ xprog).

  Definition ceq (x y : CC) : {x = y} + {x <> y}.
  Proof.
    destruct x as [c S], y as [c' S'].
    destruct (C_eq_dec c c'), (list_eq_dec K_eq_dec S S');
      [left; congruence | right; congruence | right; congruence | right; congruence].
  Defined.

  (** ** The table [progG γ] *)
  Definition spawned_comps (γ : State) (acc : list (@Undo K Σ)) : list CC :=
    flat_map (fun u => match u with
                       | USpawn _ m => match fibers γ m with Some g => [fcomp g] | None => [] end
                       | _ => []
                       end) acc.

  (** The components of the children of fibers of component [x]. *)
  Definition kids (γ : State) (x : CC) : list CC :=
    flat_map (fun q => match fibers γ q with
                       | Some f => if ceq (fcomp f) x then spawned_comps γ (acc_of (life f)) else []
                       | None => []
                       end) (names Σ γ).

  Definition progG (γ : State) (x : CC) : @Component K Σ CC :=
    mkComponent (deps Σ (prog' x)) (provs Σ (prog' x)) (body Σ (prog' x))
                (reacts Σ (prog' x) ++ kids γ x).

  Lemma wf_G γ0 (γ : State) : WF γ -> Preservation.WF K_eq_dec Σ (progG γ0) γ.
  Proof. intros W; destruct W; split; assumption. Qed.

  Lemma prov_G γ0 (γ : State) : Prov Σ prog' γ -> Prov Σ (progG γ0) γ.
  Proof. intros [P T]; split; assumption. Qed.

  Lemma step_G γ0 (γ : State) ℓ :
    (forall n i, ℓ <> OReact n i) -> Calculus.step K_eq_dec Σ (progG γ0) γ ℓ = step γ ℓ.
  Proof.
    intros H; destruct ℓ; try reflexivity; exfalso; eapply H; reflexivity.
  Qed.

  Lemma react_G γ0 (γ γ' : State) n i :
    step γ (OReact n i) = Some γ' -> Calculus.step K_eq_dec Σ (progG γ0) γ (OReact n i) = Some γ'.
  Proof.
    cbn [Calculus.step]; intros H.
    destruct (fibers γ n) as [f|]; [|discriminate H].
    destruct (life f) as [| |acc w|]; try discriminate H.
    destruct (nth_error (reacts Σ (prog' (fcomp f))) i) as [c|] eqn:E; [|discriminate H].
    assert (E' : nth_error (reacts Σ (progG γ0 (fcomp f))) i = Some c).
    { unfold progG; cbn [reacts].
      rewrite nth_error_app1; [exact E|].
      apply nth_error_Some; rewrite E; intros D; discriminate D. }
    rewrite E'; exact H.
  Qed.

  Lemma step_G_any γ0 (γ γ' : State) ℓ :
    step γ ℓ = Some γ' -> Calculus.step K_eq_dec Σ (progG γ0) γ ℓ = Some γ'.
  Proof.
    intros H; destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n];
      try (rewrite step_G; [exact H | intros ? ? E; discriminate E]).
    apply react_G; exact H.
  Qed.

  (** ** Spawning at the level of base components *)
  Definition XSpawns (c c' : C) : Prop :=
    (exists T, SpawnIn Σ c' (xbody Σ (xprog c) T)) \/ In c' (xreacts Σ (xprog c)).

  Definition XSpawnProv (γ : State) : Prop :=
    forall x f m fm, fibers γ x = Some f -> In (USpawn Σ m) (acc_of (life f)) ->
                     fibers γ m = Some fm -> XSpawns (fst (fcomp f)) (fst (fcomp fm)).

  Lemma spawnin_lift (y : CC) (P : @Prog K Σ C) :
    SpawnIn Σ y (lift Σ P) -> SpawnIn Σ (fst y) P.
  Proof.
    induction P as [| |k a κ IH|k s Q IH|c Q IH]; cbn; intros H; inversion H; subst.
    - eapply spi_op; apply IH; eassumption.
    - apply spi_prov; apply IH; assumption.
    - apply spi_here.
    - apply spi_spawn; apply IH; assumption.
  Qed.

  Lemma spawns_G γ0 x y :
    XSpawnProv γ0 -> Spawns Σ (progG γ0) x y -> XSpawns (fst x) (fst y).
  Proof.
    intros XP [Hs|Hr].
    - left; unfold progG, Optional.prog' in Hs; cbn [body] in Hs.
      eexists; exact (spawnin_lift _ _ Hs).
    - unfold progG in Hr; cbn [reacts] in Hr.
      apply in_app_or in Hr as [Hr|Hr].
      + right; unfold Optional.prog' in Hr; cbn [reacts] in Hr.
        apply in_map_iff in Hr as (c & <- & Hc); exact Hc.
      + unfold kids in Hr; apply in_flat_map in Hr as (q & _ & Hr).
        destruct (fibers γ0 q) as [f|] eqn:Hq; [|contradiction].
        destruct (ceq (fcomp f) x) as [<-|]; [|contradiction].
        unfold spawned_comps in Hr; apply in_flat_map in Hr as (u & Hu & Hr).
        destruct u as [| |m]; try contradiction.
        destruct (fibers γ0 m) as [g|] eqn:Hm; [|contradiction].
        destruct Hr as [<-|[]].
        exact (XP q f m g Hq Hu Hm).
  Qed.

  Lemma inv2_G (γ : State) : WF γ -> PidUnique Σ γ -> Inv2 Σ (progG γ) γ.
  Proof.
    intros W U; split; [exact U|].
    intros x f m fm Hx Hu Hm; right.
    unfold progG; cbn [reacts]; apply in_or_app; right.
    unfold kids; apply in_flat_map; exists x; split; [exact (in_names K_eq_dec Σ prog' γ x f W Hx)|].
    rewrite Hx; destruct (ceq (fcomp f) (fcomp f)) as [_|N]; [|contradiction N; reflexivity].
    unfold spawned_comps; apply in_flat_map; exists (USpawn Σ m); split; [exact Hu|].
    rewrite Hm; left; reflexivity.
  Qed.

  (** ** The invariant along extended executions *)
  Record XInv (γ : State) : Prop := {
    xi_wf : WF γ;
    xi_prov : Prov Σ prog' γ;
    xi_pid : PidUnique Σ γ;
    xi_spawn : XSpawnProv γ
  }.

  Lemma xinv_init : XInv (@init K Σ CC).
  Proof.
    split; [exact (wf_init K_eq_dec Σ prog') | exact (prov_init Σ prog') | | ];
      cbn; intros; discriminate.
  Qed.

  Lemma xinv_core (γ γ' : State) ℓ : XInv γ -> step γ ℓ = Some γ' -> XInv γ'.
  Proof.
    intros [W P U X] H.
    pose proof (step_G_any γ γ γ' ℓ H) as HG.
    destruct (inv2_step K_eq_dec Σ (progG γ) γ γ' ℓ (wf_G γ γ W) (prov_G γ γ P) (inv2_G γ W U) HG)
      as [U' S'].
    split.
    - exact (preservation K_eq_dec Σ prog' γ γ' ℓ W H).
    - exact (prov_step K_eq_dec Σ prog' γ γ' ℓ W P H).
    - exact U'.
    - intros x f m fm Hx Hu Hm; exact (spawns_G γ _ _ X (S' x f m fm Hx Hu Hm)).
  Qed.

  Lemma fibers_recomp (γ : State) n f m :
    fibers (recomp γ n f) m =
    if Nat.eqb m n
    then Some (mkFiber Σ (fst (fcomp f), present γ (fst (fcomp f)))
                       (Calculus.parent Σ f) (Calculus.disposed Σ f) (life f))
    else fibers γ m.
  Proof. reflexivity. Qed.

  Lemma xinv_recomp (γ : State) n f :
    XInv γ -> fibers γ n = Some f -> is_installed Σ (life f) = false -> XInv (recomp γ n f).
  Proof.
    intros [W [PF PT] U X] Hn Hi.
    (* every fiber of the new state is an old fiber with the same life and
       the same base component *)
    assert (Hb : forall m fm, fibers (recomp γ n f) m = Some fm ->
                 exists fm0, fibers γ m = Some fm0 /\ life fm = life fm0 /\
                             fst (fcomp fm) = fst (fcomp fm0)).
    { intros m fm H; rewrite fibers_recomp in H.
      destruct (Nat.eqb_spec m n) as [->|]; [injection H as <-; exists f; auto|].
      exists fm; auto. }
    split.
    - exact (wf_recomp K_eq_dec Σ xprog γ n f W Hn Hi).
    - split.
      + intros m fm H; rewrite fibers_recomp in H; cbn [Calculus.next recomp set_fiber with_fibers].
        destruct (Nat.eqb_spec m n) as [->|]; [injection H as <-|exact (PF m fm H)].
        apply (ProvF_inactive Σ prog' _ _ (match life f with Inactive _ z => z | _ => None end)); cbn.
        destruct (life f); try discriminate; reflexivity.
      + intros m1 m2 f1 f2 k1 p1 g1 k2 p2 g2 t Hne H1 H2 I1 I2.
        destruct (Hb m1 f1 H1) as (f1' & H1' & E1 & _), (Hb m2 f2 H2) as (f2' & H2' & E2 & _).
        rewrite E1 in I1; rewrite E2 in I2; exact (PT m1 m2 f1' f2' k1 p1 g1 k2 p2 g2 t Hne H1' H2' I1 I2).
    - exact U.
    - intros x fx m fm Hx Hu Hm.
      destruct (Hb x fx Hx) as (fx' & Hx' & Ex & Cx), (Hb m fm Hm) as (fm' & Hm' & Em & Cm).
      rewrite Cx, Cm; rewrite Ex in Hu; exact (X x fx' m fm' Hx' Hu Hm').
  Qed.

  Theorem xinv_step (γ γ' : State) ℓ : XInv γ -> xstep γ ℓ = Some γ' -> XInv γ'.
  Proof.
    intros I H.
    destruct (xstep_core K_eq_dec Σ xprog γ γ' ℓ H) as [S|[(n & f & _ & Hn & Hl & S)|(n & S)]].
    - exact (xinv_core γ γ' _ I S).
    - apply (xinv_core (recomp γ n f) γ' (LBegin n)); [|exact S].
      apply xinv_recomp; auto; rewrite Hl; reflexivity.
    - exact (xinv_core γ γ' _ I S).
  Qed.

  Theorem xinv_reachable (γ : State) : XReachable K_eq_dec Σ xprog γ -> XInv γ.
  Proof.
    intros [ls H].
    assert (G : forall γ0, XInv γ0 -> xrun K_eq_dec Σ xprog γ0 ls = Some γ -> XInv γ).
    { clear H; induction ls as [|ℓ ls IH]; cbn; intros γ0 I0 H0.
      - injection H0 as <-; exact I0.
      - destruct (xstep γ0 ℓ) as [γ1|] eqn:Hs; [|discriminate].
        exact (IH γ1 (xinv_step γ0 γ1 ℓ I0 Hs) H0). }
    exact (G _ xinv_init H).
  Qed.

  (** ** The rank obligation *)
  Definition XAbove (c c' : C) : Prop :=
    (exists k, In k (xprovs Σ (xprog c)) /\
               (In k (xdeps Σ (xprog c')) \/ In k (xopt Σ (xprog c')))) \/
    XSpawns c c'.

  Variable xrank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', XAbove c c' -> xrank c < xrank c'.
  Hypothesis Hbnd : forall c, xrank c <= Rb.

  Lemma above_G (γ : State) x y :
    XSpawnProv γ -> Above Σ (progG γ) x y -> xrank (fst x) < xrank (fst y).
  Proof.
    intros XP [(k & Hp & Hd)|Hs]; apply Hrank.
    - left; exists k; split; [exact Hp|].
      unfold progG, Optional.prog' in Hd; cbn [deps] in Hd.
      apply in_app_or in Hd as [Hd|Hd]; [left; exact Hd|].
      right; apply filter_In in Hd as [_ Hd].
      unfold kmem, keqb in Hd; apply existsb_exists in Hd as (k' & Hk' & E).
      destruct (K_eq_dec k k') as [->|]; [exact Hk' | discriminate].
    - right; exact (spawns_G γ x y XP Hs).
  Qed.

  Lemma wf_G_above (γ : State) :
    XSpawnProv γ -> well_founded (fun y x => Above Σ (progG γ) x y).
  Proof.
    intros XP.
    apply (well_founded_lt_compat _ (fun x => Rb - xrank (fst x))).
    intros y x HA; pose proof (above_G γ x y XP HA); pose proof (Hbnd (fst y)); lia.
  Qed.

  (** ** Quiet extended states are settled *)
  Definition xquiet (γ : State) : Prop :=
    forall n ℓ, In ℓ (@lifecycle_labels C n) -> xstep γ ℓ = None.

  Lemma visible_recomp (γ : State) n f k :
    fibers γ n = Some f -> visible Σ (recomp γ n f) k = visible Σ γ k.
  Proof.
    intros Hn; unfold visible.
    change (Calculus.binds Σ (recomp γ n f)) with (Calculus.binds Σ γ).
    destruct (Calculus.binds Σ γ k) as [b|]; [|reflexivity].
    rewrite fibers_recomp; destruct (Nat.eqb_spec (owner Σ b) n) as [->|]; [|reflexivity].
    rewrite Hn; reflexivity.
  Qed.

  Lemma resolve_ext (γ1 γ2 : State) ks :
    (forall k, visible Σ γ1 k = visible Σ γ2 k) -> resolve Σ γ1 ks = resolve Σ γ2 ks.
  Proof.
    intros E; induction ks as [|k ks IH]; cbn; [reflexivity|]; rewrite E, IH; reflexivity.
  Qed.

  Lemma resolve_app_l (γ : State) l1 l2 w :
    resolve Σ γ (l1 ++ l2) = Some w -> exists w1, resolve Σ γ l1 = Some w1.
  Proof.
    revert w; induction l1 as [|k l1 IH]; cbn; intros w H; [eauto|].
    destruct (visible Σ γ k) as [p|]; [|discriminate].
    destruct (resolve Σ γ (l1 ++ l2)) as [w'|] eqn:E; [|discriminate].
    destruct (IH w' eq_refl) as (w1 & ->); eauto.
  Qed.

  Lemma resolve_app (γ : State) l1 l2 w1 w2 :
    resolve Σ γ l1 = Some w1 -> resolve Σ γ l2 = Some w2 -> resolve Σ γ (l1 ++ l2) = Some (w1 ++ w2).
  Proof.
    revert w1; induction l1 as [|k l1 IH]; cbn; intros w1 H1 H2; [injection H1 as <-; exact H2|].
    destruct (visible Σ γ k) as [p|]; [|discriminate].
    destruct (resolve Σ γ l1) as [w'|]; [|discriminate].
    injection H1 as <-; rewrite (IH w' eq_refl H2); reflexivity.
  Qed.

  Lemma resolve_visible (γ : State) ks :
    (forall k, In k ks -> is_visible Σ γ k = true) -> exists w, resolve Σ γ ks = Some w.
  Proof.
    induction ks as [|k ks IH]; cbn; intros H; [eauto|].
    pose proof (H k (or_introl eq_refl)) as Hk; unfold is_visible in Hk.
    destruct (visible Σ γ k) as [p|]; [|discriminate].
    destruct IH as (w & ->); [intros; apply H; right; assumption | eauto].
  Qed.

  (** An Inactive fiber the core would begin, the extension begins too,
      after re-choosing its presence. *)
  Lemma begin_recomp (γ : State) n f w :
    fibers γ n = Some f -> target Σ prog' γ n = Some w ->
    exists w', target Σ prog' (recomp γ n f) n = Some w'.
  Proof.
    intros Hn Ht; unfold Calculus.target in *; rewrite Hn in Ht.
    rewrite fibers_recomp, Nat.eqb_refl; cbn [Calculus.disposed Calculus.comp].
    destruct (Calculus.disposed Σ f); [discriminate|].
    rewrite (resolve_ext _ γ _ (fun k => visible_recomp γ n f k Hn)).
    unfold Optional.prog' in *; cbn [deps fst snd] in *.
    destruct (resolve_app_l γ _ _ w Ht) as (w1 & H1).
    destruct (resolve_visible γ (filter (fun k => kmem K_eq_dec k (xopt Σ (xprog (fst (fcomp f)))))
                                        (present γ (fst (fcomp f))))) as (w2 & H2).
    { intros k Hk; apply filter_In in Hk as [Hk _]; unfold Optional.present in Hk.
      apply filter_In in Hk as [_ Hk]; exact Hk. }
    eexists; exact (resolve_app γ _ _ w1 w2 H1 H2).
  Qed.

  Lemma core_quiet (γ : State) : xquiet γ -> quiet K_eq_dec Σ (progG γ) γ.
  Proof.
    intros Q n ℓ Hin.
    rewrite step_G by (cbn in Hin; intros ? ? E; subst ℓ; intuition discriminate).
    destruct (step γ ℓ) as [γ'|] eqn:Hs; [exfalso|reflexivity].
    cbn in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
    - (* LBegin *)
      cbn [Calculus.step] in Hs.
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (target Σ prog' γ n) as [w|] eqn:Ht; [|discriminate].
      destruct (begin_recomp γ n f w Hn Ht) as (w' & Ht').
      assert (X : xstep γ (LBegin n) <> None).
      { cbn [Optional.xstep]; rewrite Hn, Hl; cbn [Calculus.step].
        rewrite fibers_recomp, Nat.eqb_refl; cbn [Calculus.life]; rewrite Hl, Ht'; discriminate. }
      exact (X (Q n (LBegin n) ltac:(cbn; auto))).
    - (* LStep *)
      assert (X : xstep γ (LDivert n) <> None \/ xstep γ (LStep n) <> None).
      { pose proof Hs as Hs0; cbn [Optional.xstep]; cbn [Calculus.step] in Hs.
        destruct (fibers γ n) as [f|]; [|discriminate].
        destruct (fresh γ f); [right; cbn [xlab]; rewrite Hs0; discriminate|left].
        destruct (life f); try discriminate; discriminate. }
      destruct X as [X|X]; [exact (X (Q n (LDivert n) ltac:(cbn; auto)))
                           | exact (X (Q n (LStep n) ltac:(cbn; auto)))].
    - (* LDivert *)
      assert (X : xstep γ (LDivert n) <> None).
      { pose proof Hs as Hs0; cbn [Optional.xstep]; cbn [Calculus.step] in Hs.
        destruct (fibers γ n) as [f|]; [|discriminate].
        destruct (fresh γ f); [rewrite Hs0; discriminate|].
        destruct (life f); try discriminate; discriminate. }
      exact (X (Q n (LDivert n) ltac:(cbn; auto))).
    - (* LLeave *)
      assert (X : xstep γ (LLeave n) <> None).
      { pose proof Hs as Hs0; cbn [Optional.xstep]; cbn [Calculus.step] in Hs.
        destruct (fibers γ n) as [f|]; [|discriminate].
        destruct (fresh γ f); [rewrite Hs0; discriminate|].
        destruct (life f); try discriminate; discriminate. }
      exact (X (Q n (LLeave n) ltac:(cbn; auto))).
    - assert (X : xstep γ (LUndo n) <> None) by (cbn [Optional.xstep xlab]; rewrite Hs; discriminate).
      exact (X (Q n (LUndo n) ltac:(cbn; auto 10))).
    - assert (X : xstep γ (LRetireChild n) <> None) by (cbn [Optional.xstep xlab]; rewrite Hs; discriminate).
      exact (X (Q n (LRetireChild n) ltac:(cbn; auto 10))).
    - assert (X : xstep γ (LUnloaded n) <> None) by (cbn [Optional.xstep xlab]; rewrite Hs; discriminate).
      exact (X (Q n (LUnloaded n) ltac:(cbn; auto 10))).
    - assert (X : xstep γ (LRemove n) <> None) by (cbn [Optional.xstep xlab]; rewrite Hs; discriminate).
      exact (X (Q n (LRemove n) ltac:(cbn; auto 10))).
  Qed.

  (** Tier 1 (no deadlock) for the extension: at a quiet extended state
      every fiber is settled in the core sense, and every Active fiber runs
      the variant for the optional keys present now. *)
  Theorem xquiet_settled (γ : State) :
    XInv γ -> xquiet γ ->
    settled Σ prog' γ /\
    (forall n f acc w, fibers γ n = Some f -> life f = Active Σ acc w -> fresh γ f = true).
  Proof.
    intros [W P U X] Q; split.
    - exact (quiet_settled K_eq_dec Σ (progG γ) (wf_G_above γ X) γ (wf_G γ γ W)
               (inv2_G γ W U) (core_quiet γ Q)).
    - intros n f acc w Hn Hl.
      destruct (fresh γ f) eqn:E; [reflexivity|exfalso].
      pose proof (Q n (LLeave n) ltac:(cbn; auto)) as Hq; cbn [Optional.xstep] in Hq.
      rewrite Hn, E, Hl in Hq; discriminate Hq.
  Qed.

  Corollary xquiet_settled_reachable (γ : State) :
    XReachable K_eq_dec Σ xprog γ -> xquiet γ ->
    settled Σ prog' γ /\
    (forall n f acc w, fibers γ n = Some f -> life f = Active Σ acc w -> fresh γ f = true).
  Proof. intros R; exact (xquiet_settled γ (xinv_reachable γ R)). Qed.
End OptProgress.
