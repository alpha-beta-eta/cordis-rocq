(** * Hygienic keys: termination

    Counterpart of [Termination.termination]: extended lifecycle steps
    alone cannot go on for ever, from any state satisfying [KTInv], in
    particular from any state an extended execution reaches
    ([ktermination_reachable]).

    The proof follows [Ext/OptTermination.v]. The core measure cannot be
    reused as it stands: it reads the core target, and a fiber whose
    exported dependency is now won by another candidate (or tied) still has
    its core target, though it must reload. The measure [kmu] has the shape
    of the core's, with two changes:
    - a Loading or Active fiber is "on target" when its selection is still
      current and the core target equals its view ([ktis]);
    - whether a fiber about to finish unloading, or Inactive, would begin
      again is read from the target it would have after choosing its
      selection ([bt]).
    As in the core, the state measure is a vector indexed by rank and drops
    lexicographically at every step. What makes this work: a step of [n]
    changes neither the visibility of a key named by a dependency of a
    fiber of rank at most that of [n], nor the selection of such a name
    ([vis_stable], [select_stable]), because the rank rises from every
    provider of a name to every component depending on it, private or
    exported ([KAbove]). Selection stability also needs unique scopes
    ([ScopedSafety.SI]): only the fiber of scope [s] binds keys at [s].

    The core's [lstep_effects] and [tinv_step] are reused through the table
    [progG γ], which adds to each component's handlers the components of
    its present children: X-Begin re-chooses a child's selection and
    X-React stamps a parent, so a child's component is no longer literally
    one its parent's component creates; only base components match
    ([KSpawnProv]).

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia Wf_nat Compare_dec.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Recovery Progress Termination.
From CordisKeys Require Import Scoped ScopedSafety.
Import ListNotations.

Section ScopedTerm.
  Context {N : Type} (N_eq_dec : forall x y : N, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (C_eq_dec : forall x y : C, {x = y} + {x <> y}).
  Context (xprog : C -> @XComponent N Σ C).

  Local Notation XC := (@XC N C).
  Local Notation Key := (@Key N).
  Local Notation State := (@State Key Σ XC).
  Local Notation Fiber := (@Fiber Key Σ XC).
  Local Notation Life := (@Life Key Σ XC).
  Local Notation View := (@View Key).
  Local Notation Undo := (@Undo Key Σ).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation next := (Calculus.next Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation fparent := (Calculus.parent Σ).
  Local Notation disposed := (Calculus.disposed Σ).
  Local Notation acc_of := (acc_of Σ).
  Local Notation owner := (owner Σ).
  Local Notation kdec := (key_eq_dec N_eq_dec).
  Local Notation prog' := (prog' N_eq_dec Σ xprog).
  Local Notation lift := (lift N_eq_dec Σ xprog).
  Local Notation handlers := (handlers N_eq_dec Σ xprog).
  Local Notation step := (step kdec Σ prog').
  Local Notation kstep := (kstep N_eq_dec Σ xprog).
  Local Notation krun := (krun N_eq_dec Σ xprog).
  Local Notation recomp := (recomp N_eq_dec Σ xprog).
  Local Notation retick := (retick Σ).
  Local Notation fresh := (fresh N_eq_dec Σ xprog).
  Local Notation select := (select N_eq_dec Σ xprog).
  Local Notation candidate := (candidate N_eq_dec Σ xprog).
  Local Notation choose := (choose N_eq_dec Σ xprog).
  Local Notation all_selected := (all_selected N_eq_dec Σ xprog).
  Local Notation globals := (globals Σ xprog).
  Local Notation target := (target Σ prog').
  Local Notation target_is := (target_is kdec Σ prog').
  Local Notation WF := (WF kdec Σ prog').
  Local Notation SI := (SI N_eq_dec Σ xprog).
  Local Notation xdeps c := (xdeps Σ (xprog c)).
  Local Notation xexports c := (xexports Σ (xprog c)).
  Local Notation xprovs c := (xprovs Σ xprog c).
  Local Notation dnames c := (map dname (xdeps c)).

  (** ** Decidable equality of components *)
  Local Notation ns_eq_dec := (ns_eq_dec N_eq_dec).

  Definition ceq (x y : XC) : {x = y} + {x <> y}.
  Proof.
    destruct x as [c s e l t], y as [c' s' e' l' t'].
    destruct (C_eq_dec c c'); [|right; congruence].
    destruct (scope_eq_dec s s'); [|right; congruence].
    destruct (list_eq_dec ns_eq_dec e e'); [|right; congruence].
    destruct (list_eq_dec ns_eq_dec l l'); [|right; congruence].
    destruct (Nat.eq_dec t t'); [|right; congruence].
    left; congruence.
  Defined.

  (** ** The table [progG γ] *)
  Definition spawned_comps (γ : State) (acc : list Undo) : list XC :=
    flat_map (fun u => match u with
                       | USpawn _ m => match fibers γ m with Some g => [fcomp g] | None => [] end
                       | _ => []
                       end) acc.

  Definition kids (γ : State) (x : XC) : list XC :=
    flat_map (fun q => match fibers γ q with
                       | Some f => if ceq (fcomp f) x then spawned_comps γ (acc_of (life f)) else []
                       | None => []
                       end) (names Σ γ).

  Definition progG (γ : State) (x : XC) : @Component Key Σ XC :=
    mkComponent (deps Σ (prog' x)) (provs Σ (prog' x)) (body Σ (prog' x))
                (reacts Σ (prog' x) ++ kids γ x).

  Lemma wf_G γ0 (γ : State) : WF γ -> Preservation.WF kdec Σ (progG γ0) γ.
  Proof. intros W; destruct W; split; assumption. Qed.

  Lemma prov_G γ0 (γ : State) : Prov Σ prog' γ -> Prov Σ (progG γ0) γ.
  Proof. intros [P T]; split; assumption. Qed.

  Lemma step_G γ0 (γ : State) ℓ :
    (forall n i, ℓ <> OReact n i) -> Calculus.step kdec Σ (progG γ0) γ ℓ = step γ ℓ.
  Proof. intros H; destruct ℓ; try reflexivity; exfalso; eapply H; reflexivity. Qed.

  Lemma react_G γ0 (γ γ' : State) n i :
    step γ (OReact n i) = Some γ' -> Calculus.step kdec Σ (progG γ0) γ (OReact n i) = Some γ'.
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
    step γ ℓ = Some γ' -> Calculus.step kdec Σ (progG γ0) γ ℓ = Some γ'.
  Proof.
    intros H; destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n];
      try (rewrite step_G; [exact H | intros ? ? E; discriminate E]).
    apply react_G; exact H.
  Qed.

  (** ** Spawning at the level of base components *)
  Definition KSpawns (c c' : C) : Prop :=
    SpawnIn Σ c' (xbody Σ (xprog c)) \/ In c' (xreacts Σ (xprog c)).

  Definition KSpawnProv (γ : State) : Prop :=
    forall x f m fm, fibers γ x = Some f -> In (USpawn Σ m) (acc_of (life f)) ->
                     fibers γ m = Some fm -> KSpawns (base (fcomp f)) (base (fcomp fm)).

  Lemma spawnin_lift (x y : XC) j (P : @Prog N Σ C) :
    SpawnIn Σ y (lift x j P) -> SpawnIn Σ (base y) P.
  Proof.
    revert j; induction P as [| |k a κ IH|k s Q IH|c Q IH]; intros j; cbn; intros H;
      inversion H; subst.
    - eapply spi_op; eapply IH; eassumption.
    - apply spi_prov; eapply IH; eassumption.
    - apply spi_here.
    - apply spi_spawn; eapply IH; eassumption.
  Qed.

  Lemma handlers_in (x y : XC) i cs : In y (handlers x i cs) -> In (base y) cs.
  Proof.
    revert i; induction cs as [|c cs IH]; intros i; cbn; [tauto|].
    intros [<-|H]; [left; reflexivity | right; exact (IH _ H)].
  Qed.

  Lemma spawns_G γ0 x y :
    KSpawnProv γ0 -> Spawns Σ (progG γ0) x y -> KSpawns (base x) (base y).
  Proof.
    intros XP [Hs|Hr].
    - left; unfold progG in Hs; cbn [body Scoped.prog'] in Hs.
      exact (spawnin_lift _ _ _ _ Hs).
    - unfold progG in Hr; cbn [reacts] in Hr.
      apply in_app_or in Hr as [Hr|Hr].
      + right; cbn [Scoped.prog' reacts] in Hr; exact (handlers_in _ _ _ _ Hr).
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
    unfold kids; apply in_flat_map; exists x; split; [exact (in_names kdec Σ prog' γ x f W Hx)|].
    rewrite Hx; destruct (ceq (fcomp f) (fcomp f)) as [_|Nq]; [|contradiction Nq; reflexivity].
    unfold spawned_comps; apply in_flat_map; exists (USpawn Σ m); split; [exact Hu|].
    rewrite Hm; left; reflexivity.
  Qed.

  (** ** The invariant *)
  Record KInv (γ : State) : Prop := {
    ki_wf : WF γ;
    ki_prov : Prov Σ prog' γ;
    ki_pid : PidUnique Σ γ;
    ki_spawn : KSpawnProv γ;
    ki_si : SI γ
  }.

  Lemma kinv_init : KInv (@init Key Σ XC).
  Proof.
    split; [exact (wf_init kdec Σ prog') | exact (prov_init Σ prog') | | | exact (si_init N_eq_dec Σ xprog)];
      cbn; intros; discriminate.
  Qed.

  (** A core step keeps everything but [SI], which [si_kstep] handles. *)
  Lemma kinv_core4 (γ γ' : State) ℓ :
    KInv γ -> step γ ℓ = Some γ' ->
    WF γ' /\ Prov Σ prog' γ' /\ PidUnique Σ γ' /\ KSpawnProv γ'.
  Proof.
    intros [W P U X _] H.
    pose proof (step_G_any γ γ γ' ℓ H) as HG.
    destruct (inv2_step kdec Σ (progG γ) γ γ' ℓ (wf_G γ γ W) (prov_G γ γ P) (inv2_G γ W U) HG)
      as [U' S'].
    split; [exact (preservation kdec Σ prog' γ γ' ℓ W H)|].
    split; [exact (prov_step kdec Σ prog' γ γ' ℓ W P H)|].
    split; [exact U'|].
    intros x f m fm Hx Hu Hm; exact (spawns_G γ _ _ X (S' x f m fm Hx Hu Hm)).
  Qed.

  Lemma fibers_refiber (γ : State) n (f' : Fiber) m :
    fibers (set_fiber Σ γ n f') m = if Nat.eqb m n then Some f' else fibers γ m.
  Proof. reflexivity. Qed.

  (** Replacing a fiber's component by one with the same base. *)
  Lemma kinv_refiber4 (γ : State) n f x' :
    KInv γ -> fibers γ n = Some f -> base x' = base (fcomp f) ->
    ProvF Σ prog' (next γ) (mkFiber Σ x' (fparent f) (disposed f) (life f)) ->
    WF (set_fiber Σ γ n (mkFiber Σ x' (fparent f) (disposed f) (life f))) ->
    Prov Σ prog' (set_fiber Σ γ n (mkFiber Σ x' (fparent f) (disposed f) (life f))) /\
    PidUnique Σ (set_fiber Σ γ n (mkFiber Σ x' (fparent f) (disposed f) (life f))) /\
    KSpawnProv (set_fiber Σ γ n (mkFiber Σ x' (fparent f) (disposed f) (life f))).
  Proof.
    intros [W [PF PT] U X _] Hn Eb PFn W'.
    set (f' := mkFiber Σ x' (fparent f) (disposed f) (life f)).
    assert (Hb : forall m fm, fibers (set_fiber Σ γ n f') m = Some fm ->
                 exists fm0, fibers γ m = Some fm0 /\ life fm = life fm0 /\
                             base (fcomp fm) = base (fcomp fm0)).
    { intros m fm H; rewrite fibers_refiber in H.
      destruct (Nat.eqb_spec m n) as [->|]; [injection H as <-; exists f; auto|].
      exists fm; auto. }
    split; [split|split].
    - intros m fm H; rewrite fibers_refiber in H; cbn [Calculus.next set_fiber with_fibers].
      destruct (Nat.eqb_spec m n) as [->|]; [injection H as <-; exact PFn | exact (PF m fm H)].
    - intros m1 m2 f1 f2 k1 p1 g1 k2 p2 g2 t Hne H1 H2 I1 I2.
      destruct (Hb m1 f1 H1) as (f1' & H1' & E1 & _), (Hb m2 f2 H2) as (f2' & H2' & E2 & _).
      rewrite E1 in I1; rewrite E2 in I2; exact (PT m1 m2 f1' f2' k1 p1 g1 k2 p2 g2 t Hne H1' H2' I1 I2).
    - exact U.
    - intros y fy m fm Hy Hu Hm.
      destruct (Hb y fy Hy) as (fy' & Hy' & Ey & Cy), (Hb m fm Hm) as (fm' & Hm' & Em & Cm).
      rewrite Cy, Cm; rewrite Ey in Hu; exact (X y fy' m fm' Hy' Hu Hm').
  Qed.

  (** Stamping does not change the operations a lifted program performs. *)
  Lemma opat_lift_tick (x : XC) t j k a (Q : @Prog N Σ C) :
    OpAt Σ k a (lift x j Q) ->
    OpAt Σ k a (lift (mkXC (base x) (scope x) (env x) (sel x) t) j Q).
  Proof.
    revert j; induction Q as [| |y b κ IH|y s Q IH|c Q IH]; intros j; cbn [Scoped.lift]; intros H;
      inversion H; subst.
    - apply at_here.
    - eapply at_cont; apply IH; eassumption.
    - apply at_prov; apply IH; assumption.
    - apply at_spawn; apply IH; assumption.
  Qed.

  Lemma kinv_recomp (γ : State) n f :
    KInv γ -> fibers γ n = Some f -> life f = Inactive Σ None -> fparent f = None -> KInv (recomp γ n f).
  Proof.
    intros I Hn Hl Hp.
    assert (Hi : is_installed Σ (life f) = false) by (rewrite Hl; reflexivity).
    pose proof (wf_recomp N_eq_dec Σ xprog γ n f (ki_wf _ I) Hn Hi) as W'.
    unfold Scoped.recomp in W' |- *.
    destruct (kinv_refiber4 γ n f (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f)) (choose γ (base (fcomp f))) (tick (fcomp f))) I Hn eq_refl
                (ProvF_inactive Σ prog' _ (mkFiber Σ _ (fparent f) (disposed f) (life f)) None Hl) W') as (P' & U' & X').
    split; auto.
    apply si_recomp_gen; [exact (ki_wf _ I) | exact (ki_si _ I) | exact Hn | reflexivity | reflexivity
                          | rewrite Hl; discriminate | right; rewrite Hl; auto].
  Qed.

  Lemma kinv_retick (γ : State) n f acc w :
    KInv γ -> fibers γ n = Some f -> life f = Active Σ acc w -> KInv (retick γ n f).
  Proof.
    intros I Hn Hl.
    pose proof (wf_retick N_eq_dec Σ xprog γ n f (ki_wf _ I) Hn) as W'.
    unfold Scoped.retick in W' |- *.
    assert (PFn : ProvF Σ prog' (next γ)
              (mkFiber Σ (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f)) (sel (fcomp f)) (next γ))
                       (fparent f) (disposed f) (life f))).
    { destruct (pv_fib Σ prog' γ (ki_prov _ I) n f Hn) as [_ H2]; split.
      - intros P acc' w' L; cbn in L; rewrite Hl in L; discriminate.
      - intros k p t g Hin; cbn in Hin; destruct (H2 k p t g Hin) as (Hp & Ht & a & s & s' & o & Ho & Hr).
        repeat split; auto; exists a, s, s', o; split; [|exact Hr].
        cbn [Calculus.comp Scoped.prog' body base]; apply opat_lift_tick; exact Ho. }
    destruct (kinv_refiber4 γ n f (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f)) (sel (fcomp f)) (next γ)) I Hn eq_refl PFn W') as (P' & U' & X').
    split; auto.
    apply si_recomp_gen; [exact (ki_wf _ I) | exact (ki_si _ I) | exact Hn | reflexivity | reflexivity
                          | rewrite Hl; discriminate | left; reflexivity].
  Qed.

  (** ** The rank obligation *)

  (** A provider of a name sits below every component depending on that
      name, private or exported; a parent sits below what it spawns. *)
  Definition KAbove (c c' : C) : Prop :=
    (exists y, In y (xprovs c) /\ In y (dnames c')) \/ KSpawns c c'.

  Variable Kb : nat.
  Hypothesis kHK : forall c, Termination.Bounded Σ Kb (xbody Σ (xprog c)).
  Variable xrank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', KAbove c c' -> xrank c < xrank c'.
  Hypothesis Hbnd : forall c, xrank c <= Rb.

  Local Notation frank f := (xrank (base (fcomp f))).
  Local Notation rank' := (fun x : XC => xrank (base x)).
  Local Notation Bm := (Bm Kb).
  Local Notation muU := (muU Σ Kb).
  Local Notation dflag := (dflag Σ).
  Local Notation Wt := (Wt Σ).
  Local Notation childflag := (childflag Σ).

  Lemma provs_name (x : XC) k :
    kmem kdec k (provs Σ (prog' x)) = true -> In (snd k) (xprovs (base x)).
  Proof.
    intros H; apply (kmem_In kdec) in H; cbn [Scoped.prog' provs] in H.
    apply in_map_iff in H as (y & <- & Hy); exact Hy.
  Qed.

  Lemma above_G (γ : State) x y :
    KSpawnProv γ -> Above Σ (progG γ) x y -> xrank (base x) < xrank (base y).
  Proof.
    intros XP [(k & Hp & Hd)|Hs]; apply Hrank.
    - left; exists (snd k); split.
      + unfold progG in Hp; cbn [provs] in Hp; cbn [Scoped.prog' provs] in Hp.
        apply in_map_iff in Hp as (y0 & <- & Hy0); exact Hy0.
      + unfold progG in Hd; cbn [deps Scoped.prog'] in Hd.
        apply in_map_iff in Hd as (d & <- & Hd); apply in_map_iff; exists d; split; [|exact Hd].
        destruct d; reflexivity.
    - right; exact (spawns_G γ x y XP Hs).
  Qed.

  Lemma bounded_lift (x : XC) i j (P : @Prog N Σ C) :
    Termination.Bounded Σ j P -> Termination.Bounded Σ j (lift x i P).
  Proof. intros H; revert i; induction H; intros i; cbn; constructor; auto. Qed.

  Lemma HKG (γ : State) : forall c, Termination.Bounded Σ Kb (body Σ (progG γ c)).
  Proof. intros x; unfold progG; cbn [body Scoped.prog']; apply bounded_lift, kHK. Qed.

  (** ** The invariant with the termination bookkeeping *)
  Definition KTInv (γ : State) : Prop := KInv γ /\ LoadBound Σ Kb γ /\ SpawnOwn Σ γ.

  Lemma ktinv_init : KTInv (@init Key Σ XC).
  Proof.
    split; [exact kinv_init|]; split; [intros n f P acc w H; discriminate|].
    intros x f m fm H; discriminate.
  Qed.

  Lemma HrG (γ : State) : KSpawnProv γ -> forall x y, Above Σ (progG γ) x y -> rank' x < rank' y.
  Proof. intros XP x y HA; exact (above_G γ x y XP HA). Qed.

  Lemma tg (γ : State) : KTInv γ -> TInv kdec Σ (progG γ) Kb γ.
  Proof.
    intros [[W P U X _] [LB SO]].
    exact (Build_TInv _ _ _ _ _ (wf_G γ γ W) (prov_G γ γ P) (inv2_G γ W U) LB SO).
  Qed.

  Lemma step_G_lc (γ0 γ γ' : State) ℓ : step γ ℓ = Some γ' ->
    Calculus.step kdec Σ (progG γ0) γ ℓ = Some γ'.
  Proof. exact (step_G_any γ0 γ γ' ℓ). Qed.

  Lemma ktinv_core (γ γ' : State) ℓ :
    KTInv γ -> step γ ℓ = Some γ' -> LoadBound Σ Kb γ' /\ SpawnOwn Σ γ'.
  Proof.
    intros X H.
    pose proof (tinv_step kdec Σ (progG γ) Kb (HKG γ) γ γ' ℓ (tg γ X) (step_G_lc γ γ γ' ℓ H)) as T.
    split; [exact (t_lb _ _ _ _ _ T) | exact (t_so _ _ _ _ _ T)].
  Qed.

  Lemma lbso_refiber (γ : State) n f x' :
    LoadBound Σ Kb γ -> SpawnOwn Σ γ -> fibers γ n = Some f ->
    (forall P acc w, life f <> Loading Σ P acc w) ->
    LoadBound Σ Kb (set_fiber Σ γ n (mkFiber Σ x' (fparent f) (disposed f) (life f))) /\
    SpawnOwn Σ (set_fiber Σ γ n (mkFiber Σ x' (fparent f) (disposed f) (life f))).
  Proof.
    intros LB SO Hn NL.
    assert (Hb : forall m fm, fibers (set_fiber Σ γ n (mkFiber Σ x' (fparent f) (disposed f) (life f))) m = Some fm ->
                 exists fm0, fibers γ m = Some fm0 /\ life fm = life fm0 /\ fparent fm = fparent fm0).
    { intros m fm H; rewrite fibers_refiber in H.
      destruct (Nat.eqb_spec m n) as [->|]; [injection H as <-; exists f; auto | exists fm; auto]. }
    split.
    - intros m fm P acc w H Hl; destruct (Hb m fm H) as (fm0 & H0 & El & _).
      rewrite El in Hl; exact (LB m fm0 P acc w H0 Hl).
    - intros y fy m fm Hy Hu Hm.
      destruct (Hb y fy Hy) as (fy0 & Hy0 & Ely & _), (Hb m fm Hm) as (fm0 & Hm0 & _ & Ep).
      rewrite Ely in Hu; rewrite Ep; exact (SO y fy0 m fm0 Hy0 Hu Hm0).
  Qed.

  Lemma ktinv_recomp (γ : State) n f :
    KTInv γ -> fibers γ n = Some f -> life f = Inactive Σ None -> fparent f = None -> KTInv (recomp γ n f).
  Proof.
    intros [I [LB SO]] Hn Hl Hp; split; [exact (kinv_recomp γ n f I Hn Hl Hp)|].
    apply lbso_refiber; auto; rewrite Hl; discriminate.
  Qed.

  Lemma ktinv_retick (γ : State) n f acc w :
    KTInv γ -> fibers γ n = Some f -> life f = Active Σ acc w -> KTInv (retick γ n f).
  Proof.
    intros [I [LB SO]] Hn Hl; split; [exact (kinv_retick γ n f acc w I Hn Hl)|].
    apply lbso_refiber; auto; rewrite Hl; discriminate.
  Qed.

  Lemma ktinv_core_full (γ γ' : State) ℓ :
    KTInv γ -> step γ ℓ = Some γ' -> SI γ' -> KTInv γ'.
  Proof.
    intros X H S'.
    destruct (kinv_core4 γ γ' ℓ (proj1 X) H) as (W' & P' & U' & X').
    split; [split; auto | exact (ktinv_core γ γ' ℓ X H)].
  Qed.

  Theorem ktinv_step (γ γ' : State) ℓ : KTInv γ -> kstep γ ℓ = Some γ' -> KTInv γ'.
  Proof.
    intros X H.
    pose proof (si_kstep N_eq_dec Σ xprog γ γ' ℓ (ki_wf _ (proj1 X)) (ki_si _ (proj1 X)) H) as S'.
    destruct (kstep_core N_eq_dec Σ xprog γ γ' ℓ H)
      as [St|[(m & f & _ & Hm & Hl & _ & Hp & St)|[(m & St)|(m & i & f & _ & Hm & St)]]].
    - exact (ktinv_core_full γ γ' _ X St S').
    - exact (ktinv_core_full _ γ' _ (ktinv_recomp γ m f X Hm Hl Hp) St S').
    - exact (ktinv_core_full γ γ' _ X St S').
    - destruct (life f) as [| |acc w|] eqn:Hl;
        try (cbn [Calculus.step] in St; unfold Scoped.retick in St; rewrite fibers_refiber, Nat.eqb_refl in St;
             cbn [Calculus.life] in St; rewrite Hl in St; discriminate St).
      exact (ktinv_core_full _ γ' _ (ktinv_retick γ m f acc w X Hm Hl) St S').
  Qed.

  (** ** What a step of [n] may do *)
  Definition KEffects (γ γ' : State) n (fn : Fiber) : Prop :=
    (forall x fx, x <> n -> fibers γ x = Some fx ->
       fibers γ' x = Some fx \/
       (fibers γ' x = Some (mkFiber Σ (fcomp fx) (fparent fx) true (life fx)) /\
        In (USpawn Σ x) (acc_of (life fn)))) /\
    (forall x fx', fibers γ x = None -> fibers γ' x = Some fx' -> x = next γ /\ frank fn < frank fx') /\
    (forall fn', fibers γ' n = Some fn' -> fcomp fn' = fcomp fn /\ disposed fn' = disposed fn) /\
    (fibers γ' n = None -> disposed fn = true) /\
    BindsOK kdec Σ prog' γ γ' fn.

  Lemma keffects_core (γ γ' : State) n ℓ fn :
    KTInv γ -> In ℓ (@lifecycle_labels XC n) -> step γ ℓ = Some γ' -> fibers γ n = Some fn ->
    KEffects γ γ' n fn.
  Proof.
    intros X Hin H Hn.
    pose proof (ki_spawn _ (proj1 X)) as XP.
    destruct (lstep_effects kdec Σ (progG γ) Kb rank' (HrG γ XP) γ γ' n ℓ fn (tg γ X) Hin
                (step_G_lc γ γ γ' ℓ H) Hn) as (E1 & E2 & E3 & E5 & EB).
    split; [exact E1|]; split; [|split; [exact E3 | split; [exact E5 | exact EB]]].
    intros x fx' Hx Hx'; destruct (E2 x fx' Hx Hx') as [Ex Hs]; split; [exact Ex|].
    exact (HrG γ XP _ _ (or_intror (or_introl Hs))).
  Qed.

  Lemma keffects_relife (γ : State) n fn (l : Life) :
    fibers γ n = Some fn -> KEffects γ (set_life Σ γ n fn l) n fn.
  Proof.
    intros Hn; split; [|split; [|split; [|split]]].
    - intros x fx Hxn Hx; left; rewrite fibers_set_life.
      destruct (Nat.eqb_spec x n); [contradiction | exact Hx].
    - intros x fx' Hx Hx'; rewrite fibers_set_life in Hx'.
      destruct (Nat.eqb_spec x n) as [->|_]; congruence.
    - intros fn' H; rewrite fibers_set_life, Nat.eqb_refl in H; injection H as <-; auto.
    - rewrite fibers_set_life, Nat.eqb_refl; discriminate.
    - intros k; left; reflexivity.
  Qed.

  (** ** Ranks *)
  Lemma child_rank_k (γ : State) n fn x fx :
    KTInv γ -> fibers γ n = Some fn -> In (USpawn Σ x) (acc_of (life fn)) ->
    fibers γ x = Some fx -> frank fn < frank fx.
  Proof.
    intros [[_ _ _ XP _] _] Hn Hin Hx; apply Hrank; right; exact (XP n fn x fx Hn Hin Hx).
  Qed.

  Lemma lower_same_k (γ γ' : State) n fn x fx :
    KTInv γ -> KEffects γ γ' n fn -> fibers γ n = Some fn ->
    x <> n -> fibers γ x = Some fx -> frank fx <= frank fn -> fibers γ' x = Some fx.
  Proof.
    intros I [E1 _] Hn Hxn Hx Hr.
    destruct (E1 x fx Hxn Hx) as [H|[_ Hin]]; [exact H|].
    pose proof (child_rank_k γ n fn x fx I Hn Hin Hx); lia.
  Qed.

  (** Keys a component reads: those named by its dependencies, whatever
      their scope (the scope may change with the selection). *)
  Definition KeyOf (c : C) (k : Key) : Prop := In (snd k) (dnames c).

  Lemma prov_rank_k (fo : Fiber) c k :
    kmem kdec k (fprovs Σ prog' fo) = true -> KeyOf c k -> frank fo < xrank c.
  Proof.
    intros Hk Hc; apply Hrank; left; exists (snd k); split; [|exact Hc].
    exact (provs_name _ k Hk).
  Qed.

  Lemma vis_stable (γ γ' : State) n fn c k :
    KTInv γ -> KEffects γ γ' n fn -> fibers γ n = Some fn ->
    KeyOf c k -> xrank c <= frank fn -> visible Σ γ' k = visible Σ γ k.
  Proof.
    intros I EF Hn Hk Hr.
    pose proof EF as (_ & _ & _ & _ & EB).
    pose proof (ki_wf _ (proj1 I)) as W.
    assert (Owner : forall b, binds γ k = Some b -> fibers γ' (owner b) = fibers γ (owner b)).
    { intros b Hb.
      destruct (wf_bind kdec Σ prog' γ W k b Hb) as (fo & Ho & _ & Hko & _).
      pose proof (prov_rank_k fo c k Hko Hk) as Hlt.
      assert (Hon : owner b <> n).
      { intros Heq; rewrite Heq, Hn in Ho; injection Ho as <-; lia. }
      rewrite Ho; exact (lower_same_k γ γ' n fn (owner b) fo I EF Hn Hon Ho ltac:(lia)). }
    destruct (EB k) as [Eq|[(b & b' & Hb & Hb' & Hp & Ho)|Hkm]].
    - unfold visible; rewrite Eq.
      destruct (binds γ k) as [b|] eqn:Hb; [|reflexivity].
      rewrite (Owner b eq_refl); reflexivity.
    - unfold visible; rewrite Hb, Hb', Ho, Hp, (Owner b Hb); reflexivity.
    - pose proof (prov_rank_k fn c k Hkm Hk); lia.
  Qed.

  Lemma resolve_stable_k (γ γ' : State) n fn c ks :
    KTInv γ -> KEffects γ γ' n fn -> fibers γ n = Some fn -> xrank c <= frank fn ->
    (forall k, In k ks -> KeyOf c k) -> resolve Σ γ' ks = resolve Σ γ ks.
  Proof.
    intros I EF Hn Hr; induction ks as [|k ks IH]; intros Hks; cbn; [reflexivity|].
    rewrite (vis_stable γ γ' n fn c k I EF Hn (Hks k (or_introl eq_refl)) Hr).
    rewrite IH; [reflexivity|]; intros k' Hk'; apply Hks; right; exact Hk'.
  Qed.

  Lemma deps_keyof (x : XC) k : In k (deps Σ (prog' x)) -> KeyOf (base x) k.
  Proof.
    cbn [Scoped.prog' deps]; intros H; apply in_map_iff in H as (d & <- & Hd).
    unfold KeyOf; apply in_map_iff; exists d; split; [destruct d; reflexivity | exact Hd].
  Qed.

  (** ** Selections are stable below the stepping fiber *)
  Lemma nmem_In y l : nmem N_eq_dec y l = true -> In y l.
  Proof.
    unfold nmem; intros H; apply existsb_exists in H as (y' & Hy & E).
    unfold neqb in E; destruct (N_eq_dec y y') as [->|]; [exact Hy | discriminate].
  Qed.

  Lemma exports_provs c y : In y (xexports c) -> In y (xprovs c).
  Proof. intros H; unfold Scoped.xprovs; apply in_or_app; right; exact H. Qed.

  Lemma candidate_stable (γ γ' : State) n fn c y :
    KTInv γ -> KEffects γ γ' n fn -> fibers γ n = Some fn ->
    In y (dnames c) -> xrank c <= frank fn ->
    forall m, candidate γ' y m = candidate γ y m.
  Proof.
    intros I EF Hn Hy Hr m.
    pose proof EF as (E1 & E2 & E3 & E5 & _).
    assert (Low : forall fm : Fiber, nmem N_eq_dec y (xexports (base (fcomp fm))) = true -> frank fm < xrank c).
    { intros fm E; apply Hrank; left; exists y; split; [|exact Hy].
      apply exports_provs, nmem_In; exact E. }
    unfold Scoped.candidate.
    destruct (fibers γ m) as [fm|] eqn:Hm.
    - destruct (Nat.eq_dec m n) as [->|Hmn].
      + rewrite Hn in Hm; injection Hm as <-.
        destruct (nmem N_eq_dec y (xexports (base (fcomp fn)))) eqn:E.
        { pose proof (Low fn E); lia. }
        destruct (fibers γ' n) as [fn'|] eqn:Hn'; [|reflexivity].
        destruct (E3 fn' eq_refl) as [-> _]; rewrite E; reflexivity.
      + assert (Hc : exists fm', fibers γ' m = Some fm' /\ fcomp fm' = fcomp fm).
        { destruct (E1 m fm Hmn Hm) as [H|[H _]]; eexists; split; [exact H| reflexivity | exact H | reflexivity]. }
        destruct Hc as (fm' & Hm' & Ec); rewrite Hm', Ec.
        destruct (nmem N_eq_dec y (xexports (base (fcomp fm)))) eqn:E; [|reflexivity].
        rewrite (vis_stable γ γ' n fn c (scope (fcomp fm), y) I EF Hn Hy Hr); reflexivity.
    - destruct (fibers γ' m) as [fx'|] eqn:Hm'; [|reflexivity].
      destruct (E2 m fx' Hm Hm') as [_ Hlt].
      destruct (nmem N_eq_dec y (xexports (base (fcomp fx')))) eqn:E; [|reflexivity].
      pose proof (Low fx' E); lia.
  Qed.

  Lemma omap_app {A B} (g : A -> option B) l1 l2 : omap g (l1 ++ l2) = omap g l1 ++ omap g l2.
  Proof. induction l1 as [|a l1 IH]; cbn; [reflexivity|]; destruct (g a); rewrite IH; reflexivity. Qed.

  Lemma omap_nil {A B} (g : A -> option B) l : (forall a, In a l -> g a = None) -> omap g l = [].
  Proof.
    induction l as [|a l IH]; intros H; cbn; [reflexivity|].
    rewrite (H a (or_introl eq_refl)); apply IH; intros; apply H; right; auto.
  Qed.

  Lemma omap_ext_in {A B} (g g' : A -> option B) l : (forall a, In a l -> g' a = g a) -> omap g' l = omap g l.
  Proof.
    induction l as [|a l IH]; intros H; cbn; [reflexivity|].
    rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]; intros; apply H; right; auto.
  Qed.

  Lemma candidates_ext (γ : State) y M :
    WF γ -> next γ <= M -> candidates N_eq_dec Σ xprog γ y = omap (candidate γ y) (seq 0 M).
  Proof.
    intros W HM; unfold Scoped.candidates, names.
    replace M with (next γ + (M - next γ)) by lia.
    rewrite seq_app, omap_app, (omap_nil _ (seq (0 + next γ) _)), app_nil_r; [reflexivity|].
    intros x Hx; apply in_seq in Hx; unfold Scoped.candidate.
    destruct (fibers γ x) eqn:E; [|reflexivity].
    apply (wf_names kdec Σ prog' γ W) in E; lia.
  Qed.

  Lemma select_ext (γ γ' : State) y :
    WF γ -> WF γ' -> (forall m, candidate γ' y m = candidate γ y m) -> select γ' y = select γ y.
  Proof.
    intros W W' E; unfold Scoped.select.
    rewrite (candidates_ext γ' y (next γ + next γ') W') by lia.
    rewrite (candidates_ext γ y (next γ + next γ') W) by lia.
    rewrite (omap_ext_in _ _ _ (fun m _ => E m)); reflexivity.
  Qed.

  Lemma select_stable (γ γ' : State) n fn c y :
    KTInv γ -> WF γ' -> KEffects γ γ' n fn -> fibers γ n = Some fn ->
    In y (dnames c) -> xrank c <= frank fn -> select γ' y = select γ y.
  Proof.
    intros I W' EF Hn Hy Hr; apply select_ext; [exact (ki_wf _ (proj1 I)) | exact W'|].
    exact (candidate_stable γ γ' n fn c y I EF Hn Hy Hr).
  Qed.

  Lemma omap_In {A B} (g : A -> option B) l b : In b (omap g l) -> exists a, In a l /\ g a = Some b.
  Proof.
    induction l as [|a l IH]; cbn; [tauto|].
    destruct (g a) as [b'|] eqn:E.
    - intros [<-|H]; [exists a; auto|]; destruct (IH H) as (a' & ? & ?); exists a'; auto.
    - intros H; destruct (IH H) as (a' & ? & ?); exists a'; auto.
  Qed.

  Lemma In_omap {A B} (g : A -> option B) l a b : In a l -> g a = Some b -> In b (omap g l).
  Proof.
    induction l as [|a' l IH]; cbn; [tauto|].
    intros [<-|H] E; [rewrite E; left; reflexivity|].
    destruct (g a'); [right|]; apply IH; auto.
  Qed.

  Lemma globals_dname c y : In y (globals c) -> In y (dnames c).
  Proof.
    unfold Scoped.globals; intros H; apply omap_In in H as (d & Hd & E).
    destruct d as [y'|y']; [discriminate|]; injection E as ->.
    apply in_map_iff; exists (Global y); auto.
  Qed.

  Lemma globals_In c y : In (Global y) (xdeps c) -> In y (globals c).
  Proof. intros H; unfold Scoped.globals; exact (In_omap _ _ _ y H eq_refl). Qed.

  Lemma choose_ext (γ γ' : State) c :
    (forall y, In y (globals c) -> select γ' y = select γ y) -> choose γ' c = choose γ c.
  Proof.
    intros E; unfold Scoped.choose; apply map_ext_in; intros y Hy; rewrite E; auto.
  Qed.

  Lemma forallb_ext_in' {A} (g g' : A -> bool) l :
    (forall a, In a l -> g' a = g a) -> forallb g' l = forallb g l.
  Proof.
    induction l as [|a l IH]; intros H; cbn; [reflexivity|].
    rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]; intros; apply H; right; auto.
  Qed.

  Lemma all_selected_ext (γ γ' : State) c :
    (forall y, In y (globals c) -> select γ' y = select γ y) -> all_selected γ' c = all_selected γ c.
  Proof.
    intros E; unfold Scoped.all_selected; apply forallb_ext_in'; intros y Hy.
    unfold Scoped.selected; rewrite E; auto.
  Qed.

  Lemma fresh_ext (γ γ' : State) f f' :
    fcomp f' = fcomp f ->
    (forall y, In y (globals (base (fcomp f))) -> select γ' y = select γ y) -> fresh γ' f' = fresh γ f.
  Proof.
    intros Ec E; unfold Scoped.fresh; rewrite Ec, (all_selected_ext γ γ' _ E), (choose_ext γ γ' _ E).
    reflexivity.
  Qed.

  (** ** The target after choosing a selection *)
  Definition rcomp (γ : State) (x : XC) : XC :=
    mkXC (base x) (scope x) (env x) (choose γ (base x)) (tick x).

  Lemma assoc_map (F : N -> Scope) l y :
    In y l -> assoc N_eq_dec y (map (fun y => (y, F y)) l) = Some (F y).
  Proof.
    induction l as [|a l IH]; cbn; [tauto|]; intros H; unfold neqb.
    destruct (N_eq_dec y a) as [->|Hne]; [reflexivity|].
    destruct H as [->|H]; [contradiction Hne; reflexivity | exact (IH H)].
  Qed.

  Lemma fresh_all_selected (γ : State) f : fresh γ f = true -> all_selected γ (base (fcomp f)) = true.
  Proof.
    unfold Scoped.fresh; intros F; apply andb_true_iff in F; exact (proj1 F).
  Qed.

  Lemma deps_rcomp_fresh (γ : State) f :
    fresh γ f = true -> deps Σ (prog' (rcomp γ (fcomp f))) = deps Σ (prog' (fcomp f)).
  Proof.
    intros F; unfold Scoped.fresh in F; apply andb_true_iff in F as [_ F].
    destruct (list_eq_dec ns_eq_dec (sel (fcomp f)) (choose γ (base (fcomp f)))) as [Es|]; [|discriminate].
    cbn [Scoped.prog' deps]; unfold rcomp; cbn [base].
    apply map_ext; intros [y|y]; unfold Scoped.dkey; cbn [env sel]; [reflexivity|].
    rewrite <- Es; reflexivity.
  Qed.

  (** What choosing a selection would give as a target. *)
  Definition bt (γ : State) (n : nat) : option View :=
    match fibers γ n with
    | Some f => if disposed f then None
                else if all_selected γ (base (fcomp f))
                     then resolve Σ γ (deps Σ (prog' (rcomp γ (fcomp f)))) else None
    | None => None
    end.

  Lemma visible_refiber (γ : State) n f x' b k :
    fibers γ n = Some f ->
    visible Σ (set_fiber Σ γ n (mkFiber Σ x' (fparent f) b (life f))) k = visible Σ γ k.
  Proof.
    intros Hn; unfold visible.
    change (Calculus.binds Σ (set_fiber Σ γ n (mkFiber Σ x' (fparent f) b (life f)))) with (binds γ).
    destruct (binds γ k) as [bd|]; [|reflexivity].
    rewrite fibers_refiber; destruct (Nat.eqb_spec (owner bd) n) as [->|]; [|reflexivity].
    rewrite Hn; reflexivity.
  Qed.

  Lemma resolve_ext (γ1 γ2 : State) ks :
    (forall k, visible Σ γ1 k = visible Σ γ2 k) -> resolve Σ γ1 ks = resolve Σ γ2 ks.
  Proof. intros E; induction ks as [|k ks IH]; cbn; [reflexivity|]; rewrite E, IH; reflexivity. Qed.

  Lemma select_refiber (γ : State) n f x' b y :
    fibers γ n = Some f -> base x' = base (fcomp f) -> scope x' = scope (fcomp f) ->
    select (set_fiber Σ γ n (mkFiber Σ x' (fparent f) b (life f))) y = select γ y.
  Proof.
    intros Hn Eb Es; unfold Scoped.select, Scoped.candidates.
    change (names Σ (set_fiber Σ γ n (mkFiber Σ x' (fparent f) b (life f)))) with (names Σ γ).
    rewrite (omap_ext_in (candidate γ y)); [reflexivity|].
    intros m _; unfold Scoped.candidate; rewrite fibers_refiber.
    destruct (Nat.eqb_spec m n) as [->|].
    - rewrite Hn; cbn [Calculus.comp]; rewrite Eb, Es, (visible_refiber γ n f x' b) by exact Hn; reflexivity.
    - destruct (fibers γ m) as [fm|]; [|reflexivity].
      rewrite (visible_refiber γ n f x' b) by exact Hn; reflexivity.
  Qed.

  Lemma bt_recomp (γ : State) n f :
    fibers γ n = Some f -> all_selected γ (base (fcomp f)) = true -> target (recomp γ n f) n = bt γ n.
  Proof.
    intros Hn A; unfold Calculus.target, bt; rewrite Hn.
    unfold Scoped.recomp at 1; rewrite fibers_refiber, Nat.eqb_refl; cbn [Calculus.disposed Calculus.comp].
    destruct (disposed f); [reflexivity|]; rewrite A.
    apply resolve_ext; intros k; apply visible_refiber; exact Hn.
  Qed.

  Lemma bt_fresh (γ : State) n f : fibers γ n = Some f -> fresh γ f = true -> bt γ n = target γ n.
  Proof.
    intros Hn F; unfold bt, Calculus.target; rewrite Hn.
    destruct (disposed f); [reflexivity|].
    rewrite (fresh_all_selected γ f F), (deps_rcomp_fresh γ f F); reflexivity.
  Qed.

  (** Stability for a fiber of rank at most that of [n]. *)
  Lemma stable_fiber (γ γ' : State) n fn m fm fm' :
    KTInv γ -> WF γ' -> KEffects γ γ' n fn -> fibers γ n = Some fn ->
    fibers γ m = Some fm -> fibers γ' m = Some fm' ->
    fcomp fm' = fcomp fm -> disposed fm' = disposed fm -> frank fm <= frank fn ->
    target γ' m = target γ m /\ bt γ' m = bt γ m /\ fresh γ' fm' = fresh γ fm.
  Proof.
    intros I W' EF Hn Hm Hm' Hc Hd Hr.
    assert (Es : forall y, In y (globals (base (fcomp fm))) -> select γ' y = select γ y).
    { intros y Hy; exact (select_stable γ γ' n fn (base (fcomp fm)) y I W' EF Hn (globals_dname _ _ Hy) Hr). }
    split; [|split].
    - unfold Calculus.target; rewrite Hm, Hm', Hd, Hc.
      destruct (disposed fm); [reflexivity|].
      apply (resolve_stable_k γ γ' n fn (base (fcomp fm))); auto; apply deps_keyof.
    - unfold bt; rewrite Hm, Hm', Hd, Hc.
      destruct (disposed fm); [reflexivity|].
      rewrite (all_selected_ext γ γ' _ Es).
      destruct (all_selected γ (base (fcomp fm))); [|reflexivity].
      unfold rcomp; rewrite (choose_ext γ γ' _ Es).
      apply (resolve_stable_k γ γ' n fn (base (fcomp fm))); auto.
      intros k Hk; exact (deps_keyof _ k Hk).
    - exact (fresh_ext γ γ' fm fm' Hc Es).
  Qed.

  (** ** The measure *)
  Definition ktis (γ : State) (n : nat) (f : Fiber) (w : View) : bool :=
    fresh γ f && target_is γ n w.

  Definition kmu (γ : State) (n : nat) (f : Fiber) : nat :=
    match life f with
    | Inactive _ (Some _) => dflag f
    | Inactive _ None => match bt γ n with Some _ => Bm | None => dflag f end
    | Loading _ _ acc w =>
        if ktis γ n f w then 3 * Kb + 10 - length acc
        else 2 * Kb + 1 + muU γ f [] None (bt γ n) + (Kb - length acc)
    | Active _ acc w =>
        if ktis γ n f w then 0
        else muU γ f acc None (bt γ n) + 1
    | Unloading _ acc _ z => muU γ f acc z (bt γ n)
    end.

  Lemma own_item_ne_k (γ : State) n fn x :
    KTInv γ -> fibers γ n = Some fn -> In (USpawn Σ x) (acc_of (life fn)) -> x <> n.
  Proof. intros I Hn Hin ->; pose proof (child_rank_k γ n fn n fn I Hn Hin Hn); lia. Qed.

  (** ** The measure of the other fibers of rank at most that of [n] *)
  Lemma mu_other_k (γ γ' : State) n fn m fm :
    KTInv γ -> WF γ' -> KEffects γ γ' n fn -> fibers γ n = Some fn ->
    m <> n -> fibers γ m = Some fm -> frank fm <= frank fn ->
    fibers γ' m = Some fm /\ kmu γ' m fm = kmu γ m fm.
  Proof.
    intros I W' EF Hn Hmn Hm Hr.
    pose proof (lower_same_k γ γ' n fn m fm I EF Hn Hmn Hm Hr) as Hm'.
    split; [exact Hm'|].
    destruct (stable_fiber γ γ' n fn m fm fm I W' EF Hn Hm Hm' eq_refl eq_refl Hr) as (Ht & Hb & Hf).
    assert (Hfl : forall x, In (USpawn Σ x) (acc_of (life fm)) -> childflag γ' x = childflag γ x).
    { intros x Hx; destruct EF as (E1 & E2 & E3 & E5 & _).
      pose proof (proj2 (proj2 I)) as SO.
      unfold Termination.childflag.
      destruct (fibers γ x) as [fx|] eqn:Hfx.
      - destruct (Nat.eq_dec x n) as [->|Hxn].
        + rewrite Hn in Hfx; injection Hfx as <-.
          destruct (fibers γ' n) as [fn'|] eqn:Hn'.
          * destruct (E3 fn' eq_refl) as [_ ->]; reflexivity.
          * rewrite (E5 eq_refl); reflexivity.
        + destruct (E1 x fx Hxn Hfx) as [->|[_ Hinn]]; [reflexivity|].
          exfalso.
          pose proof (SO m fm x fx Hm Hx Hfx) as P1.
          pose proof (SO n fn x fx Hn Hinn Hfx) as P2.
          congruence.
      - destruct (fibers γ' x) as [fx'|] eqn:Hfx'; [|reflexivity].
        destruct (E2 x fx' Hfx Hfx') as [Hxe _].
        pose proof (wf_spawn_lt kdec Σ prog' γ (ki_wf _ (proj1 I)) m fm x Hm Hx); lia. }
    unfold kmu, ktis.
    destruct (life fm) as [[e|]|P acc w|acc w|acc w z] eqn:Hl.
    - reflexivity.
    - rewrite Hb; reflexivity.
    - rewrite Hf; unfold target_is; rewrite Ht, Hb; reflexivity.
    - rewrite Hf; unfold target_is; rewrite Ht, Hb; unfold Termination.muU.
      rewrite (Wt_ext Σ γ γ' acc); [reflexivity|].
      intros x Hx; apply Hfl; exact Hx.
    - rewrite Hb; unfold Termination.muU.
      rewrite (Wt_ext Σ γ γ' acc); [reflexivity|].
      intros x Hx; apply Hfl; exact Hx.
  Qed.

  Lemma ktis_false (γ : State) n f w : target_is γ n w = false -> ktis γ n f w = false.
  Proof. intros H; unfold ktis; rewrite H, andb_false_r; reflexivity. Qed.

  (** ** The measure of [n] drops at a core lifecycle step of [n] *)
  Lemma mu_drop_core (γ γ' : State) n ℓ fn :
    KTInv γ -> In ℓ (@lifecycle_labels XC n) -> step γ ℓ = Some γ' -> fibers γ n = Some fn ->
    ((ℓ = LBegin n \/ ℓ = LStep n) -> fresh γ fn = true) ->
    match fibers γ' n with Some fn' => kmu γ' n fn' | None => 0 end < kmu γ n fn.
  Proof.
    intros I Hin H Hn Hfr.
    pose proof (keffects_core γ γ' n ℓ fn I Hin H Hn) as EF.
    pose proof (preservation kdec Σ prog' γ γ' ℓ (ki_wf _ (proj1 I)) H) as W'.
    pose proof EF as (_ & _ & E3 & _ & _).
    assert (Hst : forall fn', fibers γ' n = Some fn' ->
              target γ' n = target γ n /\ bt γ' n = bt γ n /\ fresh γ' fn' = fresh γ fn).
    { intros fn' Hn'; destruct (E3 fn' Hn') as [Hc Hd].
      exact (stable_fiber γ γ' n fn n fn fn' I W' EF Hn Hn Hn' Hc Hd (le_n _)). }
    clear W'.
    assert (Hrl : forall γ1 (l : Life), fibers (set_life Σ γ1 n fn l) n =
                    Some (mkFiber Σ (fcomp fn) (fparent fn) (disposed fn) l))
      by (intros; rewrite fibers_set_life, Nat.eqb_refl; reflexivity).
    pose proof (proj1 (proj2 I)) as LB.
    cbn in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
      pose proof H as H0; cbn [Calculus.step] in H; rewrite Hn in H.
    - (* LBegin *)
      pose proof (Hfr (or_introl eq_refl)) as F.
      destruct (life fn) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (target γ n) as [w|] eqn:Htg; [|discriminate]; injection H as <-.
      rewrite Hrl; destruct (Hst _ (Hrl _ _)) as (Ht & _ & Hf).
      unfold kmu, ktis; cbn [life]; rewrite Hl, (bt_fresh γ n fn Hn F), Htg, Hf, F.
      rewrite (proj2 (target_is_spec kdec Σ prog' _ n w) ltac:(rewrite Ht; first [exact Htg | reflexivity])); cbn; lia.
    - (* LStep *)
      pose proof (Hfr (or_intror eq_refl)) as F.
      destruct (life fn) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (may_step kdec Σ prog' γ n P w) eqn:Hms; [|discriminate]; injection H as <-.
      destruct (LB n fn P acc w Hn Hl) as [Hlen HbP].
      destruct (target_is γ n w) eqn:Hti.
      2: {
      assert (HnD : P <> PDone) by (intros ->; cbn in Hms; congruence).
      set (T := muU γ fn [] None (bt γ n)).
      assert (Hmu : kmu γ n fn = 2 * Kb + 1 + T + (Kb - length acc))
        by (unfold kmu, ktis; rewrite Hl, F, Hti; reflexivity).
      rewrite Hmu.
      assert (Goal : forall γ1 (l : Life),
                (target (set_life Σ γ1 n fn l) n = target γ n /\
                 bt (set_life Σ γ1 n fn l) n = bt γ n /\
                 fresh (set_life Σ γ1 n fn l) (mkFiber Σ (fcomp fn) (fparent fn) (disposed fn) l) = fresh γ fn) ->
                (match l with
                 | Unloading _ acc' _ (Some _) => acc' = acc
                 | Loading _ _ acc' w' => length acc' = S (length acc) /\ w' = w /\ length acc < Kb
                 | _ => False
                 end) ->
                kmu (set_life Σ γ1 n fn l) n (mkFiber Σ (fcomp fn) (fparent fn) (disposed fn) l)
                < 2 * Kb + 1 + T + (Kb - length acc)).
      { intros γ1 l (Ht' & Hb' & Hf') Hshape.
        unfold kmu, ktis; cbn [life].
        destruct l as [z'|P' acc' w'|acc' w'|acc' w' [e|]]; try contradiction.
        - destruct Hshape as (Hla & -> & Hlt).
          rewrite Hf', F; unfold target_is; rewrite Ht'; fold (target_is γ n w); rewrite Hti, Hb'; cbn [andb].
          unfold T, Termination.muU, Termination.dflag; cbn [Termination.Wt disposed].
          destruct (bt γ n); destruct (disposed fn); unfold Bm; lia.
        - subst acc'; unfold T, Termination.muU, Termination.dflag; cbn [Termination.Wt disposed].
          match goal with |- context [Termination.Wt _ ?g acc] => pose proof (Wt_le Σ g acc) end.
          destruct (bt γ n); destruct (bt (set_life Σ γ1 n fn (Unloading Σ acc w' (Some e))) n);
            destruct (disposed fn); unfold Bm; lia. }
      Ltac finx2 Goal Hst Hrl :=
        rewrite Hrl; apply Goal; [apply Hst; apply Hrl | cbn; repeat split; auto].
      destruct P as [| |k a κ|k s P'|c P'].
      + contradiction.
      + cbn [load_step] in Hst |- *; finx2 Goal Hst Hrl.
      + assert (Hlt : length acc < Kb) by (inversion HbP; lia).
        rewrite (load_step_op kdec Σ prog' γ n fn k a κ acc w) in Hst |- *.
        destruct (op_binding kdec Σ prog' γ n fn k w) as [b|]; [|finx2 Goal Hst Hrl].
        destruct (run a (next γ) (bst Σ b)) as [[[s' g] o]|]; finx2 Goal Hst Hrl.
      + assert (Hlt : length acc < Kb) by (inversion HbP; lia).
        cbn [load_step] in Hst |- *.
        destruct (kmem kdec k (provs Σ (prog' (fcomp fn)))); [|finx2 Goal Hst Hrl].
        destruct (binds γ k); finx2 Goal Hst Hrl.
      + assert (Hlt : length acc < Kb) by (inversion HbP; lia).
        cbn [load_step] in Hst |- *.
        destruct (conflict kdec Σ prog' γ c); finx2 Goal Hst Hrl. }
      assert (Hmu : kmu γ n fn = 3 * Kb + 10 - length acc)
        by (unfold kmu, ktis; rewrite Hl, F, Hti; reflexivity).
      rewrite Hmu.
      assert (Goal : forall γ1 (l : Life),
                (target (set_life Σ γ1 n fn l) n = target γ n /\
                 bt (set_life Σ γ1 n fn l) n = bt γ n /\
                 fresh (set_life Σ γ1 n fn l) (mkFiber Σ (fcomp fn) (fparent fn) (disposed fn) l) = fresh γ fn) ->
                (match l with
                 | Active _ acc' w' => acc' = acc /\ w' = w
                 | Unloading _ acc' _ (Some _) => acc' = acc
                 | Loading _ _ acc' w' => length acc' = S (length acc) /\ w' = w
                 | _ => False
                 end) ->
                kmu (set_life Σ γ1 n fn l) n (mkFiber Σ (fcomp fn) (fparent fn) (disposed fn) l)
                < 3 * Kb + 10 - length acc).
      { intros γ1 l (Ht' & _ & Hf') Hshape.
        unfold kmu, ktis; cbn [life].
        destruct l as [z'|P' acc' w'|acc' w'|acc' w' [e|]]; try contradiction.
        - destruct Hshape as [Hla ->].
          rewrite Hf', F; unfold target_is; rewrite Ht'; fold (target_is γ n w); rewrite Hti; cbn; lia.
        - destruct Hshape as [-> ->].
          rewrite Hf', F; unfold target_is; rewrite Ht'; fold (target_is γ n w); rewrite Hti; cbn; lia.
        - subst acc'; unfold Termination.muU, Termination.dflag; cbn.
          pose proof (Wt_le Σ (set_life Σ γ1 n fn (Unloading Σ acc w' (Some e))) acc).
          destruct (disposed fn); lia. }
      Ltac finx Goal Hst Hrl :=
        rewrite Hrl; apply Goal; [apply Hst; apply Hrl | cbn; auto].
      destruct P as [| |k a κ|k s P'|c P'].
      + cbn [load_step] in Hst |- *; finx Goal Hst Hrl.
      + cbn [load_step] in Hst |- *; finx Goal Hst Hrl.
      + rewrite (load_step_op kdec Σ prog' γ n fn k a κ acc w) in Hst |- *.
        destruct (op_binding kdec Σ prog' γ n fn k w) as [b|]; [|finx Goal Hst Hrl].
        destruct (run a (next γ) (bst Σ b)) as [[[s' g] o]|]; finx Goal Hst Hrl.
      + cbn [load_step] in Hst |- *.
        destruct (kmem kdec k (provs Σ (prog' (fcomp fn)))); [|finx Goal Hst Hrl].
        destruct (binds γ k); finx Goal Hst Hrl.
      + cbn [load_step] in Hst |- *.
        destruct (conflict kdec Σ prog' γ c); finx Goal Hst Hrl.
    - (* LDivert *)
      destruct (life fn) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is γ n w) eqn:Hti; [discriminate|]; injection H as <-.
      rewrite Hrl; destruct (Hst _ (Hrl _ _)) as (_ & Hb & _).
      unfold kmu; cbn [life]; rewrite Hl, (ktis_false γ n fn w Hti), Hb.
      destruct (LB n fn P acc w Hn Hl) as [Hlen _].
      unfold Termination.muU, Termination.dflag; cbn [Termination.Wt disposed].
      match goal with |- context [Termination.Wt _ ?g acc] => pose proof (Wt_le Σ g acc) end.
      destruct (bt γ n); destruct (disposed fn); unfold Bm; lia.
    - (* LLeave *)
      destruct (life fn) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (target_is γ n w) eqn:Hti; [discriminate|]; injection H as <-.
      rewrite Hrl; destruct (Hst _ (Hrl _ _)) as (_ & Hb & _).
      unfold kmu; cbn [life]; rewrite Hl, (ktis_false γ n fn w Hti), Hb.
      unfold Termination.muU; rewrite (Wt_ext Σ γ _ acc); [unfold Termination.dflag; cbn; lia|].
      intros x Hx; apply childflag_relife; [reflexivity|].
      apply (own_item_ne_k γ n fn x I Hn); rewrite Hl; exact Hx.
    - (* LUndo *)
      destruct (life fn) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      destruct (undo_step_shape kdec Σ γ γ' n fn u acc w z H) as (γ1 & -> & E).
      rewrite Hrl; destruct (Hst _ (Hrl _ _)) as (_ & Hb & _).
      unfold kmu; cbn [life]; rewrite Hl, Hb.
      unfold Termination.muU; cbn [Termination.Wt].
      rewrite (Wt_ext Σ γ _ acc); [unfold Termination.dflag; cbn; destruct u; cbn; lia|].
      intros x Hx; apply childflag_relife; [exact E|].
      apply (own_item_ne_k γ n fn x I Hn); rewrite Hl; right; exact Hx.
    - (* LRetireChild *)
      destruct (life fn) as [| | |[|[k p t g|k p|mm] acc] w z] eqn:Hl; try discriminate.
      destruct (fibers γ mm) as [g|] eqn:Hg; [|discriminate].
      unheld H; destruct (disposed g) eqn:Hdg; [discriminate|]; injection H as <-.
      assert (Hmn : mm <> n)
        by (apply (own_item_ne_k γ n fn mm I Hn); rewrite Hl; left; reflexivity).
      assert (Hn' : fibers (set_fiber Σ γ mm (mkFiber Σ (fcomp g) (fparent g) true (life g))) n
                    = Some fn).
      { cbn; unfold fupd; destruct (Nat.eqb_spec n mm); [congruence | exact Hn]. }
      rewrite Hn'; destruct (Hst _ Hn') as (_ & Hb & _).
      unfold kmu; rewrite Hl, Hb.
      unfold Termination.muU; cbn [Termination.Wt Termination.wt].
      assert (Hf : childflag (set_fiber Σ γ mm (mkFiber Σ (fcomp g) (fparent g) true (life g))) mm = 0)
        by (unfold Termination.childflag; cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity).
      assert (Hf0 : childflag γ mm = 1) by (unfold Termination.childflag; rewrite Hg, Hdg; reflexivity).
      assert (Hm : Wt (set_fiber Σ γ mm (mkFiber Σ (fcomp g) (fparent g) true (life g))) acc
                   <= Wt γ acc).
      { apply Wt_mono; intros x _; unfold Termination.childflag; cbn; unfold fupd.
        destruct (Nat.eqb_spec x mm) as [->|_]; [rewrite Hg, Hdg; cbn; lia | apply Nat.le_refl]. }
      rewrite Hf, Hf0; lia.
    - (* LUnloaded *)
      destruct (life fn) as [| | |[|u acc] w z] eqn:Hl; try discriminate; injection H as <-.
      rewrite Hrl; destruct (Hst _ (Hrl _ _)) as (_ & Hb & _).
      unfold kmu; cbn [life]; rewrite Hl, Hb.
      unfold Termination.muU; cbn [Termination.Wt].
      destruct z as [e|]; cbn; [unfold Termination.dflag; cbn; lia|].
      destruct (bt γ n); unfold Termination.dflag; cbn; lia.
    - (* LRemove *)
      destruct (life fn) as [z| | |] eqn:Hl; try discriminate.
      destruct (disposed fn) eqn:Hd; [|discriminate]; cbn in H.
      destruct (negb (has_child Σ γ n)); [|discriminate]; injection H as <-.
      cbn; unfold fupd; rewrite Nat.eqb_refl.
      unfold kmu; rewrite Hl; unfold Termination.dflag; rewrite Hd.
      destruct z; [lia|].
      assert (Hbn : bt γ n = None) by (unfold bt; rewrite Hn, Hd; reflexivity).
      rewrite Hbn; lia.
  Qed.

  (** The measure of [n] drops when it reloads because its selection changed. *)
  Lemma mu_drop_restart (γ : State) n fn acc w (l : Life) :
    KTInv γ -> fibers γ n = Some fn -> fresh γ fn = false ->
    (exists P, life fn = Loading Σ P acc w \/ life fn = Active Σ acc w) ->
    l = Unloading Σ acc w None ->
    kmu (set_life Σ γ n fn l) n (mkFiber Σ (fcomp fn) (fparent fn) (disposed fn) l) < kmu γ n fn.
  Proof.
    intros I Hn F (P & Hl) ->.
    pose proof (keffects_relife γ n fn (Unloading Σ acc w None) Hn) as EF.
    assert (Hn' : fibers (set_life Σ γ n fn (Unloading Σ acc w None)) n =
                  Some (mkFiber Σ (fcomp fn) (fparent fn) (disposed fn) (Unloading Σ acc w None)))
      by (rewrite fibers_set_life, Nat.eqb_refl; reflexivity).
    assert (W' : WF (set_life Σ γ n fn (Unloading Σ acc w None))).
    { apply (wf_relife kdec Σ prog' γ n fn _ (ki_wf _ (proj1 I)) Hn); destruct Hl as [Hl|Hl]; rewrite Hl; reflexivity. }
    destruct (stable_fiber γ _ n fn n fn _ I W' EF Hn Hn Hn' eq_refl eq_refl (le_n _)) as (_ & Hb & _).
    assert (Hw : Wt (set_life Σ γ n fn (Unloading Σ acc w None)) acc = Wt γ acc).
    { apply Wt_ext; intros x Hx; apply childflag_relife; [reflexivity|].
      apply (own_item_ne_k γ n fn x I Hn); destruct Hl as [Hl|Hl]; rewrite Hl; exact Hx. }
    unfold kmu at 1; cbn [life]; rewrite Hb.
    unfold kmu, ktis; rewrite F; cbn [andb].
    destruct Hl as [Hl|Hl]; rewrite Hl; unfold Termination.muU; rewrite Hw; unfold Termination.dflag; cbn [Calculus.disposed].
    - destruct (proj1 (proj2 I) n fn P acc w Hn Hl) as [Hlen _].
      pose proof (Wt_le Σ γ acc); cbn [Termination.Wt].
      destruct (bt γ n); destruct (disposed fn); unfold Bm; lia.
    - destruct (bt γ n); lia.
  Qed.

  (** ** The measure of a state *)
  Definition kcontrib (γ : State) (r m : nat) : nat :=
    match fibers γ m with
    | Some f => if Nat.eqb (frank f) r then kmu γ m f else 0
    | None => 0
    end.

  Definition KPhi (γ : State) (r : nat) : nat := sumf (kcontrib γ r) (names Σ γ).

  Lemma KPhi_ext (γ : State) r M :
    WF γ -> next γ <= M -> KPhi γ r = sumf (kcontrib γ r) (seq 0 M).
  Proof.
    intros W HM; unfold KPhi, names.
    replace M with (next γ + (M - next γ)) by lia.
    rewrite seq_app, sumf_app.
    rewrite (sumf_zero _ (seq (0 + next γ) _)); [lia|].
    intros x Hx; apply in_seq in Hx; unfold kcontrib.
    destruct (fibers γ x) eqn:E; [|reflexivity].
    apply (wf_names kdec Σ prog' γ W) in E; lia.
  Qed.

  Theorem phi_drop_gen (γ γ' : State) n fn :
    KTInv γ -> WF γ' -> KEffects γ γ' n fn -> fibers γ n = Some fn ->
    match fibers γ' n with Some fn' => kmu γ' n fn' | None => 0 end < kmu γ n fn ->
    lexR Rb (KPhi γ') (KPhi γ).
  Proof.
    intros I W' EF Hn Hd.
    pose proof EF as (E1 & E2 & E3 & E5 & _).
    set (r0 := frank fn).
    assert (P1 : forall r, r <= r0 -> forall m,
              kcontrib γ' r m <= kcontrib γ r m /\
              (m <> n \/ r < r0 -> kcontrib γ' r m = kcontrib γ r m)).
    { intros r Hr m; unfold kcontrib.
      destruct (Nat.eq_dec m n) as [->|Hmn].
      - rewrite Hn.
        destruct (fibers γ' n) as [fn'|] eqn:Hn'.
        + destruct (E3 fn' eq_refl) as [Hc _]; rewrite Hc.
          destruct (Nat.eqb_spec (frank fn) r) as [Er|Er].
          * split; [lia|]; intros [Cx|Cx]; [contradiction | subst r0; lia].
          * split; [lia | intros; reflexivity].
        + destruct (Nat.eqb_spec (frank fn) r) as [Er|Er].
          * split; [lia|]; intros [Cx|Cx]; [contradiction | subst r0; lia].
          * split; [lia | intros; reflexivity].
      - destruct (fibers γ m) as [fm|] eqn:Hm.
        + destruct (Compare_dec.le_lt_dec (frank fm) r0) as [Hle|Hgt].
          * destruct (mu_other_k γ γ' n fn m fm I W' EF Hn Hmn Hm Hle) as [Hm' Hmu].
            rewrite Hm', Hmu; split; [lia | auto].
          * destruct (E1 m fm Hmn Hm) as [Hm'|[Hm' _]]; rewrite Hm'; cbn [Calculus.comp];
              (destruct (Nat.eqb_spec (frank fm) r); [subst r0; lia | split; [lia | auto]]).
        + destruct (fibers γ' m) as [fm'|] eqn:Hm'; [|split; [lia | auto]].
          destruct (E2 m fm' Hm Hm') as [_ Hlt].
          destruct (Nat.eqb_spec (frank fm') r); [subst r0; lia | split; [lia | auto]]. }
    assert (P2 : kcontrib γ' r0 n < kcontrib γ r0 n).
    { unfold kcontrib; rewrite Hn; subst r0; rewrite Nat.eqb_refl.
      destruct (fibers γ' n) as [fn'|] eqn:Hn'; [|exact Hd].
      destruct (E3 fn' eq_refl) as [Hc _]; rewrite Hc, Nat.eqb_refl; exact Hd. }
    set (M := next γ + next γ').
    pose proof (ki_wf _ (proj1 I)) as W.
    exists r0; split; [apply Hbnd|]; split.
    - intros i Hi.
      rewrite (KPhi_ext γ' i M W') by lia; rewrite (KPhi_ext γ i M W) by lia.
      apply sumf_eq; intros m _; apply (proj2 (P1 i ltac:(lia) m)); right; exact Hi.
    - rewrite (KPhi_ext γ' r0 M W') by lia; rewrite (KPhi_ext γ r0 M W) by lia.
      apply (sumf_lt _ _ _ n); [intros m _; exact (proj1 (P1 r0 (le_n _) m)) | | exact P2].
      apply in_seq; pose proof (wf_names kdec Σ prog' γ W n fn Hn); lia.
  Qed.

  (** ** Choosing an Inactive fiber's selection leaves the measure *)
  Lemma kphi_recomp (γ : State) n f :
    fibers γ n = Some f -> life f = Inactive Σ None ->
    forall r, KPhi (recomp γ n f) r = KPhi γ r.
  Proof.
    intros Hn Hl r.
    set (x' := rcomp γ (fcomp f)).
    assert (Er : recomp γ n f = set_fiber Σ γ n (mkFiber Σ x' (fparent f) (disposed f) (life f)))
      by reflexivity.
    rewrite Er.
    set (γr := set_fiber Σ γ n (mkFiber Σ x' (fparent f) (disposed f) (life f))).
    assert (Hv : forall k, visible Σ γr k = visible Σ γ k)
      by (intros k; exact (visible_refiber γ n f x' (disposed f) k Hn)).
    assert (Hs : forall y, select γr y = select γ y)
      by (intros y; exact (select_refiber γ n f x' (disposed f) y Hn eq_refl eq_refl)).
    assert (Hr : forall ks, resolve Σ γr ks = resolve Σ γ ks)
      by (intros ks; apply resolve_ext; exact Hv).
    assert (Hcf : forall x, childflag γr x = childflag γ x).
    { intros x; unfold Termination.childflag, γr; rewrite fibers_refiber.
      destruct (Nat.eqb_spec x n) as [->|]; [rewrite Hn; reflexivity | reflexivity]. }
    assert (Hwt : forall l, Wt γr l = Wt γ l)
      by (intros l; apply Wt_ext; intros x _; apply Hcf).
    assert (Hch : forall c, choose γr c = choose γ c)
      by (intros c; apply choose_ext; intros y _; apply Hs).
    assert (Has : forall c, all_selected γr c = all_selected γ c)
      by (intros c; apply all_selected_ext; intros y _; apply Hs).
    assert (Hbt : forall m, m <> n -> bt γr m = bt γ m).
    { intros m Hmn; unfold bt, γr; rewrite fibers_refiber, (proj2 (Nat.eqb_neq m n) Hmn).
      destruct (fibers γ m) as [fm|]; [|reflexivity].
      destruct (disposed fm); [reflexivity|]; fold γr; rewrite Has.
      destruct (all_selected γ (base (fcomp fm))); [|reflexivity].
      unfold rcomp; rewrite Hch, Hr; reflexivity. }
    unfold KPhi; change (names Σ γr) with (names Σ γ).
    apply sumf_eq; intros m _; unfold kcontrib, γr; rewrite fibers_refiber.
    destruct (Nat.eqb_spec m n) as [->|Hmn].
    - rewrite Hn; cbn [Calculus.comp].
      change (base x') with (base (fcomp f)).
      destruct (Nat.eqb (frank f) r); [|reflexivity].
      fold γr.
      assert (Ebt : bt γr n = bt γ n).
      { unfold bt, γr; rewrite fibers_refiber, Nat.eqb_refl, Hn; cbn [Calculus.disposed Calculus.comp].
        fold γr; rewrite Has; unfold x', rcomp; cbn [base scope env tick]; rewrite Hch, Hr; reflexivity. }
      unfold kmu; cbn [life]; rewrite Hl, Ebt; reflexivity.
    - destruct (fibers γ m) as [fm|] eqn:Hm; [|reflexivity].
      destruct (Nat.eqb (frank fm) r); [|reflexivity].
      fold γr.
      assert (Etg : target γr m = target γ m).
      { unfold Calculus.target, γr; rewrite fibers_refiber, (proj2 (Nat.eqb_neq m n) Hmn), Hm.
        fold γr; rewrite Hr; reflexivity. }
      assert (Efr : fresh γr fm = fresh γ fm) by (apply fresh_ext; [reflexivity | intros y _; apply Hs]).
      unfold kmu, ktis, target_is, Termination.muU; rewrite (Hbt m Hmn), Etg, Efr.
      destruct (life fm); rewrite ?Hwt; reflexivity.
  Qed.

  Lemma klexR_ext R (v1 v2 v : nat -> nat) : (forall r, v2 r = v r) -> lexR R v1 v2 -> lexR R v1 v.
  Proof.
    intros E (r & Hr & Heq & Hlt); exists r; split; [exact Hr|]; split.
    - intros i Hi; rewrite <- E; apply Heq; exact Hi.
    - rewrite <- E; exact Hlt.
  Qed.

  (** ** Every extended lifecycle step decreases the measure *)
  Theorem kphi_drop (γ γ' : State) n ℓ :
    KTInv γ -> In ℓ (@lifecycle_labels C n) -> kstep γ ℓ = Some γ' -> lexR Rb (KPhi γ') (KPhi γ).
  Proof.
    intros I Hin H.
    pose proof (ki_wf _ (proj1 (ktinv_step γ γ' ℓ I H))) as W'.
    destruct (fibers γ n) as [fn|] eqn:Hn.
    2: { exfalso.
         assert (Hs : forall (ℓ0 : @Calculus.Label XC), In ℓ0 (@lifecycle_labels XC n) -> step γ ℓ0 = None)
           by (intros ℓ0 Hin0; exact (step_absent kdec Σ prog' γ n ℓ0 Hn Hin0)).
         cbn in Hin; destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
           cbn [Scoped.kstep klab] in H; rewrite ?Hn in H; try discriminate H;
           rewrite Hs in H by (cbn; tauto); discriminate H. }
    assert (Core : forall ℓ', In ℓ' (@lifecycle_labels XC n) -> step γ ℓ' = Some γ' ->
              ((ℓ' = LBegin n \/ ℓ' = LStep n) -> fresh γ fn = true) ->
              lexR Rb (KPhi γ') (KPhi γ)).
    { intros ℓ' Hin' St Fr.
      exact (phi_drop_gen γ γ' n fn I W' (keffects_core γ γ' n ℓ' fn I Hin' St Hn) Hn
               (mu_drop_core γ γ' n ℓ' fn I Hin' St Hn Fr)). }
    assert (Nb : forall ℓ' : @Calculus.Label XC, ℓ' <> LBegin n /\ ℓ' <> LStep n ->
              (ℓ' = LBegin n \/ ℓ' = LStep n) -> fresh γ fn = true)
      by (intros ℓ' [A B] [E|E]; contradiction).
    cbn in Hin; destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
    - (* X-Begin: choose the selection, then the core L-Begin *)
      cbn [Scoped.kstep] in H; rewrite Hn in H.
      destruct (life fn) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (fparent fn) as [q|] eqn:Hp.
      { destruct (fresh γ fn) eqn:F; [|discriminate].
        refine (Core _ _ H (fun _ => eq_refl)); cbn; tauto. }
      destruct (all_selected γ (base (fcomp fn))) eqn:A; [|discriminate].
      set (γr := recomp γ n fn) in H.
      set (fr := mkFiber Σ (rcomp γ (fcomp fn)) (fparent fn) (disposed fn) (life fn)).
      assert (Hnr : fibers γr n = Some fr) by (unfold γr, Scoped.recomp; rewrite fibers_refiber, Nat.eqb_refl; reflexivity).
      assert (Ir : KTInv γr) by (apply ktinv_recomp; auto).
      assert (Fr : fresh γr fr = true).
      { assert (Es : forall y, select γr y = select γ y)
          by (intros y; unfold γr; exact (select_refiber γ n fn (rcomp γ (fcomp fn)) (disposed fn) y Hn eq_refl eq_refl)).
        unfold Scoped.fresh, fr; cbn [Calculus.comp]; unfold rcomp; cbn [base sel].
        rewrite (all_selected_ext γ γr _ (fun y _ => Es y)), A, (choose_ext γ γr _ (fun y _ => Es y)); cbn [andb].
        destruct (list_eq_dec ns_eq_dec _ _) as [_|Q]; [reflexivity | contradiction Q; reflexivity]. }
      assert (Hin0 : In (@LBegin XC n) (@lifecycle_labels XC n)) by (cbn; tauto).
      pose proof (phi_drop_gen γr γ' n fr Ir W' (keffects_core γr γ' n _ fr Ir Hin0 H Hnr) Hnr
                    (mu_drop_core γr γ' n _ fr Ir Hin0 H Hnr (fun _ => Fr))) as D.
      apply (klexR_ext Rb _ (KPhi γr)); [|exact D].
      intros r; unfold γr; exact (kphi_recomp γ n fn Hn Hl r).
    - (* X-Step *)
      cbn [Scoped.kstep] in H; rewrite Hn in H.
      destruct (fresh γ fn) eqn:F; [|discriminate].
      refine (Core _ _ H (fun _ => eq_refl)); cbn; tauto.
    - (* X-Divert *)
      cbn [Scoped.kstep] in H; rewrite Hn in H.
      destruct (fresh γ fn) eqn:F.
      { refine (Core _ _ H (Nb _ _)); first [split; discriminate | cbn; tauto]. }
      destruct (life fn) as [|P acc w| |] eqn:Hl; try discriminate; injection H as <-.
      apply (phi_drop_gen γ _ n fn I W' (keffects_relife γ n fn _ Hn) Hn).
      rewrite fibers_set_life, Nat.eqb_refl.
      exact (mu_drop_restart γ n fn acc w _ I Hn F (ex_intro _ P (or_introl Hl)) eq_refl).
    - (* X-Leave *)
      cbn [Scoped.kstep] in H; rewrite Hn in H.
      destruct (fresh γ fn) eqn:F.
      { refine (Core _ _ H (Nb _ _)); first [split; discriminate | cbn; tauto]. }
      destruct (life fn) as [| |acc w|] eqn:Hl; try discriminate; injection H as <-.
      apply (phi_drop_gen γ _ n fn I W' (keffects_relife γ n fn _ Hn) Hn).
      rewrite fibers_set_life, Nat.eqb_refl.
      exact (mu_drop_restart γ n fn acc w _ I Hn F (ex_intro _ PDone (or_intror Hl)) eq_refl).
    - cbn [Scoped.kstep klab] in H; refine (Core _ _ H (Nb _ _)); first [split; discriminate | cbn; tauto].
    - cbn [Scoped.kstep klab] in H; refine (Core _ _ H (Nb _ _)); first [split; discriminate | cbn; tauto].
    - cbn [Scoped.kstep klab] in H; refine (Core _ _ H (Nb _ _)); first [split; discriminate | cbn; tauto].
    - cbn [Scoped.kstep klab] in H; refine (Core _ _ H (Nb _ _)); first [split; discriminate | cbn; tauto].
  Qed.

  (** ** Termination *)
  Definition KLStepRel (γ' γ : State) : Prop :=
    KTInv γ /\ exists n ℓ, In ℓ (@lifecycle_labels C n) /\ kstep γ ℓ = Some γ'.

  (** Extended lifecycle steps alone always terminate. *)
  Theorem ktermination (γ : State) : KTInv γ -> Acc KLStepRel γ.
  Proof.
    assert (G : forall v, Acc (lexR Rb) v ->
                forall γ, KTInv γ -> (forall r, KPhi γ r = v r) -> Acc KLStepRel γ).
    { intros v Hacc; induction Hacc as [v _ IH]; intros γ0 I E.
      constructor; intros γ1 [I0 (n & ℓ & Hin & H)].
      pose proof (kphi_drop γ0 γ1 n ℓ I0 Hin H) as D.
      apply (IH (KPhi γ1)); [| exact (ktinv_step γ0 γ1 ℓ I0 H) | intros; reflexivity].
      exact (klexR_ext Rb _ _ _ E D). }
    intros I; exact (G (KPhi γ) (lexR_wf Rb _) γ I (fun _ => eq_refl)).
  Qed.

  (** There is no infinite sequence of extended lifecycle steps. *)
  Corollary kno_infinite_run (γ : State) :
    KTInv γ ->
    ~ exists g : nat -> State, g 0 = γ /\
        forall i, exists n ℓ, In ℓ (@lifecycle_labels C n) /\ kstep (g i) ℓ = Some (g (S i)).
  Proof.
    intros I (g & G0 & Gs).
    assert (Inv : forall i, KTInv (g i)).
    { induction i as [|i IH]; [rewrite G0; exact I|].
      destruct (Gs i) as (n & ℓ & _ & H); exact (ktinv_step _ _ ℓ IH H). }
    assert (A : forall x, Acc KLStepRel x -> forall i, g i = x -> False).
    { intros x Hx; induction Hx as [x _ IHx]; intros i Ei.
      refine (IHx (g (S i)) _ (S i) eq_refl).
      rewrite <- Ei; split; [exact (Inv i) | exact (Gs i)]. }
    exact (A γ (ktermination γ I) 0 G0).
  Qed.

  (** From the initial state, after any extended execution (orchestration,
      reactions and lifecycle steps in any order). *)
  Corollary ktermination_reachable (γ : State) :
    KReachable N_eq_dec Σ xprog γ -> Acc KLStepRel γ.
  Proof.
    intros [ls H]; apply ktermination.
    assert (G : forall γ0, KTInv γ0 -> krun γ0 ls = Some γ -> KTInv γ).
    { clear H; induction ls as [|ℓ ls IH]; cbn; intros γ0 I0 H0.
      - injection H0 as <-; exact I0.
      - destruct (kstep γ0 ℓ) as [γ1|] eqn:Hs; [|discriminate].
        exact (IH γ1 (ktinv_step γ0 γ1 ℓ I0 Hs) H0). }
    exact (G _ ktinv_init H).
  Qed.
End ScopedTerm.
