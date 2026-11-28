(** * Hygienic keys: confluence with spawn

    Counterpart of [SpawnConf.spawn_confluence]: two extended lifecycle
    executions from a common state that end quiet with no fiber failed
    agree up to renaming ([kspawn_confluence]): canonical names name every
    fiber once, the same names occur with the same components (scope and
    selection included) and activity, corresponding fibers own each key,
    each key's service states are ≃, and every exported name has the same
    resolution and the same ties.

    Obligation: a parent declares every exported name its children depend
    on ([kSub]). A child inherits its parent's selection when spawned and
    never re-chooses it ([Scoped.inherit]), so its component stays the one
    its parent spawned, which the core's trace invariant ([Episode.Corr])
    checks; at a quiet state its selection is current because its parent's
    is ([quiet_child_fresh]).

    What the proof adds to the core's:
    - Final states are normalised ([norm]): every Inactive root takes the
      selection choosing would give, so every fiber's selection is current
      ([Fresh]).
    - The core's rank induction is redone with one change: two
      corresponding roots are known to agree on everything but the
      selection; that the selections agree follows from the correspondence
      at lower ranks ([select_corr]): the candidates for an exported name
      have lower rank, corresponding candidates have equal scopes and
      priorities and the same activity, so the two candidate lists are
      permutations of each other, and resolution does not depend on order.
      Exporters may be children, whose names differ between the runs.
    - Unique scopes ([ScopedSafety.SI]) identify the owner of a key at a
      fiber's scope with that fiber.

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia RelationClasses Permutation Sorted Wf_nat.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering
  Recovery Progress Termination Confluence StateInv Episode StateConf SpawnConf Dynamic.
From CordisKeys Require Import Scoped ScopedSafety ScopedTerm ScopedProgress ScopedConf.
Import ListNotations.

Section ScopedSpawn.
  Context {N : Type} (N_eq_dec : forall x y : N, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (xprog : C -> @XComponent N Σ C).

  Local Notation XC := (@XC N C).
  Local Notation Key := (@Key N).
  Local Notation State := (@State Key Σ XC).
  Local Notation Fiber := (@Fiber Key Σ XC).
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
  Local Notation kdec := (key_eq_dec N_eq_dec).
  Local Notation prog' := (prog' N_eq_dec Σ xprog).
  Local Notation lift := (lift N_eq_dec Σ xprog).
  Local Notation handlers := (handlers N_eq_dec Σ xprog).
  Local Notation step := (step kdec Σ prog').
  Local Notation kstep := (kstep N_eq_dec Σ xprog).
  Local Notation recomp := (recomp N_eq_dec Σ xprog).
  Local Notation rcomp := (rcomp N_eq_dec Σ xprog).
  Local Notation select := (select N_eq_dec Σ xprog).
  Local Notation candidate := (candidate N_eq_dec Σ xprog).
  Local Notation candidates := (candidates N_eq_dec Σ xprog).
  Local Notation choose := (choose N_eq_dec Σ xprog).
  Local Notation all_selected := (all_selected N_eq_dec Σ xprog).
  Local Notation globals := (globals Σ xprog).
  Local Notation fresh := (fresh N_eq_dec Σ xprog).
  Local Notation bt := (bt N_eq_dec Σ xprog).
  Local Notation SI := (SI N_eq_dec Σ xprog).
  Local Notation WF := (WF kdec Σ prog').
  Local Notation kquiet := (kquiet N_eq_dec Σ xprog).
  Local Notation xprovs c := (xprovs Σ xprog c).
  Local Notation dnames c := (map dname (xdeps Σ (xprog c))).

  (** ** Hypotheses *)
  Variable Kb : nat.
  Hypothesis kHK : forall c, Termination.Bounded Σ Kb (xbody Σ (xprog c)).
  Variable xrank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', KAbove Σ xprog c c' -> xrank c < xrank c'.
  Hypothesis Hbnd : forall c, xrank c <= Rb.
  Hypothesis kTotal : forall c y, In y (xprovs c) -> AllDoneProv Σ y (xbody Σ (xprog c)).
  (** A parent declares every exported name its children depend on. *)
  Hypothesis kSub : forall c c', KSpawns Σ xprog c c' -> forall y, In y (globals c') -> In y (globals c).

  Hypothesis Hwb : forall a t, WellBehaved (Σ := Σ) a t.
  Hypothesis HUI : forall (a : Op Σ) (t : nat) (s1 s2 s1' s2' : S) (g1 g2 : S -> S) (o1 o2 : Out Σ),
    run a t s1 = Some (s1', g1, o1) -> run a t s2 = Some (s2', g2, o2) -> fun_eq (Σ := Σ) g1 g2.
  Hypothesis HTI : forall (a : Op Σ) (t t' : nat) (s : S),
    match run a t s, run a t' s with
    | None, None => True
    | Some (s1, _, o1), Some (s2, _, o2) => @st_eq Σ s1 s2 /\ o1 = o2
    | _, _ => False
    end.
  Hypothesis HRI : forall (k : Key) (a b : Op Σ) (ta tb : nat) (g : S -> S),
    CoPair Σ prog' k a b -> ta <> tb -> yields (Σ := Σ) a ta g ->
    forall x, After (CoPair Σ prog' k a) a ta x -> shifted_ok (Σ := Σ) g (run b tb x) (run b tb (g x)).
  Hypothesis HCom : forall (k : Key) (a b : Op Σ) (ta tb : nat), CoPair Σ prog' k a b -> ta <> tb ->
    Commute (Σ := Σ) a ta b tb.

  Local Notation rank' := (fun x : XC => xrank (base x)).

  (** ** The core hypotheses for [prog'] *)
  Lemma Hrank2 : forall x y, Above Σ prog' x y -> rank' x < rank' y.
  Proof.
    intros x y [(k & Hp & Hd)|[Hs|Hr]]; apply Hrank.
    - left; exists (snd k); split.
      + cbn [Scoped.prog' provs] in Hp; apply in_map_iff in Hp as (y0 & <- & Hy0); exact Hy0.
      + exact (deps_keyof N_eq_dec Σ xprog _ k Hd).
    - right; left; cbn [Scoped.prog' body] in Hs; exact (spawnin_lift N_eq_dec Σ xprog _ _ _ _ Hs).
    - right; right; cbn [Scoped.prog' reacts] in Hr; exact (handlers_in N_eq_dec Σ xprog _ _ _ _ Hr).
  Qed.

  Local Notation HK' := (HK' N_eq_dec Σ xprog Kb kHK).
  Local Notation Total' := (Total' N_eq_dec Σ xprog kTotal).
  Local Notation PInv := (PInv kdec Σ prog' Kb).
  Local Notation SInv := (SInv kdec Σ prog' Kb).
  Local Notation TInv := (TInv kdec Σ prog' Kb).
  Local Notation pinv_step :=
    (pinv_step kdec Σ prog' Kb HK' rank' Hrank2 Total' Hwb HUI HTI HRI HCom).
  Local Notation FinalS := (FinalS kdec Σ prog' Kb).
  Local Notation Final := (Final kdec Σ prog' Kb).

  Lemma pinv_tinv (γ : State) : PInv γ -> TInv γ.
  Proof. intros P; exact (c0_t _ _ _ _ _ (s_c _ _ _ _ _ (p_s _ _ _ _ _ P))). Qed.

  Lemma xc_eta (x : XC) : x = mkXC (base x) (scope x) (env x) (sel x) (tick x).
  Proof. destruct x; reflexivity. Qed.

  Lemma fiber_eta (f : Fiber) : f = @mkFiber Key Σ XC (fcomp f) (fparent f) (disposed f) (life f).
  Proof. destruct f; reflexivity. Qed.

  (** ** Changing the components of Inactive fibers *)
  Definition RF (γ : State) (F : nat -> option Fiber) : Prop :=
    (forall m fm, F m = Some fm ->
       exists fm0, fibers γ m = Some fm0 /\ life fm = life fm0 /\ fparent fm = fparent fm0 /\
                   disposed fm = disposed fm0 /\ base (fcomp fm) = base (fcomp fm0) /\
                   scope (fcomp fm) = scope (fcomp fm0) /\ env (fcomp fm) = env (fcomp fm0) /\
                   tick (fcomp fm) = tick (fcomp fm0) /\
                   (is_installed (life fm0) = true -> fm = fm0)) /\
    (forall m fm0, fibers γ m = Some fm0 -> exists fm, F m = Some fm).

  Definition RF2 (γ : State) (F : nat -> option Fiber) : Prop :=
    RF γ F /\
    (forall m fm fm0, F m = Some fm -> fibers γ m = Some fm0 -> fparent fm0 <> None -> fm = fm0).

  Lemma rf_installed (γ : State) F m fm0 :
    RF γ F -> fibers γ m = Some fm0 -> is_installed (life fm0) = true -> F m = Some fm0.
  Proof.
    intros [R1 R2] H0 Hi; destruct (R2 m fm0 H0) as [fm Hm].
    destruct (R1 m fm Hm) as (fm0' & H0' & _ & _ & _ & _ & _ & _ & _ & E).
    rewrite H0 in H0'; injection H0' as <-; rewrite Hm, (E Hi); reflexivity.
  Qed.

  Lemma fprovs_bs (f f' : Fiber) :
    base (fcomp f) = base (fcomp f') -> scope (fcomp f) = scope (fcomp f') ->
    fprovs Σ prog' f = fprovs Σ prog' f'.
  Proof. intros Eb Es; unfold fprovs; cbn [Scoped.prog' provs]; rewrite Eb, Es; reflexivity. Qed.

  Lemma rf_wf (γ : State) F : WF γ -> RF γ F -> WF (with_fibers Σ γ F).
  Proof.
    intros W R; pose proof R as [R1 R2].
    destruct W as [Wn Wp Ws Wpar Wd Wv Wk Wb Wu Wuu]; split; cbn [Calculus.next Calculus.binds Calculus.fibers with_fibers] in *.
    - intros m fm H; destruct (R1 m fm H) as (fm0 & H0 & _); eauto.
    - exact Wp.
    - intros m fm m' H I; destruct (R1 m fm H) as (fm0 & H0 & El & _); rewrite El in I; eauto.
    - intros m fm q H Hq; destruct (R1 m fm H) as (fm0 & H0 & _ & Ep & _); rewrite Ep in Hq.
      destruct (Wpar m fm0 q H0 Hq) as (fq & Hq0 & Iq & Uq).
      exists fq; split; [exact (rf_installed γ F q fq R Hq0 Iq) | auto].
    - intros m m' fm fm' Hne H H'.
      destruct (R1 m fm H) as (fm0 & H0 & _ & _ & _ & Eb & Es & _).
      destruct (R1 m' fm' H') as (fm0' & H0' & _ & _ & _ & Eb' & Es' & _).
      rewrite (fprovs_bs _ _ Eb Es), (fprovs_bs _ _ Eb' Es'); eauto.
    - intros m fm k p H I; destruct (R1 m fm H) as (fm0 & H0 & El & _); rewrite El in I; eauto.
    - intros m fm H I; destruct (R1 m fm H) as (fm0 & H0 & El & _ & _ & _ & _ & _ & _ & Eq).
      rewrite El in I; rewrite (Eq I); eauto.
    - intros k b Hb; destruct (Wb k b Hb) as (fo & Ho & Io & Ko & Uo).
      exists fo; repeat split; auto; exact (rf_installed γ F _ fo R Ho Io).
    - intros m fm k p H I; destruct (R1 m fm H) as (fm0 & H0 & El & _); rewrite El in I; eauto.
    - intros m fm H; destruct (R1 m fm H) as (fm0 & H0 & El & _).
      pose proof (Wuu m fm0 H0) as U; rewrite El; exact U.
  Qed.

  Lemma rf_item (γ : State) F k p t :
    RF γ F -> (Item Σ (with_fibers Σ γ F) k p t <-> Item Σ γ k p t).
  Proof.
    intros [R1 R2]; unfold Item, uacc; cbn [Calculus.fibers with_fibers]; split.
    - intros (m & fm & g & H & I); destruct (R1 m fm H) as (fm0 & H0 & El & _).
      rewrite El in I; eauto.
    - intros (m & fm0 & g & H0 & I); destruct (R2 m fm0 H0) as [fm H].
      destruct (R1 m fm H) as (fm0' & H0' & El & _); rewrite H0 in H0'; injection H0' as <-.
      exists m, fm, g; rewrite El; auto.
  Qed.

  Lemma acc_installed (l : @Life Key Σ XC) u : In u (acc_of l) -> is_installed l = true.
  Proof. destruct l; cbn; [intros []|reflexivity..]. Qed.

  Lemma rf2_tinv (γ : State) F : TInv γ -> RF2 γ F -> TInv (with_fibers Σ γ F).
  Proof.
    intros [W [PF PT] [U Sp] LB SO] [R E2]; pose proof R as [R1 R2].
    assert (Hpar : forall x fx m, F x = Some fx -> In (USpawn Σ m) (acc_of (life fx)) ->
              fibers γ x = Some fx /\
              forall fm, F m = Some fm -> fibers γ m = Some fm /\ fparent fm = Some x).
    { intros x fx m Hx Hu.
      destruct (R1 x fx Hx) as (fx0 & Hx0 & El & _ & _ & _ & _ & _ & _ & Ei).
      assert (Ins : is_installed (life fx0) = true) by (rewrite El in Hu; exact (acc_installed _ _ Hu)).
      pose proof (Ei Ins) as Efx; subst fx; split; [exact Hx0|].
      intros fm Hm; destruct (R1 m fm Hm) as (fm0 & Hm0 & _ & Ep & _).
      pose proof (SO x fx0 m fm0 Hx0 Hu Hm0) as Hp0.
      rewrite (E2 m fm fm0 Hm Hm0 ltac:(rewrite Hp0; discriminate)); auto. }
    split.
    - exact (rf_wf γ F W R).
    - split.
      + intros m fm H; destruct (R1 m fm H) as (fm0 & H0 & El & _ & _ & _ & _ & _ & _ & E).
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
    intros [[[T PI] SG SI0] EP] R2; pose proof R2 as [R E2]; pose proof R as [R1 R0].
    pose proof (rf2_tinv γ F T R2) as T'.
    pose proof T as [_ _ _ _ SO].
    split; [split; [split|..]|].
    - exact T'.
    - intros m fm H; destruct (R1 m fm H) as (fm0 & H0 & El & _ & _ & _ & _ & _ & _ & E).
      destruct (is_installed (life fm0)) eqn:Hi.
      + rewrite (E eq_refl); exact (PI m fm0 H0).
      + unfold PIF; rewrite El; destruct (life fm0); try discriminate; exact Logic.I.
    - intros m fm H; destruct (R1 m fm H) as (fm0 & H0 & El & _ & _ & _ & _ & _ & _ & E).
      destruct (is_installed (life fm0)) eqn:Hi.
      + rewrite (E eq_refl); exact (SG m fm0 H0).
      + unfold GF, uacc; rewrite El; destruct (life fm0); try discriminate; cbn.
        split; [constructor | intros k p t g []].
    - intros k b Hb; destruct (SI0 k b Hb) as (s0 & L & s & Hi & [Hs HL] & Rp & E).
      exists s0, L, s; split; [exact Hi|]; split; [split; [exact Hs|]|split; [exact Rp | exact E]].
      intros a t; rewrite (HL a t); cbn [Calculus.oplog with_fibers].
      rewrite (rf_item γ F k (pid Σ b) t R); reflexivity.
    - intros m fm H; destruct (R1 m fm H) as (fm0 & H0 & El & _ & _ & _ & _ & _ & _ & E).
      destruct (is_installed (life fm0)) eqn:Hi.
      + rewrite (E eq_refl); pose proof (EP m fm0 H0) as Ep.
        assert (Hcorr : forall c w acc evs, acc = acc_of (life fm0) ->
                  Corr kdec Σ prog' γ c w acc evs ->
                  Corr kdec Σ prog' (with_fibers Σ γ F) c w acc evs).
        { intros c w acc evs Ea Co; apply (corr_mono kdec Σ prog' γ _ c w acc evs Co);
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

  Lemma si_rf (γ : State) F : WF γ -> SI γ -> RF2 γ F -> SI (with_fibers Σ γ F).
  Proof.
    intros W S0 [R E2]; pose proof R as [R1 R2].
    assert (Fwd : forall m fm0, fibers γ m = Some fm0 ->
              exists fm, F m = Some fm /\ scope (fcomp fm) = scope (fcomp fm0)).
    { intros m fm0 H0; destruct (R2 m fm0 H0) as [fm H].
      destruct (R1 m fm H) as (fm0' & H0' & _ & _ & _ & _ & Es & _).
      rewrite H0 in H0'; injection H0' as <-; eauto. }
    split; cbn [Calculus.next Calculus.fibers with_fibers].
    - intros m m' fm fm' Hm Hm' E.
      destruct (R1 m fm Hm) as (fm0 & H0 & _ & _ & _ & _ & Es & _).
      destruct (R1 m' fm' Hm') as (fm0' & H0' & _ & _ & _ & _ & Es' & _).
      apply (si_uniq _ _ _ _ S0 m m' fm0 fm0' H0 H0'); congruence.
    - intros m fm Hm; destruct (R1 m fm Hm) as (fm0 & H0 & _ & _ & _ & _ & Es & _); rewrite Es.
      exact (si_bound _ _ _ _ S0 m fm0 H0).
    - intros m fm j s Hm Hs; destruct (R1 m fm Hm) as (fm0 & H0 & _ & Ep & _ & _ & Es & _).
      rewrite Es in Hs; destruct (si_parent _ _ _ _ S0 m fm0 j s H0 Hs) as (q & fq & Pq & Hq & Eq).
      destruct (Fwd q fq Hq) as (fq' & Hq' & Eq').
      exists q, fq'; split; [congruence|]; split; [exact Hq'|]; congruence.
    - intros m fm Hm P acc w L.
      destruct (R1 m fm Hm) as (fm0 & H0 & El & _ & _ & _ & _ & _ & _ & Ei).
      assert (Efm : fm = fm0) by (apply Ei; rewrite <- El, L; reflexivity); subst fm.
      destruct (si_load _ _ _ _ S0 m fm0 H0 P acc w L) as (j & Q & EP & K).
      exists j, Q; split; [exact EP|].
      intros m' fm' j' Hm' Hs; destruct (R1 m' fm' Hm') as (fm1 & H1 & _ & _ & _ & _ & Es1 & _).
      rewrite Es1 in Hs; exact (K m' fm1 j' H1 Hs).
    - intros m fm Hm; destruct (R1 m fm Hm) as (fm0 & H0 & _ & _ & _ & _ & Es & _); rewrite Es.
      exact (si_ne _ _ _ _ S0 m fm0 H0).
    - intros m fm q fq Hm Hp Hq.
      destruct (R1 m fm Hm) as (fm0 & H0 & _ & Ep & _).
      assert (Hp0 : fparent fm0 = Some q) by (rewrite <- Ep; exact Hp).
      rewrite (E2 m fm fm0 Hm H0 ltac:(rewrite Hp0; discriminate)).
      destruct (wf_parent _ _ _ _ W m fm0 q H0 Hp0) as (fq0 & Hq0 & Iq & _).
      cbn [Calculus.fibers with_fibers] in Hq.
      rewrite (rf_installed γ F q fq0 R Hq0 Iq) in Hq; injection Hq as <-.
      exact (si_child _ _ _ _ S0 m fm0 q fq0 H0 Hp0 Hq0).
  Qed.

  Lemma rf2_recomp (γ : State) n f :
    fibers γ n = Some f -> is_installed (life f) = false -> fparent f = None ->
    RF2 γ (Calculus.fibers Σ (recomp γ n f)).
  Proof.
    intros Hn Hi Hpn; split; [split|].
    - intros m fm H; unfold Scoped.recomp in H; rewrite fibers_refiber in H.
      destruct (Nat.eqb_spec m n) as [->|]; [injection H as <-|].
      + exists f; repeat split; try reflexivity; [exact Hn | intros E; congruence].
      + exists fm; repeat split; auto.
    - intros m fm0 H0; unfold Scoped.recomp; rewrite fibers_refiber; destruct (Nat.eqb_spec m n); eauto.
    - intros m fm fm0 H H0 Hp; unfold Scoped.recomp in H; rewrite fibers_refiber in H.
      destruct (Nat.eqb_spec m n) as [->|]; [|congruence].
      rewrite Hn in H0; injection H0 as <-; contradiction.
  Qed.

  Lemma recomp_with (γ : State) n f : recomp γ n f = with_fibers Σ γ (Calculus.fibers Σ (recomp γ n f)).
  Proof. reflexivity. Qed.

  (** ** Roots keep their components but for the selection *)
  Definition KRootKeep (γ γ' : State) : Prop :=
    (forall m f', fibers γ' m = Some f' -> fparent f' = None ->
       exists f, fibers γ m = Some f /\ fparent f = None /\ base (fcomp f) = base (fcomp f') /\
                 scope (fcomp f) = scope (fcomp f') /\ env (fcomp f) = env (fcomp f') /\
                 tick (fcomp f) = tick (fcomp f') /\ disposed f = disposed f') /\
    (forall m f, fibers γ m = Some f -> fparent f = None -> disposed f = false ->
       exists f', fibers γ' m = Some f' /\ fparent f' = None /\ disposed f' = false).

  Lemma krk_refl (γ : State) : KRootKeep γ γ.
  Proof. split; intros m f H P; [exists f; auto 10 | intros D; exists f; auto]. Qed.

  Lemma krk_trans (γ1 γ2 γ3 : State) : KRootKeep γ1 γ2 -> KRootKeep γ2 γ3 -> KRootKeep γ1 γ3.
  Proof.
    intros [A1 B1] [A2 B2]; split.
    - intros m f3 H3 P3; destruct (A2 m f3 H3 P3) as (f2 & H2 & P2 & C2 & S2 & E2 & T2 & D2).
      destruct (A1 m f2 H2 P2) as (f1 & H1 & P1 & C1 & S1 & E1 & T1 & D1); exists f1; repeat split; congruence.
    - intros m f1 H1 P1 D1; destruct (B1 m f1 H1 P1 D1) as (f2 & H2 & P2 & D2); exact (B2 m f2 H2 P2 D2).
  Qed.

  Lemma krk_of (γ γ' : State) : RootKeep Σ γ γ' -> KRootKeep γ γ'.
  Proof.
    intros [A B]; split; [|exact B].
    intros m f' H P; destruct (A m f' H P) as (f & Hf & Pf & Cf & Df); exists f; rewrite Cf; auto 10.
  Qed.

  Lemma krk_rf (γ : State) F : RF γ F -> KRootKeep γ (with_fibers Σ γ F).
  Proof.
    intros [R1 R2]; split; cbn [Calculus.fibers with_fibers].
    - intros m f' H P; destruct (R1 m f' H) as (f & Hf & _ & Ep & Ed & Eb & Es & Ee & Et & _).
      exists f; repeat split; congruence.
    - intros m f Hf P D; destruct (R2 m f Hf) as [f' H].
      destruct (R1 m f' H) as (f0 & H0 & _ & Ep & Ed & _); rewrite Hf in H0; injection H0 as <-.
      exists f'; repeat split; congruence.
  Qed.

  Lemma krk_restart (γ γ' : State) n : step γ (ORestart n) = Some γ' -> KRootKeep γ γ'.
  Proof.
    intros H; destruct (restart_shape kdec Σ prog' γ γ' n H) as (f & acc & w & Hn & _ & _ & ->).
    split.
    - intros m fm Hm P; cbn [set_life set_fiber with_fibers Calculus.fibers] in Hm; unfold fupd in Hm.
      destruct (Nat.eqb_spec m n) as [->|]; [injection Hm as <-; exists f; auto 10|exists fm; auto 10].
    - intros m f0 H0 P D; cbn [set_life set_fiber with_fibers Calculus.fibers]; unfold fupd.
      destruct (Nat.eqb_spec m n) as [->|]; [rewrite Hn in H0; injection H0 as <-; cbn; eauto|eauto].
  Qed.

  (** ** Extended runs keep [PInv], [SLInv], [SI] and the roots *)
  Lemma kstep_inv (γ γ' : State) n ℓ :
    PInv γ -> SLInv Σ γ -> SI γ -> In ℓ (@lifecycle_labels C n) -> kstep γ ℓ = Some γ' ->
    PInv γ' /\ SLInv Σ γ' /\ SI γ' /\ KRootKeep γ γ'.
  Proof.
    intros P SL S0 Hin H.
    pose proof (t_wf _ _ _ _ _ (pinv_tinv γ P)) as W.
    pose proof (si_kstep N_eq_dec Σ xprog γ γ' ℓ W S0 H) as S'.
    destruct (kstep_core N_eq_dec Σ xprog γ γ' ℓ H)
      as [St|[(m & f & _ & Hm & Hl & _ & Hpm & St)|[(m & St)|(m & i & f & E & _)]]].
    - assert (Hlc : is_lifecycle (klab Σ xprog γ ℓ)).
      { exists n; cbn in Hin |- *.
        destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn; tauto. }
      split; [exact (pinv_step γ γ' _ (lifecycle_not_react _ Hlc) P St)|].
      split; [exact (sl_step kdec Σ prog' Kb γ γ' _ P SL Hlc St)|].
      split; [exact S'|].
      exact (krk_of _ _ (rk_step kdec Σ prog' Kb γ γ' _ P Hlc St)).
    - assert (Hlc : is_lifecycle (@LBegin XC m)) by (exists m; cbn; auto).
      assert (Hi : is_installed (life f) = false) by (rewrite Hl; reflexivity).
      pose proof (rf2_recomp γ m f Hm Hi Hpm) as R2.
      pose proof (rf2_pinv γ _ P R2) as Pr; pose proof (rf2_sl γ _ SL R2) as SLr.
      pose proof (krk_rf γ _ (proj1 R2)) as Kr.
      rewrite <- recomp_with in Pr, SLr, Kr.
      split; [exact (pinv_step _ γ' _ (lifecycle_not_react _ Hlc) Pr St)|].
      split; [exact (sl_step kdec Σ prog' Kb _ γ' _ Pr SLr Hlc St)|].
      split; [exact S'|].
      exact (krk_trans _ _ _ Kr (krk_of _ _ (rk_step kdec Σ prog' Kb _ γ' _ Pr Hlc St))).
    - assert (NR : forall a b, @ORestart XC m <> OReact a b) by (intros a b E; discriminate E).
      split; [exact (pinv_step γ γ' _ NR P St)|].
      split; [exact (sl_restart kdec Σ prog' γ γ' m SL St)|].
      split; [exact S'|].
      exact (krk_restart γ γ' m St).
    - subst ℓ; exfalso; cbn in Hin; intuition discriminate.
  Qed.

  Local Notation KLRun := (KLRun N_eq_dec Σ xprog).

  Lemma klrun_inv (γ0 γ : State) :
    PInv γ0 -> SLInv Σ γ0 -> SI γ0 -> KLRun γ0 γ ->
    PInv γ /\ SLInv Σ γ /\ SI γ /\ KRootKeep γ0 γ.
  Proof.
    intros P0 S0 I0 R; induction R as [γ|γ n ℓ γ1 γ2 Hin Hs R IH].
    - split; [exact P0 | split; [exact S0 | split; [exact I0 | apply krk_refl]]].
    - destruct (kstep_inv γ γ1 n ℓ P0 S0 I0 Hin Hs) as (P1 & S1 & I1 & K1).
      destruct (IH P1 S1 I1) as (P2 & S2 & I2 & K2).
      split; [exact P2 | split; [exact S2 | split; [exact I2 | exact (krk_trans _ _ _ K1 K2)]]].
  Qed.

  (** ** Final states, normalised *)
  Definition nfib (γ : State) (f : Fiber) : Fiber :=
    match fparent f with
    | Some _ => f
    | None => if is_installed (life f) then f
              else mkFiber Σ (rcomp γ (fcomp f)) (fparent f) (disposed f) (life f)
    end.

  Definition norm (γ : State) : State :=
    with_fibers Σ γ (fun m => option_map (nfib γ) (fibers γ m)).

  Lemma rf_norm (γ : State) : RF γ (fun m => option_map (nfib γ) (fibers γ m)).
  Proof.
    split.
    - intros m fm H; destruct (fibers γ m) as [fm0|] eqn:H0; [|discriminate].
      cbn in H; injection H as <-; exists fm0; unfold nfib.
      destruct (fparent fm0) as [q|] eqn:Hp; [repeat split; auto|].
      destruct (is_installed (life fm0)) eqn:Hi.
      + repeat split; auto.
      + repeat split; try reflexivity; intros E; congruence.
    - intros m fm0 H0; rewrite H0; eexists; reflexivity.
  Qed.

  Lemma rf2_norm (γ : State) : RF2 γ (fun m => option_map (nfib γ) (fibers γ m)).
  Proof.
    split; [exact (rf_norm γ)|].
    intros m fm fm0 H H0 Hp; rewrite H0 in H; cbn in H; injection H as <-.
    unfold nfib; destruct (fparent fm0) as [q|]; [reflexivity | contradiction].
  Qed.

  Lemma visible_rf (γ : State) F k : RF γ F -> visible Σ (with_fibers Σ γ F) k = visible Σ γ k.
  Proof.
    intros [R1 R2]; unfold visible; cbn [Calculus.binds Calculus.fibers with_fibers].
    destruct (binds γ k) as [b|]; [|reflexivity].
    destruct (F (owner b)) as [fo|] eqn:Ho.
    - destruct (R1 _ fo Ho) as (fo0 & H0 & El & _); rewrite H0, El; reflexivity.
    - destruct (fibers γ (owner b)) as [fo0|] eqn:H0; [|reflexivity].
      destruct (R2 _ fo0 H0) as [fo Hfo]; congruence.
  Qed.

  Lemma candidates_rf (γ : State) F y : RF γ F -> candidates (with_fibers Σ γ F) y = candidates γ y.
  Proof.
    intros R; pose proof R as [R1 R2]; unfold Scoped.candidates.
    change (names Σ (with_fibers Σ γ F)) with (names Σ γ).
    apply omap_ext_in; intros m _; unfold Scoped.candidate; cbn [Calculus.fibers with_fibers].
    destruct (F m) as [fm|] eqn:HF.
    - destruct (R1 m fm HF) as (fm0 & H0 & _ & _ & _ & Eb & Es & _); rewrite H0, Eb, Es.
      rewrite (visible_rf γ F _ R); reflexivity.
    - destruct (fibers γ m) as [fm0|] eqn:H0; [|reflexivity].
      destruct (R2 m fm0 H0) as [fm HF']; congruence.
  Qed.

  Lemma select_rf (γ : State) F y : RF γ F -> select (with_fibers Σ γ F) y = select γ y.
  Proof. intros R; unfold Scoped.select; rewrite (candidates_rf γ F y R); reflexivity. Qed.

  Lemma tied_rf (γ : State) F y :
    RF γ F -> tied N_eq_dec Σ xprog (with_fibers Σ γ F) y = tied N_eq_dec Σ xprog γ y.
  Proof. intros R; unfold Scoped.tied; rewrite (candidates_rf γ F y R); reflexivity. Qed.

  Lemma spawns_base (γ : State) : TInv γ -> KSpawnProv Σ xprog γ.
  Proof.
    intros [_ _ [_ Sp] _ _] x f m fm Hx Hu Hm.
    destruct (Sp x f m fm Hx Hu Hm) as [Hs|Hr].
    - left; cbn [Scoped.prog' body] in Hs; exact (spawnin_lift N_eq_dec Σ xprog _ _ _ _ Hs).
    - right; cbn [Scoped.prog' reacts] in Hr; exact (handlers_in N_eq_dec Σ xprog _ _ _ _ Hr).
  Qed.

  Lemma kinv_tinv (γ : State) : TInv γ -> SI γ -> KInv N_eq_dec Σ xprog γ.
  Proof.
    intros T S0; pose proof T as [W P [U _] _ _].
    split; [exact W | exact P | exact U | exact (spawns_base γ T) | exact S0].
  Qed.

  Lemma nfib_life (γ : State) f : life (nfib γ f) = life f.
  Proof. unfold nfib; destruct (fparent f); [|destruct (is_installed (life f))]; reflexivity. Qed.

  Lemma nfib_disposed (γ : State) f : disposed (nfib γ f) = disposed f.
  Proof. unfold nfib; destruct (fparent f); [|destruct (is_installed (life f))]; reflexivity. Qed.

  (** At a quiet state every child's selection is current. *)
  Lemma quiet_child_fresh (γ : State) n f q :
    KInv N_eq_dec Σ xprog γ -> kquiet γ -> NoFailed Σ γ -> fibers γ n = Some f -> fparent f = Some q ->
    fresh γ f = true.
  Proof.
    intros KI Q NF Hn Hq.
    pose proof (kquiet_settled N_eq_dec Σ xprog xrank Rb Hrank Hbnd kSub γ KI Q) as St.
    destruct (wf_parent kdec Σ prog' γ (ki_wf _ _ _ _ KI) n f q Hn Hq) as (fq & Hfq & Iq & _).
    destruct (kshape N_eq_dec Σ xprog γ q fq St NF Hfq) as [_ [[Lq _]|(accq & wq & Lq & _ & Fq)]];
      [rewrite Lq in Iq; discriminate|].
    exact (child_fresh N_eq_dec Σ xprog kSub γ n f q fq KI Hn Hq Hfq Fq).
  Qed.

  (** An unresolved exported name reads as the empty scope, which no fiber
      has, so its key is not visible. *)
  Lemma empty_invisible (γ : State) y : WF γ -> SI γ -> visible Σ γ ([], y) = None.
  Proof.
    intros W S0; unfold visible.
    destruct (binds γ ([], y)) as [b|] eqn:Hb; [|reflexivity].
    destruct (wf_bind kdec Σ prog' γ W _ b Hb) as (fo & Ho & _ & Hk & _).
    unfold fprovs in Hk; cbn [Scoped.prog' provs] in Hk.
    apply (kmem_provs N_eq_dec Σ xprog) in Hk; cbn in Hk.
    exfalso; exact (si_ne _ _ _ _ S0 _ fo Ho (eq_sym Hk)).
  Qed.

  Lemma final_norm2 (γ : State) :
    PInv γ -> SLInv Σ γ -> SI γ -> kquiet γ -> NoFailed Σ γ -> FinalS (norm γ).
  Proof.
    intros P SL S0 Q NF.
    pose proof (pinv_tinv γ P) as T; pose proof (t_wf _ _ _ _ _ T) as W.
    pose proof (kquiet_settled N_eq_dec Σ xprog xrank Rb Hrank Hbnd kSub γ (kinv_tinv γ T S0) Q) as St.
    split; [|exact (rf2_sl γ _ SL (rf2_norm γ))].
    split; [exact (rf2_pinv γ _ P (rf2_norm γ))|]; split.
    - intros n fm H; unfold norm in H; cbn [Calculus.fibers with_fibers] in H.
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate]; cbn in H; injection H as <-.
      pose proof (St n f Hn) as Sf; unfold ksettled_fiber, settled_fiber in *.
      rewrite nfib_life, nfib_disposed.
      assert (Ht : target Σ prog' (norm γ) n =
                   if disposed f then None else resolve Σ γ (deps Σ (prog' (fcomp (nfib γ f))))).
      { unfold Calculus.target, norm; cbn [Calculus.fibers with_fibers]; rewrite Hn; cbn [option_map].
        rewrite nfib_disposed; destruct (disposed f); [reflexivity|].
        apply resolve_ext; intros k; exact (visible_rf γ _ k (rf_norm γ)). }
      rewrite Ht.
      destruct (life f) as [[z|]|P0 acc w|acc w|acc w z] eqn:Hl; try exact Sf.
      + destruct Sf as [Hd Hbt]; split; [exact Hd|]; rewrite Hd.
        destruct (fparent f) as [q|] eqn:Hp.
        { unfold nfib; rewrite Hp.
          pose proof (quiet_child_fresh γ n f q (kinv_tinv γ T S0) Q NF Hn Hp) as Ff.
          rewrite (bt_fresh N_eq_dec Σ xprog γ n f Hn Ff) in Hbt.
          unfold Calculus.target in Hbt; rewrite Hn, Hd in Hbt; exact Hbt. }
        unfold nfib; rewrite Hp, Hl; cbn [is_installed Calculus.comp].
        unfold ScopedTerm.bt in Hbt; rewrite Hn, Hd in Hbt.
        destruct (all_selected γ (base (fcomp f))) eqn:A; [exact Hbt|].
        unfold Scoped.all_selected in A; apply Bool.not_true_iff_false in A.
        destruct (existsb (fun y => negb (Scoped.selected N_eq_dec Σ xprog γ y)) (globals (base (fcomp f)))) eqn:Ex.
        * apply existsb_exists in Ex as (y & Hy & Ey).
          apply (resolve_none Σ γ ([], y)); [|exact (empty_invisible γ y W S0)].
          cbn [Scoped.prog' deps]; unfold ScopedTerm.rcomp; cbn [base].
          apply in_map_iff; exists (Global y); split.
          -- unfold Scoped.dkey, Scoped.assoc_or; cbn [sel]; unfold Scoped.choose.
             rewrite (assoc_map N_eq_dec _ _ y Hy).
             unfold Scoped.selected in Ey; destruct (select γ y); [discriminate | reflexivity].
          -- unfold Scoped.globals in Hy; apply omap_In in Hy as (d & Hdd & E).
             destruct d as [y'|y']; [discriminate|]; injection E as ->; exact Hdd.
        * exfalso; apply A; apply forallb_forall; intros y Hy.
          destruct (Scoped.selected N_eq_dec Σ xprog γ y) eqn:Es; [reflexivity|].
          assert (existsb (fun y => negb (Scoped.selected N_eq_dec Σ xprog γ y)) (globals (base (fcomp f))) = true)
            by (apply existsb_exists; exists y; rewrite Es; auto).
          congruence.
      + destruct Sf as [Ht' _].
        unfold Calculus.target in Ht'; rewrite Hn in Ht'.
        unfold nfib; destruct (fparent f); [exact Ht'|]; rewrite Hl; cbn [is_installed]; exact Ht'.
    - intros n fm e H; unfold norm in H; cbn [Calculus.fibers with_fibers] in H.
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate]; cbn in H; injection H as <-.
      rewrite nfib_life; exact (NF n f e Hn).
  Qed.

  (** Every fiber's selection is current. *)
  Definition Fresh (γ : State) : Prop :=
    forall n f, fibers γ n = Some f -> sel (fcomp f) = choose γ (base (fcomp f)).

  Lemma choose_rf (γ : State) F c : RF γ F -> choose (with_fibers Σ γ F) c = choose γ c.
  Proof. intros R; apply choose_ext; intros y _; apply (select_rf γ F y R). Qed.

  Lemma fresh_norm (γ : State) :
    PInv γ -> SI γ -> kquiet γ -> NoFailed Σ γ -> Fresh (norm γ).
  Proof.
    intros P S0 Q NF n fm H.
    pose proof (pinv_tinv γ P) as T.
    pose proof (kquiet_settled N_eq_dec Σ xprog xrank Rb Hrank Hbnd kSub γ (kinv_tinv γ T S0) Q) as St.
    unfold norm in H |- *; rewrite (choose_rf γ _ _ (rf_norm γ)).
    cbn [Calculus.fibers with_fibers] in H.
    destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate]; cbn in H; injection H as <-.
    assert (Cur : fresh γ f = true -> sel (fcomp f) = choose γ (base (fcomp f))).
    { intros F; unfold Scoped.fresh in F; apply andb_true_iff in F as [_ F].
      destruct (list_eq_dec (ns_eq_dec N_eq_dec) (sel (fcomp f)) (choose γ (base (fcomp f)))) as [E|];
        [exact E | discriminate]. }
    destruct (fparent f) as [q|] eqn:Hp.
    { unfold nfib; rewrite Hp; exact (Cur (quiet_child_fresh γ n f q (kinv_tinv γ T S0) Q NF Hn Hp)). }
    destruct (kshape N_eq_dec Σ xprog γ n f St NF Hn) as [_ [[Hl _]|(acc & w & Hl & _ & F)]];
      unfold nfib; rewrite Hp, Hl; cbn [is_installed].
    - reflexivity.
    - unfold Scoped.fresh in F; apply andb_true_iff in F as [_ F].
      destruct (list_eq_dec (ns_eq_dec N_eq_dec) (sel (fcomp f)) (choose γ (base (fcomp f)))) as [E|];
        [exact E | discriminate].
  Qed.

  (** ** Selections follow the correspondence at lower ranks *)
  Lemma vis_scope (γ : State) a fa y :
    CInv0 kdec Σ prog' Kb γ -> SI γ -> fibers γ a = Some fa ->
    ((exists p, visible Σ γ (scope (fcomp fa), y) = Some p) <->
     is_active (life fa) = true /\ In y (xprovs (base (fcomp fa)))).
  Proof.
    intros CI S0 Ha; pose proof (t_wf _ _ _ _ _ (c0_t _ _ _ _ _ CI)) as W; split.
    - intros [p Hv]; unfold visible in Hv.
      destruct (binds γ (scope (fcomp fa), y)) as [b|] eqn:Hb; [|discriminate].
      destruct (fibers γ (owner b)) as [fo|] eqn:Ho; [|discriminate].
      destruct (is_active (life fo)) eqn:Hac; [|discriminate].
      destruct (wf_bind kdec Σ prog' γ W _ b Hb) as (fo' & Ho' & _ & Hk & _).
      rewrite Ho in Ho'; injection Ho' as <-.
      pose proof (provs_name N_eq_dec Σ xprog _ _ Hk) as Hy; cbn in Hy.
      unfold fprovs in Hk; cbn [Scoped.prog' provs] in Hk.
      apply (kmem_provs N_eq_dec Σ xprog) in Hk; cbn in Hk.
      pose proof (si_uniq _ _ _ _ S0 _ a fo fa Ho Ha (eq_sym Hk)) as Eo.
      rewrite Eo, Ha in Ho; injection Ho as <-; auto.
    - intros [Hac Hy].
      assert (Hk : In (scope (fcomp fa), y) (provs Σ (prog' (fcomp fa))))
        by (cbn [Scoped.prog' provs]; apply in_map; exact Hy).
      destruct (active_binds kdec Σ prog' Kb γ a fa _ CI Ha Hac Hk) as (b & Hb & Ho).
      exists (pid Σ b); unfold visible; rewrite Hb, Ho, Ha, Hac; reflexivity.
  Qed.

  Lemma candidate_corr (γa γb : State) a fa b fb y :
    FinalS γa -> FinalS γb -> SI γa -> SI γb ->
    fibers γa a = Some fa -> fibers γb b = Some fb -> fcomp fb = fcomp fa ->
    is_active (life fb) = is_active (life fa) ->
    candidate γa y a = candidate γb y b.
  Proof.
    intros Fa Fb Sa Sb Ha Hb Ec Eact.
    pose proof (s_c _ _ _ _ _ (p_s _ _ _ _ _ (proj1 (proj1 Fa)))) as CIa.
    pose proof (s_c _ _ _ _ _ (p_s _ _ _ _ _ (proj1 (proj1 Fb)))) as CIb.
    unfold Scoped.candidate; rewrite Ha, Hb, Ec.
    destruct (nmem N_eq_dec y (xexports Σ (xprog (base (fcomp fa))))); [|reflexivity].
    pose proof (vis_scope γa a fa y CIa Sa Ha) as Va.
    pose proof (vis_scope γb b fb y CIb Sb Hb) as Vb; rewrite Ec, Eact in Vb.
    destruct (visible Σ γa (scope (fcomp fa), y)) as [p1|] eqn:V1,
             (visible Σ γb (scope (fcomp fa), y)) as [p2|] eqn:V2; try reflexivity.
    - exfalso; destruct (proj2 Vb (proj1 Va (ex_intro _ p1 eq_refl))) as [p E]; discriminate.
    - exfalso; destruct (proj2 Va (proj1 Vb (ex_intro _ p2 eq_refl))) as [p E]; discriminate.
  Qed.

  Lemma omap_flat {A B} (g : A -> option B) l :
    omap g l = concat (filter nonnil (map (fun a => match g a with Some b => [b] | None => [] end) l)).
  Proof.
    induction l as [|a l IH]; cbn; [reflexivity|].
    destruct (g a); cbn; rewrite IH; reflexivity.
  Qed.

  Lemma perm_concat {A} (L1 L2 : list (list A)) : Permutation L1 L2 -> Permutation (concat L1) (concat L2).
  Proof.
    intros H; induction H; cbn.
    - constructor.
    - apply Permutation_app_head; exact IHPermutation.
    - rewrite !app_assoc; apply Permutation_app_tail, Permutation_app_comm.
    - eapply perm_trans; eassumption.
  Qed.

  Lemma filter_perm {A} (g : A -> bool) l1 l2 : Permutation l1 l2 -> Permutation (filter g l1) (filter g l2).
  Proof.
    intros H; induction H; cbn.
    - constructor.
    - destruct (g x); [constructor|]; exact IHPermutation.
    - destruct (g x), (g y); first [apply perm_swap | constructor; apply Permutation_refl | apply Permutation_refl].
    - eapply perm_trans; eassumption.
  Qed.

  Lemma top_perm (l1 l2 : list (Scope * nat)) :
    Permutation l1 l2 ->
    fold_right (fun c m => Nat.max (snd c) m) 0 l1 = fold_right (fun c m => Nat.max (snd c) m) 0 l2.
  Proof. intros H; induction H; cbn; lia. Qed.

  Lemma select_perm (γ1 γ2 : State) y :
    Permutation (candidates γ1 y) (candidates γ2 y) ->
    select γ1 y = select γ2 y /\ tied N_eq_dec Σ xprog γ1 y = tied N_eq_dec Σ xprog γ2 y.
  Proof.
    intros Hp; unfold Scoped.select, Scoped.tied.
    rewrite <- (top_perm _ _ Hp).
    pose proof (filter_perm (fun c => Nat.eqb (snd c) (fold_right (fun c m => Nat.max (snd c) m) 0 (candidates γ1 y))) _ _ Hp) as Hf.
    split; [|rewrite (Permutation_length Hf); reflexivity].
    destruct (filter _ (candidates γ1 y)) as [|[s p] [|c2 l]] eqn:E1.
    - apply Permutation_nil in Hf; rewrite Hf; reflexivity.
    - apply Permutation_length_1_inv in Hf; rewrite Hf; reflexivity.
    - pose proof (Permutation_length Hf) as L; cbn in L.
      destruct (filter _ (candidates γ2 y)) as [|[s' p'] [|c2' l']]; cbn in L; try lia; reflexivity.
  Qed.

  Local Notation Corresp := (Corresp kdec Σ prog' rank').

  Lemma select_corr la lb (γa γb : State) r y :
    FinalS γa -> FinalS γb -> SI γa -> SI γb -> RootInj Σ la γa -> RootInj Σ lb γb ->
    Corresp la lb γa γb r -> Corresp lb la γb γa r ->
    (forall c', In y (xexports Σ (xprog c')) -> xrank c' < r) ->
    select γa y = select γb y /\ tied N_eq_dec Σ xprog γa y = tied N_eq_dec Σ xprog γb y.
  Proof.
    intros Fa Fb Sa Sb RIa RIb Cab Cba HE.
    pose proof (p_s _ _ _ _ _ (proj1 (proj1 Fa))) as SIa; pose proof (p_s _ _ _ _ _ (proj1 (proj1 Fb))) as SIb.
    pose proof (sinv_wf _ _ _ _ _ SIa) as Wa; pose proof (sinv_wf _ _ _ _ _ SIb) as Wb.
    apply select_perm; unfold Scoped.candidates, names; rewrite !omap_flat.
    apply perm_concat.
    apply (perm_bij_blocks _ _ (fun a b => exists x fa, CN Σ la γa a x /\ CN Σ lb γb b x /\
                                     fibers γa a = Some fa /\ rank' (fcomp fa) < r));
      [apply seq_NoDup | apply seq_NoDup | | | | |].
    - intros a _; destruct (candidate γa y a) as [cd|] eqn:Ec; [right|left; reflexivity].
      unfold Scoped.candidate in Ec; destruct (fibers γa a) as [fa|] eqn:Ha; [|discriminate].
      destruct (nmem N_eq_dec y (xexports Σ (xprog (base (fcomp fa))))) eqn:Ex; [|discriminate].
      assert (Hr : rank' (fcomp fa) < r) by (apply HE; exact (nmem_In N_eq_dec y _ Ex)).
      destruct (cn_total kdec Σ prog' Kb la γa a fa SIa (proj2 Fa) Ha) as [x Hx].
      destruct (Cab x a fa Hx Ha Hr) as (b & fb & Hxb & Hb & _).
      exists b; split; [apply in_seq; pose proof (wf_names kdec Σ prog' γb Wb b fb Hb); lia|].
      exists x, fa; auto.
    - intros b _; destruct (candidate γb y b) as [cd|] eqn:Ec; [right|left; reflexivity].
      unfold Scoped.candidate in Ec; destruct (fibers γb b) as [fb|] eqn:Hb; [|discriminate].
      destruct (nmem N_eq_dec y (xexports Σ (xprog (base (fcomp fb))))) eqn:Ex; [|discriminate].
      assert (Hr : rank' (fcomp fb) < r) by (apply HE; exact (nmem_In N_eq_dec y _ Ex)).
      destruct (cn_total kdec Σ prog' Kb lb γb b fb SIb (proj2 Fb) Hb) as [x Hx].
      destruct (Cba x b fb Hx Hb Hr) as (a & fa & Hxa & Ha & Hc & _).
      exists a; split; [apply in_seq; pose proof (wf_names kdec Σ prog' γa Wa a fa Ha); lia|].
      exists x, fa; split; [exact Hxa|]; split; [exact Hx|]; split; [exact Ha|]; rewrite Hc; exact Hr.
    - intros a b b' (x & fa & Ha & Hb & _) (x' & fa' & Ha' & Hb' & _).
      rewrite (cn_fun Σ la γa a x x' (proj2 Fa) Ha Ha') in Hb; exact (cn_inj Σ lb γb b b' x' RIb Hb Hb').
    - intros a a' b (x & fa & Ha & Hb & _) (x' & fa' & Ha' & Hb' & _).
      rewrite (cn_fun Σ lb γb b x x' (proj2 Fb) Hb Hb') in Ha; exact (cn_inj Σ la γa a a' x' RIa Ha Ha').
    - intros a b (x & fa & Hxa & Hxb & Ha & Hr).
      destruct (Cab x a fa Hxa Ha Hr) as (b' & fb & Hxb' & Hb & Hc & Hact & _).
      rewrite <- (cn_inj Σ lb γb b b' x RIb Hxb Hxb') in Hb.
      rewrite (candidate_corr γa γb a fa b fb y Fa Fb Sa Sb Ha Hb Hc Hact); reflexivity.
  Qed.

  (** ** The rank induction, with roots matched up to the selection *)
  Definition RootsMatchX (la lb : nat -> nat) (γa γb : State) : Prop :=
    forall n fa, fibers γa n = Some fa -> fparent fa = None ->
      exists nb fb, fibers γb nb = Some fb /\ fparent fb = None /\ lb nb = la n /\
                    base (fcomp fb) = base (fcomp fa) /\ scope (fcomp fb) = scope (fcomp fa) /\
                    env (fcomp fb) = env (fcomp fa) /\ tick (fcomp fb) = tick (fcomp fa).

  Lemma choose_corr la lb (γa γb : State) r c :
    FinalS γa -> FinalS γb -> SI γa -> SI γb -> RootInj Σ la γa -> RootInj Σ lb γb ->
    Corresp la lb γa γb r -> Corresp lb la γb γa r -> xrank c <= r ->
    choose γa c = choose γb c.
  Proof.
    intros Fa Fb Sa Sb RIa RIb Cab Cba Hr; unfold Scoped.choose; apply map_ext_in; intros y Hy.
    assert (HE : forall c', In y (xexports Σ (xprog c')) -> xrank c' < r).
    { intros c' He; assert (xrank c' < xrank c); [|lia].
      apply Hrank; left; exists y; split; [exact (exports_provs Σ xprog _ _ He)|].
      exact (globals_dname Σ xprog _ _ Hy). }
    rewrite (proj1 (select_corr la lb γa γb r y Fa Fb Sa Sb RIa RIb Cab Cba HE)); reflexivity.
  Qed.

  Lemma corr_stepX la lb (γa γb : State) r :
    FinalS γa -> FinalS γb -> SI γa -> SI γb -> Fresh γa -> Fresh γb ->
    RootInj Σ la γa -> RootInj Σ lb γb -> RootsMatchX la lb γa γb ->
    Corresp la lb γa γb r -> Corresp lb la γb γa r -> Corresp la lb γa γb (Datatypes.S r).
  Proof.
    intros Fa Fb Sa Sb Fra Frb RIa RIb RM IHab IHba x na fa CNa Ha Hr.
    assert (Hr' : rank' (fcomp fa) <= r) by (cbn in Hr |- *; lia).
    pose proof (p_s _ _ _ _ _ (proj1 (proj1 Fb))) as SIb.
    assert (Find : exists nb fb, CN Σ lb γb nb x /\ fibers γb nb = Some fb /\ fcomp fb = fcomp fa).
    { inversion CNa as [n f Hn Hp|n f p fp y j Hn Hp Hfp Hy Hj]; subst; rewrite Ha in Hn; injection Hn as <-.
      - destruct (RM na fa Ha Hp) as (nb & fb & Hfb & Hpb & Hl & Eb & Es & Ee & Et).
        exists nb, fb; split; [rewrite <- Hl; exact (cn_root Σ lb γb nb fb Hfb Hpb)|]; split; [exact Hfb|].
        rewrite (xc_eta (fcomp fb)), (xc_eta (fcomp fa)), (Fra na fa Ha), (Frb nb fb Hfb), Eb, Es, Ee, Et.
        f_equal; symmetry; exact (choose_corr la lb γa γb r _ Fa Fb Sa Sb RIa RIb IHab IHba Hr').
      - destruct (final_fiber kdec Σ prog' Kb γa p fp (proj1 Fa) Hfp) as [E|(accp & wp & evp & Lp & Tp & Cp)].
        { unfold SpawnAt in Hj; rewrite E in Hj; cbn in Hj; destruct j; discriminate. }
        unfold SpawnAt in Hj; rewrite Lp in Hj; cbn [acc_of] in Hj.
        destruct (f2_nth _ _ _ j na (f2_rev _ _ _ (corr_f2 _ _ _ _ _ _ _ _ Cp)) Hj) as (c' & Hc' & Hca).
        pose proof (Hca fa Ha) as Ec.
        assert (Hsp : SpawnIn Σ c' (body Σ (prog' (fcomp fp)))).
        { apply (tr_spawnin kdec Σ prog' _ _ _ _ c' Tp); apply (proj2 (in_rev _ _)); exact (nth_error_In _ _ Hc'). }
        assert (Hrp : rank' (fcomp fp) < r).
        { pose proof (Hrank2 (fcomp fp) c' (or_intror (or_introl Hsp))); rewrite <- Ec in *; lia. }
        destruct (IHab y p fp Hy Hfp Hrp) as (pb & fpb & CNpb & Hfpb & Hcpb & Hapb & Hevp).
        rewrite Lp in Hapb; cbn in Hapb.
        destruct (final_fiber kdec Σ prog' Kb γb pb fpb (proj1 Fb) Hfpb) as [E|(accpb & wpb & evpb & Lpb & Tpb & Cpb)];
          [rewrite E in Hapb; discriminate|].
        pose proof (Hevp accp wp evp accpb wpb evpb Lp Lpb Tp Cp Tpb Cpb) as Eev.
        rewrite Eev in Hc'.
        destruct (f2_nth_r _ _ _ j c' (f2_rev _ _ _ (corr_f2 _ _ _ _ _ _ _ _ Cpb)) Hc') as (nb & Hnb & Hcb).
        assert (Inb : In nb (spawns Σ (acc_of (life fpb)))).
        { rewrite Lpb; apply (proj2 (in_rev _ _)); exact (nth_error_In _ _ Hnb). }
        destruct (sl_live _ _ (proj2 Fb) pb fpb nb Hfpb Inb) as [(a1 & w1 & z1 & E)|(fb & Hfb & _)];
          [rewrite Lpb in E; discriminate|].
        pose proof (t_so kdec Σ prog' Kb γb (c0_t kdec Σ prog' Kb γb (s_c _ _ _ _ _ SIb)) pb fpb nb fb Hfpb
                      (proj1 (in_spawns _ _ _) Inb) Hfb) as Hpar.
        exists nb, fb; split; [|split; [exact Hfb | rewrite (Hcb fb Hfb); exact (eq_sym Ec)]].
        apply (cn_child Σ lb γb nb fb pb fpb y j Hfb Hpar Hfpb CNpb); unfold SpawnAt; rewrite Lpb; exact Hnb. }
    destruct Find as (nb & fb & CNb & Hb & Hc).
    destruct (corr_pair kdec Σ prog' Kb rank' Hrank2 Hwb la lb γa γb r na fa nb fb Fa Fb IHab IHba Ha Hb Hc Hr')
      as [Hact Htr].
    exists nb, fb; auto.
  Qed.

  Lemma corresp_allX l1 l2 (γ1 γ2 : State) :
    FinalS γ1 -> FinalS γ2 -> SI γ1 -> SI γ2 -> Fresh γ1 -> Fresh γ2 ->
    RootInj Σ l1 γ1 -> RootInj Σ l2 γ2 ->
    RootsMatchX l1 l2 γ1 γ2 -> RootsMatchX l2 l1 γ2 γ1 ->
    forall r, Corresp l1 l2 γ1 γ2 r /\ Corresp l2 l1 γ2 γ1 r.
  Proof.
    intros F1 F2 S1 S2 Fr1 Fr2 RI1 RI2 R12 R21 r; induction r as [|r [IH12 IH21]].
    - split; intros x na fa _ _ Hr; lia.
    - split; [exact (corr_stepX l1 l2 γ1 γ2 r F1 F2 S1 S2 Fr1 Fr2 RI1 RI2 R12 IH12 IH21)
             | exact (corr_stepX l2 l1 γ2 γ1 r F2 F1 S2 S1 Fr2 Fr1 RI2 RI1 R21 IH21 IH12)].
  Qed.

  (** ** Two final states with matching roots agree up to renaming *)
  Local Notation CoPair_sym := (Recovery.CoPair_sym Σ prog').

  Theorem final_agreeX l1 l2 (γ1 γ2 : State) :
    FinalS γ1 -> FinalS γ2 -> SI γ1 -> SI γ2 -> Fresh γ1 -> Fresh γ2 ->
    RootInj Σ l1 γ1 -> RootInj Σ l2 γ2 ->
    RootsMatchX l1 l2 γ1 γ2 -> RootsMatchX l2 l1 γ2 γ1 ->
    AgreeL Σ l1 l2 γ1 γ2.
  Proof.
    intros F1 F2 Si1 Si2 Fr1 Fr2 RI1 RI2 RM12 RM21; unfold AgreeL.
    pose proof (proj2 F1) as S1; pose proof (proj2 F2) as S2.
    pose proof (proj1 (proj1 F1)) as P1; pose proof (proj1 (proj1 F2)) as P2.
    destruct (corresp_allX l1 l2 γ1 γ2 F1 F2 Si1 Si2 Fr1 Fr2 RI1 RI2 RM12 RM21 (Datatypes.S Rb)) as [C12 C21].
    assert (Hr : forall c : XC, rank' c < Datatypes.S Rb) by (intros c; pose proof (Hbnd (base c)); cbn; lia).
    pose proof (p_s _ _ _ _ _ P1) as SI1; pose proof (p_s _ _ _ _ _ P2) as SI2.
    pose proof (sinv_wf _ _ _ _ _ SI1) as W1; pose proof (sinv_wf _ _ _ _ _ SI2) as W2.
    assert (Own : forall la lb (γa γb : State) (Fa : FinalS γa) (Fb : FinalS γb),
              Corresp la lb γa γb (Datatypes.S Rb) ->
              forall k ba x, binds γa k = Some ba -> CN Σ la γa (owner ba) x ->
              exists bb, binds γb k = Some bb /\ CN Σ lb γb (owner bb) x).
    { intros la lb γa γb Fa Fb Cab k ba x Hba Hx.
      pose proof (p_s _ _ _ _ _ (proj1 (proj1 Fa))) as SIa; pose proof (p_s _ _ _ _ _ (proj1 (proj1 Fb))) as SIb.
      destruct (wf_bind kdec Σ prog' γa (sinv_wf _ _ _ _ _ SIa) k ba Hba) as (fo & Hfo & _ & Hkp & Hup).
      destruct (final_fiber kdec Σ prog' Kb γa _ fo (proj1 Fa) Hfo) as [E|(acc & w & evs & Lo & _ & _)];
        [rewrite E in Hup; destruct Hup|].
      destruct (Cab x _ fo Hx Hfo (Hr _)) as (ob & fob & CNb & Hfob & Hc & Ha & _).
      rewrite Lo in Ha; cbn in Ha.
      assert (Hkb : In k (provs Σ (prog' (fcomp fob)))) by (rewrite Hc; exact (kmem_In kdec k _ Hkp)).
      pose proof (proj2 (owner_iff kdec Σ prog' Kb γb k ob (s_c _ _ _ _ _ SIb) (proj1 (proj2 (proj1 Fb)))
                           (proj2 (proj2 (proj1 Fb)))) (ex_intro _ fob (conj Hfob (conj Ha Hkb)))) as E.
      destruct (binds γb k) as [bb|]; [|discriminate]; injection E as E.
      exists bb; split; [reflexivity | rewrite E; exact CNb]. }
    split; [intros n f H; exact (cn_total kdec Σ prog' Kb l1 γ1 n f SI1 S1 H)|].
    split; [intros n f H; exact (cn_total kdec Σ prog' Kb l2 γ2 n f SI2 S2 H)|].
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
    destruct (wf_bind kdec Σ prog' γ1 W1 k b1 Hb1) as (fo1 & Hfo1 & _ & _ & Hup1).
    destruct (wf_bind kdec Σ prog' γ2 W2 k b2 Hb2) as (fo2 & Hfo2 & _ & _ & Hup2).
    destruct (cn_total kdec Σ prog' Kb l1 γ1 _ fo1 SI1 S1 Hfo1) as [x Hx].
    destruct (Own l1 l2 γ1 γ2 F1 F2 C12 k b1 x Hb1 Hx) as (b2' & Hb2' & Hx2).
    rewrite Hb2 in Hb2'; injection Hb2' as <-.
    destruct (C12 x _ fo1 Hx Hfo1 (Hr _)) as (o2 & fo2' & CN2 & Hfo2' & Hc0 & Ha0 & Htr).
    rewrite <- (cn_inj Σ l2 γ2 _ _ x RI2 Hx2 CN2) in Hfo2'; rewrite Hfo2 in Hfo2'; injection Hfo2' as <-.
    destruct (final_fiber kdec Σ prog' Kb γ1 _ fo1 (proj1 F1) Hfo1) as [E|(acc1 & w1 & evs1 & L1' & T1 & C1)];
      [rewrite E in Hup1; destruct Hup1|].
    destruct (final_fiber kdec Σ prog' Kb γ2 _ fo2 (proj1 F2) Hfo2) as [E|(acc2 & w2 & evs2 & L2' & T2 & C2)];
      [rewrite E in Hup2; destruct Hup2|].
    pose proof (Htr acc1 w1 evs1 acc2 w2 evs2 L1' L2' T1 C1 T2 C2) as Eev.
    pose proof (wf_uprov_unique kdec Σ prog' γ1 W1 _ fo1 Hfo1) as U1; rewrite L1' in U1, Hup1.
    pose proof (wf_uprov_unique kdec Σ prog' γ2 W2 _ fo2 Hfo2) as U2; rewrite L2' in U2, Hup2.
    destruct (corr_find kdec Σ prog' γ1 _ w1 acc1 evs1 k (pid Σ b1) C1 U1 Hup1) as (s1' & Hi1' & Hf1).
    destruct (corr_find kdec Σ prog' γ2 _ w2 acc2 evs2 k (pid Σ b2) C2 U2 Hup2) as (s2' & Hi2' & Hf2).
    assert (s02 = s01) by (rewrite Eev in Hf1; congruence); subst s02.
    destruct (final_blocks kdec Σ prog' Kb Hwb HCom γ1 k b1 L1 (Calculus.next Σ γ1) s01 s1 (proj1 F1) (le_n _) Hb1 PL1 Rp1)
      as (x1 & X1 & Ex1).
    destruct (final_blocks kdec Σ prog' Kb Hwb HCom γ2 k b2 L2 (Calculus.next Σ γ2) s01 s2 (proj1 F2) (le_n _) Hb2 PL2 Rp2)
      as (x2 & X2 & Ex2).
    assert (EM : Permutation (filter nonnil (map (map fst) (map (blockAt kdec Σ γ1 k) (seq 0 (Calculus.next Σ γ1)))))
                             (filter nonnil (map (map fst) (map (blockAt kdec Σ γ2 k) (seq 0 (Calculus.next Σ γ2)))))).
    { rewrite !map_map.
      apply (perm_bij_blocks _ _ (fun a b => exists x, CN Σ l1 γ1 a x /\ CN Σ l2 γ2 b x));
        [apply seq_NoDup | apply seq_NoDup | | | | |].
      - intros a _; unfold blockAt, itemsAt; destruct (fibers γ1 a) as [fa|] eqn:Ha; [|left; reflexivity].
        right; destruct (cn_total kdec Σ prog' Kb l1 γ1 a fa SI1 S1 Ha) as [y Hy].
        destruct (C12 y a fa Hy Ha (Hr _)) as (b & fb & Hyb & Hb & _).
        exists b; split; [apply in_seq; pose proof (wf_names kdec Σ prog' γ2 W2 b fb Hb); lia | exists y; auto].
      - intros b _; unfold blockAt, itemsAt; destruct (fibers γ2 b) as [fb|] eqn:Hb; [|left; reflexivity].
        right; destruct (cn_total kdec Σ prog' Kb l2 γ2 b fb SI2 S2 Hb) as [y Hy].
        destruct (C21 y b fb Hy Hb (Hr _)) as (a & fa & Hya & Ha & _).
        exists a; split; [apply in_seq; pose proof (wf_names kdec Σ prog' γ1 W1 a fa Ha); lia | exists y; auto].
      - intros a b b' (y & Ha & Hb) (y' & Ha' & Hb').
        rewrite (cn_fun Σ l1 γ1 a y y' S1 Ha Ha') in Hb; exact (cn_inj Σ l2 γ2 b b' y' RI2 Hb Hb').
      - intros a a' b (y & Ha & Hb) (y' & Ha' & Hb').
        rewrite (cn_fun Σ l2 γ2 b y y' S2 Hb Hb') in Ha; exact (cn_inj Σ l1 γ1 a a' y' RI1 Ha Ha').
      - intros a b (y & Ha & Hb).
        destruct (cn_present Σ l1 γ1 a y Ha) as [fa Hfa]; destruct (cn_present Σ l2 γ2 b y Hb) as [fb Hfb].
        destruct (C12 y a fa Ha Hfa (Hr _)) as (b' & fb' & Hb' & Hfb' & _ & Hact & Htr').
        rewrite <- (cn_inj Σ l2 γ2 _ _ y RI2 Hb Hb') in Hfb'; rewrite Hfb in Hfb'; injection Hfb' as <-.
        unfold blockAt, itemsAt; rewrite Hfa, Hfb, !map_rev; f_equal.
        destruct (final_fiber kdec Σ prog' Kb γ1 a fa (proj1 F1) Hfa) as [Ea|(acca & wa & evsa & La & Ta & Ca)];
          destruct (final_fiber kdec Σ prog' Kb γ2 b fb (proj1 F2) Hfb) as [Eb|(accb & wb & evsb & Lb & Tb & Cb)].
        + unfold uacc; rewrite Ea, Eb; reflexivity.
        + rewrite Ea, Lb in Hact; discriminate.
        + rewrite La, Eb in Hact; discriminate.
        + unfold uacc; rewrite La, Lb; cbn [acc_of].
          rewrite (corr_ops kdec Σ prog' γ1 _ _ _ _ k Ca), (corr_ops kdec Σ prog' γ2 _ _ _ _ k Cb); f_equal.
          exact (Htr' acca wa evsa accb wb evsb La Lb Ta Ca Tb Cb). }
    pose proof (replay_blocks (CoPair Σ prog' k) Hwb HTI (CoPair_sym k) (HCom k) _ _ s01 x1 x2
                  (blocks_cross kdec Σ prog' Kb γ1 k _ SI1 (seq_NoDup _ _)) EM X1 X2) as Es.
    transitivity s1; [exact E1|]; transitivity x1; [exact Ex1|]; transitivity x2; [exact Es|].
    transitivity s2; symmetry; assumption.
  Qed.

  (** ** Confluence with spawn *)
  Lemma roots_matchX (γ0 γ1 γ2 : State) :
    KRootKeep γ0 γ1 -> KRootKeep γ0 γ2 -> Final γ1 ->
    RootsMatchX (fun n => n) (fun n => n) γ1 γ2.
  Proof.
    intros [A1 _] [A2 B2] F1 n fa Ha Hp.
    destruct (A1 n fa Ha Hp) as (f0 & H0 & P0 & Cb0 & Cs0 & Ce0 & Ct0 & D0).
    destruct (settled_shape Σ prog' γ1 n fa (proj1 (proj2 F1)) (proj2 (proj2 F1)) Ha) as [Hd _].
    destruct (B2 n f0 H0 P0 ltac:(congruence)) as (fb & Hb & Pb & _).
    destruct (A2 n fb Hb Pb) as (f0' & H0' & _ & Cb1 & Cs1 & Ce1 & Ct1 & _).
    rewrite H0 in H0'; injection H0' as <-.
    exists n, fb; split; [exact Hb|]; split; [exact Pb|]; split; [reflexivity|].
    repeat split; congruence.
  Qed.

  (** Two extended lifecycle runs from a common state, ending quiet with no
      failure, agree up to renaming once the stale selections of their
      Inactive fibers are normalised ([norm] changes nothing else: the
      bindings, parents, lives, base components and scopes stay as they
      are); and every exported name is resolved alike, with the same ties. *)
  Theorem kspawn_confluence (γ0 γ1 γ2 : State) :
    PInv γ0 -> SLInv Σ γ0 -> SI γ0 ->
    KLRun γ0 γ1 -> KLRun γ0 γ2 ->
    kquiet γ1 -> kquiet γ2 -> NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    Agree Σ (norm γ1) (norm γ2) /\
    (forall y, select γ1 y = select γ2 y /\ tied N_eq_dec Σ xprog γ1 y = tied N_eq_dec Σ xprog γ2 y).
  Proof.
    intros P0 S0 I0 R1 R2 Q1 Q2 NF1 NF2.
    destruct (klrun_inv γ0 γ1 P0 S0 I0 R1) as (P1 & S1 & I1 & K1).
    destruct (klrun_inv γ0 γ2 P0 S0 I0 R2) as (P2 & S2 & I2 & K2).
    pose proof (final_norm2 γ1 P1 S1 I1 Q1 NF1) as F1; pose proof (final_norm2 γ2 P2 S2 I2 Q2 NF2) as F2.
    pose proof (fresh_norm γ1 P1 I1 Q1 NF1) as Fr1; pose proof (fresh_norm γ2 P2 I2 Q2 NF2) as Fr2.
    pose proof (si_rf γ1 _ (t_wf _ _ _ _ _ (pinv_tinv γ1 P1)) I1 (rf2_norm γ1)) as N1;
    pose proof (si_rf γ2 _ (t_wf _ _ _ _ _ (pinv_tinv γ2 P2)) I2 (rf2_norm γ2)) as N2.
    pose proof (krk_trans _ _ _ K1 (krk_rf γ1 _ (rf_norm γ1))) as K1'.
    pose proof (krk_trans _ _ _ K2 (krk_rf γ2 _ (rf_norm γ2))) as K2'.
    assert (RI : forall γ : State, RootInj Σ (fun n => n) γ) by (intros γ n n' f f' _ _ _ _ E; exact E).
    assert (RM12 := roots_matchX γ0 _ _ K1' K2' (proj1 F1)).
    assert (RM21 := roots_matchX γ0 _ _ K2' K1' (proj1 F2)).
    split; [exact (final_agreeX _ _ (norm γ1) (norm γ2) F1 F2 N1 N2 Fr1 Fr2 (RI _) (RI _) RM12 RM21)|].
    intros y.
    destruct (corresp_allX _ _ (norm γ1) (norm γ2) F1 F2 N1 N2 Fr1 Fr2 (RI _) (RI _) RM12 RM21 (Datatypes.S Rb))
      as [C12 C21].
    assert (HE : forall c', In y (xexports Σ (xprog c')) -> xrank c' < Datatypes.S Rb)
      by (intros c' _; pose proof (Hbnd c'); lia).
    destruct (select_corr _ _ (norm γ1) (norm γ2) _ y F1 F2 N1 N2 (RI _) (RI _) C12 C21 HE) as [Es Et].
    unfold norm in Es, Et; rewrite (select_rf γ1 _ y (rf_norm γ1)), (select_rf γ2 _ y (rf_norm γ2)) in Es.
    rewrite (tied_rf γ1 _ y (rf_norm γ1)), (tied_rf γ2 _ y (rf_norm γ2)) in Et.
    auto.
  Qed.
End ScopedSpawn.
