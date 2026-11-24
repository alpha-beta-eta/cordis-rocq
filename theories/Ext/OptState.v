(** * Extension 1: confluence of service states with optional dependencies

    Counterpart of [StateConf.state_confluence] (components that spawn
    nothing): two extended lifecycle executions from a common state that
    end quiet with no fiber failed leave every bound key with service
    states related by ≃.

    The core proof compares two final states through the invariant [PInv]
    (each binding's state replays its pending operations; each Active
    fiber's accumulator is an ideal trace of its program) and asks that
    corresponding fibers have equal components. Two things change.
    - [PInv] must survive the extension's non-core move, re-choosing the
      presence of an Inactive fiber. More generally it survives any change
      of the components of Inactive fibers that keeps their base
      components ([RF], [rf_pinv]): an Inactive fiber holds no undo item
      and no trace.
    - At a final state an Inactive fiber may keep a stale presence, so two
      final states need not have equal components there. They are
      normalised first ([norm]): every Inactive fiber takes the presence of
      the final state. Normalising keeps [PInv], the bindings, and
      settledness; and by [xcontrol_confluence] the two normalised states
      have equal components everywhere. The core comparison then applies. *)

From Stdlib Require Import List PeanoNat Bool Lia RelationClasses Permutation Sorted Wf_nat.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering
  Recovery Progress Termination Confluence StateInv Episode StateConf.
From Cordis Require Import Ext.Optional Ext.OptProgress Ext.OptConfluence.
Import ListNotations.

Section OptState.
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

  (** ** Hypotheses *)
  Variable Kb : nat.
  Hypothesis xHK : forall c T, Bounded Σ Kb (xbody Σ (xprog c) T).
  Variable xrank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', XAbove Σ xprog c c' -> xrank c < xrank c'.
  Hypothesis Hbnd : forall c, xrank c <= Rb.
  Hypothesis xNoSpawn : forall c T c', ~ SpawnIn Σ c' (xbody Σ (xprog c) T).
  Hypothesis xTotal : forall c T k, In k (xprovs Σ (xprog c)) -> AllDoneProv Σ k (xbody Σ (xprog c) T).

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

  Local Notation HK' := (HK' K_eq_dec Σ xprog Kb xHK).
  Local Notation Hrank' := (Hrank' K_eq_dec Σ xprog xrank Hrank xNoSpawn).
  Local Notation Total' := (Total' K_eq_dec Σ xprog xTotal).
  Local Notation CInv := (CInv K_eq_dec Σ prog' Kb).
  Local Notation PInv := (PInv K_eq_dec Σ prog' Kb).
  Local Notation rank' := (fun x : CC => xrank (fst x)).
  Local Notation pinv_step :=
    (pinv_step K_eq_dec Σ prog' Kb HK' rank' Hrank' Total' Hwb HUI HTI HRI HCom).

  (** ** Changing the components of Inactive fibers *)

  (** [F] has the fibers of [γ], with the same lives, parents, disposal
      and base components; an installed fiber is unchanged. *)
  Definition RF (γ : State) (F : nat -> option Fiber) : Prop :=
    (forall m fm, F m = Some fm ->
       exists fm0, fibers γ m = Some fm0 /\ life fm = life fm0 /\ fparent fm = fparent fm0 /\
                   disposed fm = disposed fm0 /\ fst (fcomp fm) = fst (fcomp fm0) /\
                   (is_installed (life fm0) = true -> fm = fm0)) /\
    (forall m fm0, fibers γ m = Some fm0 -> exists fm, F m = Some fm).

  Lemma rf_installed (γ : State) F m fm0 :
    RF γ F -> fibers γ m = Some fm0 -> is_installed (life fm0) = true -> F m = Some fm0.
  Proof.
    intros [R1 R2] H0 Hi; destruct (R2 m fm0 H0) as [fm Hm].
    destruct (R1 m fm Hm) as (fm0' & H0' & _ & _ & _ & _ & E).
    rewrite H0 in H0'; injection H0' as <-; rewrite Hm, (E Hi); reflexivity.
  Qed.

  Lemma fprovs_fst (f f' : Fiber) :
    fst (fcomp f) = fst (fcomp f') -> fprovs Σ prog' f = fprovs Σ prog' f'.
  Proof. intros E; unfold fprovs, Optional.prog'; cbn [provs]; rewrite E; reflexivity. Qed.

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
      destruct (R1 m fm H) as (fm0 & H0 & _ & _ & _ & Ec & _).
      destruct (R1 m' fm' H') as (fm0' & H0' & _ & _ & _ & Ec' & _).
      rewrite (fprovs_fst _ _ Ec), (fprovs_fst _ _ Ec'); eauto.
    - intros m fm k p H I; destruct (R1 m fm H) as (fm0 & H0 & El & _); rewrite El in I; eauto.
    - intros m fm H I; destruct (R1 m fm H) as (fm0 & H0 & El & _ & _ & _ & Eq).
      rewrite El in I; rewrite (Eq I); eauto.
    - intros k b Hb; destruct (Wb k b Hb) as (fo & Ho & Io & Ko & Uo).
      exists fo; repeat split; auto; exact (rf_installed γ F _ fo R Ho Io).
    - intros m fm k p H I; destruct (R1 m fm H) as (fm0 & H0 & El & _); rewrite El in I; eauto.
    - intros m fm H; destruct (R1 m fm H) as (fm0 & H0 & El & _).
      pose proof (Wuu m fm0 H0) as U; rewrite El; exact U.
  Qed.

  Lemma rf_cinv (γ : State) F : CInv γ -> RF γ F -> CInv (with_fibers Σ γ F).
  Proof.
    intros [[W [PF PT] [U _] LB _] PI NS] R; pose proof R as [R1 R2].
    assert (NS' : NoSpawnInv Σ (with_fibers Σ γ F)).
    { intros m fm x H Hu; destruct (R1 m fm H) as (fm0 & H0 & El & _).
      rewrite El in Hu; exact (NS m fm0 x H0 Hu). }
    split; [split|..]; [exact (rf_wf γ F W R)| | | | | |exact NS'].
    - split.
      + intros m fm H; destruct (R1 m fm H) as (fm0 & H0 & El & _ & _ & _ & E).
        destruct (is_installed (life fm0)) eqn:Hi.
        * rewrite (E eq_refl); exact (PF m fm0 H0).
        * destruct (life fm0) as [z| | |] eqn:L; try discriminate.
          exact (ProvF_inactive Σ prog' _ fm z El).
      + intros m1 m2 f1 f2 k1 p1 g1 k2 p2 g2 t Hne H1 H2 I1 I2.
        destruct (R1 m1 f1 H1) as (f1' & H1' & E1 & _), (R1 m2 f2 H2) as (f2' & H2' & E2 & _).
        rewrite E1 in I1; rewrite E2 in I2; exact (PT m1 m2 f1' f2' k1 p1 g1 k2 p2 g2 t Hne H1' H2' I1 I2).
    - split; [exact U|]; intros x fx m fm Hx Hu; destruct (NS' x fx m Hx Hu).
    - intros m fm P acc w H Hl; destruct (R1 m fm H) as (fm0 & H0 & El & _ & _ & _ & E).
      rewrite El in Hl; exact (LB m fm0 P acc w H0 Hl).
    - intros x fx m fm Hx Hu; destruct (NS' x fx m Hx Hu).
    - intros m fm H; destruct (R1 m fm H) as (fm0 & H0 & El & _ & _ & _ & E).
      destruct (is_installed (life fm0)) eqn:Hi.
      + rewrite (E eq_refl); exact (PI m fm0 H0).
      + unfold PIF; rewrite El; destruct (life fm0); try discriminate; exact Logic.I.
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

  Lemma rf_pinv (γ : State) F : PInv γ -> CInv γ -> RF γ F -> PInv (with_fibers Σ γ F).
  Proof.
    intros [[SC SG SI] EP] CI R; pose proof R as [R1 R2].
    pose proof (c_ns _ _ _ _ _ CI) as NS.
    pose proof (rf_cinv γ F CI R) as CI'.
    split; [split|].
    - exact (cinv_0 _ _ _ _ _ CI').
    - intros m fm H; destruct (R1 m fm H) as (fm0 & H0 & El & _ & _ & _ & E).
      destruct (is_installed (life fm0)) eqn:Hi.
      + rewrite (E eq_refl); exact (SG m fm0 H0).
      + unfold GF, uacc; rewrite El; destruct (life fm0); try discriminate; cbn.
        split; [constructor | intros k p t g []].
    - intros k b Hb; destruct (SI k b Hb) as (s0 & L & s & Hi & [Hs HL] & Rp & E).
      exists s0, L, s; split; [exact Hi|]; split; [split; [exact Hs|]|split; [exact Rp | exact E]].
      intros a t; rewrite (HL a t); cbn [Calculus.oplog with_fibers].
      rewrite (rf_item γ F k (pid Σ b) t R); reflexivity.
    - intros m fm H; destruct (R1 m fm H) as (fm0 & H0 & El & _ & _ & _ & E).
      destruct (is_installed (life fm0)) eqn:Hi.
      + rewrite (E eq_refl); pose proof (EP m fm0 H0) as Ep.
        assert (Hcorr : forall c w acc evs, (forall x, ~ In (USpawn Σ x) acc) ->
                  Corr K_eq_dec Σ prog' γ c w acc evs ->
                  Corr K_eq_dec Σ prog' (with_fibers Σ γ F) c w acc evs).
        { intros c w acc evs Nsp Co; apply (corr_mono K_eq_dec Σ prog' γ _ c w acc evs Co);
            [intros; reflexivity | intros; reflexivity | intros x Hx; destruct (Nsp x Hx)]. }
        unfold epl in *; destruct (life fm0) as [|P acc w|acc w|] eqn:L; try exact Logic.I;
          destruct Ep as (evs & T & Co); exists evs; split; [exact T| |exact T|];
          apply Hcorr; [| exact Co | | exact Co];
          intros x Hx; apply (NS m fm0 x H0); rewrite L; exact Hx.
      + unfold epl; rewrite El; destruct (life fm0); try discriminate; exact Logic.I.
  Qed.

  (** Re-choosing presence is such a change. *)
  Lemma rf_recomp (γ : State) n f :
    fibers γ n = Some f -> is_installed (life f) = false ->
    RF γ (Calculus.fibers Σ (recomp γ n f)).
  Proof.
    intros Hn Hi; split.
    - intros m fm H; rewrite fibers_recomp in H.
      destruct (Nat.eqb_spec m n) as [->|]; [injection H as <-|].
      + exists f; repeat split; try reflexivity; [exact Hn | intros E; congruence].
      + exists fm; repeat split; auto.
    - intros m fm0 H0; rewrite fibers_recomp; destruct (Nat.eqb_spec m n); eauto.
  Qed.

  Lemma recomp_with (γ : State) n f : recomp γ n f = with_fibers Σ γ (Calculus.fibers Σ (recomp γ n f)).
  Proof. reflexivity. Qed.

  (** ** Extended runs keep [PInv] *)
  Lemma xstep_pinv (γ γ' : State) n ℓ :
    PInv γ -> CInv γ -> In ℓ (@lifecycle_labels C n) -> xstep γ ℓ = Some γ' -> PInv γ'.
  Proof.
    intros P I Hin H.
    destruct (xstep_core K_eq_dec Σ xprog γ γ' ℓ H) as [St|[(m & f & _ & Hm & Hl & St)|(m & St)]].
    - pose proof (@xlab_lifecycle K C n ℓ Hin) as Hlc.
      exact (pinv_step γ γ' _ (lifecycle_not_react _ Hlc) P St).
    - assert (Hi : is_installed (life f) = false) by (rewrite Hl; reflexivity).
      pose proof (rf_pinv γ _ P I (rf_recomp γ m f Hm Hi)) as Pr; rewrite <- recomp_with in Pr.
      assert (NR : forall a b, @LBegin CC m <> OReact a b) by (intros a b E; discriminate E).
      exact (pinv_step _ γ' _ NR Pr St).
    - assert (NR : forall a b, @ORestart CC m <> OReact a b) by (intros a b E; discriminate E).
      exact (pinv_step γ γ' _ NR P St).
  Qed.

  Lemma xlrun_pinv (γ0 γ : State) :
    PInv γ0 -> CInv γ0 -> XLRun K_eq_dec Σ xprog γ0 γ -> PInv γ.
  Proof.
    intros P0 I0 R; induction R as [γ|γ n ℓ γ1 γ2 Hin Hs R IH]; [exact P0|].
    pose proof (xstep_pinv γ γ1 n ℓ P0 I0 Hin Hs) as P1.
    assert (R1 : XLRun K_eq_dec Σ xprog γ γ1) by (eapply xlr_cons; [exact Hin | exact Hs | constructor]).
    destruct (xlrun_cinv K_eq_dec Σ xprog Kb xHK xrank Hrank xNoSpawn xTotal γ γ1 I0 R1) as [I1 _].
    exact (IH P1 I1).
  Qed.

  (** ** Normalising a final state *)
  Definition nfib (γ : State) (f : Fiber) : Fiber :=
    if is_installed (life f) then f
    else mkFiber Σ (fst (fcomp f), present γ (fst (fcomp f))) (fparent f) (disposed f) (life f).

  Definition norm (γ : State) : State :=
    with_fibers Σ γ (fun m => option_map (nfib γ) (fibers γ m)).

  Lemma rf_norm (γ : State) : RF γ (fun m => option_map (nfib γ) (fibers γ m)).
  Proof.
    split.
    - intros m fm H; destruct (fibers γ m) as [fm0|] eqn:H0; [|discriminate].
      cbn in H; injection H as <-; exists fm0; unfold nfib.
      destruct (is_installed (life fm0)) eqn:Hi.
      + split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
        split; [reflexivity|]; split; [reflexivity|]; intros _; reflexivity.
      + split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
        split; [reflexivity|]; split; [reflexivity|]; intros E; discriminate E.
    - intros m fm0 H0; rewrite H0; cbn; eauto.
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

  Lemma target_norm (γ : State) n f :
    fibers γ n = Some f ->
    target Σ prog' (norm γ) n =
    if disposed f then None else resolve Σ γ (deps Σ (prog' (fcomp (nfib γ f)))).
  Proof.
    intros Hn; unfold Calculus.target, norm; cbn [Calculus.fibers with_fibers]; rewrite Hn; cbn.
    assert (Ed : disposed (nfib γ f) = disposed f) by (unfold nfib; destruct (is_installed (life f)); reflexivity).
    rewrite Ed; destruct (disposed f); [reflexivity|].
    apply resolve_ext; intros k; exact (visible_rf γ _ k (rf_norm γ)).
  Qed.

  Lemma final_norm (γ : State) :
    PInv γ -> CInv γ -> xquiet K_eq_dec Σ xprog γ -> NoFailed Σ γ ->
    Final K_eq_dec Σ prog' Kb (norm γ).
  Proof.
    intros P I Q NF.
    destruct (final_settled K_eq_dec Σ C_eq_dec xprog Kb xrank Rb Hrank Hbnd γ I Q) as [St _].
    split; [exact (rf_pinv γ _ P I (rf_norm γ))|]; split.
    - intros n fm H; unfold norm in H; cbn [Calculus.fibers with_fibers] in H.
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate]; cbn in H; injection H as <-.
      pose proof (St n f Hn) as Sf; unfold settled_fiber in *.
      assert (El : life (nfib γ f) = life f) by (unfold nfib; destruct (is_installed (life f)); reflexivity).
      assert (Ed : disposed (nfib γ f) = disposed f) by (unfold nfib; destruct (is_installed (life f)); reflexivity).
      rewrite El, Ed, (target_norm γ n f Hn).
      destruct (life f) as [[z|]|P0 acc w|acc w|acc w z] eqn:Hl; try exact Sf.
      + (* Inactive None: X-Begin does not apply *)
        destruct Sf as [Hd _]; split; [exact Hd|]; rewrite Hd.
        unfold nfib; rewrite Hl; cbn [is_installed Calculus.comp].
        pose proof (Q n (LBegin n) ltac:(cbn; auto)) as Hq.
        cbn [Optional.xstep] in Hq; rewrite Hn, Hl in Hq; cbn [Calculus.step] in Hq.
        rewrite fibers_recomp, Nat.eqb_refl in Hq; cbn [Calculus.life] in Hq; rewrite Hl in Hq.
        unfold Calculus.target in Hq; rewrite fibers_recomp, Nat.eqb_refl in Hq.
        cbn [Calculus.disposed Calculus.comp] in Hq; rewrite Hd in Hq.
        rewrite (resolve_ext Σ _ γ _ (fun k => visible_recomp Σ xprog γ n f k Hn)) in Hq.
        destruct (resolve Σ γ _); [discriminate Hq | reflexivity].
      + (* Active: unchanged *)
        unfold Calculus.target in Sf; rewrite Hn in Sf.
        unfold nfib; rewrite Hl; cbn [is_installed].
        exact Sf.
    - intros n fm e H; unfold norm in H; cbn [Calculus.fibers with_fibers] in H.
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate]; cbn in H; injection H as <-.
      assert (El : life (nfib γ f) = life f) by (unfold nfib; destruct (is_installed (life f)); reflexivity).
      rewrite El; exact (NF n f e Hn).
  Qed.

  (** ** Two final states with equal components agree on service states *)
  Lemma final_states_agree (γ1 γ2 : State) :
    Final K_eq_dec Σ prog' Kb γ1 -> Final K_eq_dec Σ prog' Kb γ2 ->
    (forall n, (exists f, fibers γ1 n = Some f) <-> (exists f, fibers γ2 n = Some f)) ->
    (forall n f1 f2, fibers γ1 n = Some f1 -> fibers γ2 n = Some f2 ->
       fcomp f1 = fcomp f2 /\ is_active (life f1) = is_active (life f2)) ->
    (forall k, option_map owner (binds γ1 k) = option_map owner (binds γ2 k)) ->
    forall k b1 b2, binds γ1 k = Some b1 -> binds γ2 k = Some b2 -> bst b1 ≃ bst b2.
  Proof.
    intros F1 F2 Hex Hcomp Hown k b1 b2 Hb1 Hb2.
    pose proof (final_evs K_eq_dec Σ prog' Kb rank' Hrank' Hwb γ1 γ2 F1 F2 Hcomp Hown) as Hev.
    pose proof (proj1 F1) as P1; pose proof (proj1 F2) as P2.
    pose proof (sinv_wf K_eq_dec Σ prog' Kb γ1 (p_s _ _ _ _ _ P1)) as W1.
    pose proof (sinv_wf K_eq_dec Σ prog' Kb γ2 (p_s _ _ _ _ _ P2)) as W2.
    destruct (s_inv _ _ _ _ _ (p_s _ _ _ _ _ P1) k b1 Hb1) as (s01 & L1 & s1 & Hi1 & PL1 & Rp1 & E1).
    destruct (s_inv _ _ _ _ _ (p_s _ _ _ _ _ P2) k b2 Hb2) as (s02 & L2 & s2 & Hi2 & PL2 & Rp2 & E2).
    assert (Ho : owner b1 = owner b2) by (pose proof (Hown k) as E; rewrite Hb1, Hb2 in E; injection E; auto).
    destruct (wf_bind K_eq_dec Σ prog' γ1 W1 k b1 Hb1) as (fo1 & Hfo1 & _ & _ & Hup1).
    destruct (wf_bind K_eq_dec Σ prog' γ2 W2 k b2 Hb2) as (fo2 & Hfo2 & _ & _ & Hup2).
    rewrite <- Ho in Hfo2.
    destruct (final_fiber K_eq_dec Σ prog' Kb γ1 _ fo1 F1 Hfo1) as [E|(acc1' & w1' & evs1' & L1' & T1' & C1')];
      [rewrite E in Hup1; destruct Hup1|].
    destruct (final_fiber K_eq_dec Σ prog' Kb γ2 _ fo2 F2 Hfo2) as [E|(acc2' & w2' & evs2' & L2' & T2' & C2')];
      [rewrite E in Hup2; destruct Hup2|].
    pose proof (Hev _ fo1 fo2 acc1' w1' acc2' w2' evs1' evs2' Hfo1 Hfo2 L1' L2' T1' C1' T2' C2') as Eev.
    pose proof (wf_uprov_unique K_eq_dec Σ prog' γ1 W1 _ fo1 Hfo1) as U1; rewrite L1' in U1, Hup1.
    pose proof (wf_uprov_unique K_eq_dec Σ prog' γ2 W2 _ fo2 Hfo2) as U2; rewrite L2' in U2, Hup2.
    destruct (corr_find K_eq_dec Σ prog' γ1 _ w1' acc1' evs1' k (pid Σ b1) C1' U1 Hup1) as (s1' & Hi1' & Hf1).
    destruct (corr_find K_eq_dec Σ prog' γ2 _ w2' acc2' evs2' k (pid Σ b2) C2' U2 Hup2) as (s2' & Hi2' & Hf2).
    assert (s02 = s01) by (rewrite Eev in Hf1; congruence); subst s02.
    set (B := Calculus.next Σ γ1 + Calculus.next Σ γ2).
    destruct (final_blocks K_eq_dec Σ prog' Kb Hwb HCom γ1 k b1 L1 B s01 s1 F1 ltac:(unfold B; lia) Hb1 PL1 Rp1)
      as (x1 & X1 & Ex1).
    destruct (final_blocks K_eq_dec Σ prog' Kb Hwb HCom γ2 k b2 L2 B s01 s2 F2 ltac:(unfold B; lia) Hb2 PL2 Rp2)
      as (x2 & X2 & Ex2).
    assert (EM : map fst (concat (map (blockAt K_eq_dec Σ γ1 k) (seq 0 B))) =
                 map fst (concat (map (blockAt K_eq_dec Σ γ2 k) (seq 0 B)))).
    { rewrite !concat_map, !map_map; f_equal; apply map_ext_in; intros n _.
      unfold blockAt; rewrite !map_rev; f_equal; unfold itemsAt.
      destruct (fibers γ1 n) as [f1|] eqn:H1; destruct (fibers γ2 n) as [f2|] eqn:H2.
      - pose proof (Hcomp n f1 f2 H1 H2) as [_ Ha].
        destruct (final_fiber K_eq_dec Σ prog' Kb γ1 n f1 F1 H1) as [E1'|(acc1 & w1 & evs1 & L1'' & T1 & C1)];
          destruct (final_fiber K_eq_dec Σ prog' Kb γ2 n f2 F2 H2) as [E2'|(acc2 & w2 & evs2 & L2'' & T2 & C2)].
        + unfold uacc; rewrite E1', E2'; reflexivity.
        + rewrite E1', L2'' in Ha; discriminate.
        + rewrite L1'', E2' in Ha; discriminate.
        + unfold uacc; rewrite L1'', L2''; cbn [Calculus.acc_of].
          rewrite (corr_ops K_eq_dec Σ prog' γ1 _ _ _ _ k C1), (corr_ops K_eq_dec Σ prog' γ2 _ _ _ _ k C2); f_equal.
          exact (Hev n f1 f2 acc1 w1 acc2 w2 evs1 evs2 H1 H2 L1'' L2'' T1 C1 T2 C2).
      - destruct (proj1 (Hex n) (ex_intro _ f1 H1)) as [f2 H2']; congruence.
      - destruct (proj2 (Hex n) (ex_intro _ f2 H2)) as [f1 H1']; congruence.
      - reflexivity. }
    destruct (replay_tokens Hwb HTI _ _ s01 x1 EM X1 s01 (reflexivity _)) as (x3 & X3 & E13).
    pose proof (replay_det _ s01 x3 x2 X3 X2) as E32.
    transitivity s1; [exact E1|]; transitivity x1; [exact Ex1|]; transitivity x3; [exact E13|].
    transitivity x2; [exact E32|]; transitivity s2; symmetry; assumption.
  Qed.

  (** ** State confluence *)
  Theorem xstate_confluence (γ0 γ1 γ2 : State) :
    PInv γ0 -> NoSpawnInv Σ γ0 ->
    XLRun K_eq_dec Σ xprog γ0 γ1 -> XLRun K_eq_dec Σ xprog γ0 γ2 ->
    xquiet K_eq_dec Σ xprog γ1 -> xquiet K_eq_dec Σ xprog γ2 ->
    NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    forall k b1 b2, binds γ1 k = Some b1 -> binds γ2 k = Some b2 -> bst b1 ≃ bst b2.
  Proof.
    intros P0 NS0 R1 R2 Q1 Q2 NF1 NF2.
    pose proof (p_s _ _ _ _ _ P0) as SI0.
    assert (I0 : CInv γ0) by (destruct (s_c _ _ _ _ _ SI0) as [T PI]; split; assumption).
    destruct (xlrun_cinv K_eq_dec Σ xprog Kb xHK xrank Hrank xNoSpawn xTotal γ0 γ1 I0 R1) as [I1 _].
    destruct (xlrun_cinv K_eq_dec Σ xprog Kb xHK xrank Hrank xNoSpawn xTotal γ0 γ2 I0 R2) as [I2 _].
    pose proof (xlrun_pinv γ0 γ1 P0 I0 R1) as P1.
    pose proof (xlrun_pinv γ0 γ2 P0 I0 R2) as P2.
    destruct (xcontrol_confluence K_eq_dec Σ C_eq_dec xprog Kb xHK xrank Rb Hrank Hbnd xNoSpawn xTotal
                γ0 γ1 γ2 I0 R1 R2 Q1 Q2 NF1 NF2) as (Hex & Hcomp & Hown & Hpr).
    apply (final_states_agree (norm γ1) (norm γ2) (final_norm γ1 P1 I1 Q1 NF1) (final_norm γ2 P2 I2 Q2 NF2)).
    - intros n; unfold norm; cbn [Calculus.fibers with_fibers].
      split; intros [f H]; destruct (fibers _ n) as [f'|] eqn:E; try discriminate;
        [destruct (proj1 (Hex n) (ex_intro _ f' E)) as [g Hg]
        |destruct (proj2 (Hex n) (ex_intro _ f' E)) as [g Hg]]; rewrite Hg; cbn; eauto.
    - intros n f1 f2; unfold norm; cbn [Calculus.fibers with_fibers].
      destruct (fibers γ1 n) as [g1|] eqn:H1, (fibers γ2 n) as [g2|] eqn:H2; try discriminate;
        cbn; intros [= <-] [= <-].
      destruct (Hcomp n g1 g2 H1 H2) as (Ec & Ea & Ef).
      destruct (final_settled K_eq_dec Σ C_eq_dec xprog Kb xrank Rb Hrank Hbnd γ1 I1 Q1) as [St1 _].
      destruct (final_settled K_eq_dec Σ C_eq_dec xprog Kb xrank Rb Hrank Hbnd γ2 I2 Q2) as [St2 _].
      destruct (settled_shape Σ prog' γ1 n g1 St1 NF1 H1) as [_ [[L1 _]|(a1 & v1 & L1 & _)]];
        destruct (settled_shape Σ prog' γ2 n g2 St2 NF2 H2) as [_ [[L2 _]|(a2 & v2 & L2 & _)]];
        unfold nfib; rewrite L1, L2; cbn [is_installed].
      + split; [cbn; rewrite Ec, Hpr; reflexivity | reflexivity].
      + exfalso; rewrite L1, L2 in Ea; discriminate Ea.
      + exfalso; rewrite L1, L2 in Ea; discriminate Ea.
      + split; [exact (Ef ltac:(rewrite L1; reflexivity)) | rewrite L1, L2; reflexivity].
    - intros k; exact (Hown k).
  Qed.
End OptState.
