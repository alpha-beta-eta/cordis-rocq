(** * Confluence with failures, layer 1: control states (errors/DESIGN.md, section 3)

    The core's control confluence ([Confluence.control_confluence]) holds
    for runs that end with no failed fiber. With failures scoped to their
    view, the proof splits in two:

    - layer 1 (this file): two quiet runs from the same state that end with
      the same failed fibers have the same fibers, the same components, the
      same Active fibers and the same provider for every key;
    - layer 2 (to do): the failed fibers are the same, because whether a
      load fails is decided by its ideal trajectory (DESIGN.md section 3).

    Layer 1 is the core's proof with one change: a fiber is Active iff it
    has not failed and each key it declares is provided by an Active fiber
    ([vactive_iff]); the fixpoint has one solution for any fixed set of
    failed fibers ([fix_unique_guard]). Failed fibers are settled the way
    the core's settled states allow ([vsettled_shape]). [Total] already
    lets a program fail on some paths: it only asks paths that reach [Done]
    to provide.

    As in the core, layer 1 is stated for components that do not spawn.

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Progress Recovery
  Termination Confluence.
From CordisErr Require Import ViewFail.
Import ListNotations.

Section Classify.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Variable Kb : nat.
  Hypothesis HK : forall c, Bounded Σ Kb (body Σ (prog c)).
  Variable rank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', Above Σ prog c c' -> rank c < rank c'.
  Hypothesis Hbnd : forall c, rank c <= Rb.
  Hypothesis NoSpawn : forall c c', ~ SpawnIn Σ c' (body Σ (prog c)).
  Hypothesis Total : forall c k, In k (provs Σ (prog c)) -> AllDoneProv Σ k (body Σ (prog c)).

  Local Notation State := (@State K Σ C).
  Local Notation Fiber := (@Fiber K Σ C).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation target := (Calculus.target Σ prog).
  Local Notation target_is := (target_is K_eq_dec Σ prog).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation cdeps c := (deps Σ (prog c)).
  Local Notation cprovs c := (provs Σ (prog c)).
  Local Notation CInv := (CInv K_eq_dec Σ prog Kb).
  Local Notation CInv0 := (CInv0 K_eq_dec Σ prog Kb).
  Local Notation VState := (@VState K Σ C).
  Local Notation vstep := (vstep K_eq_dec Σ prog).
  Local Notation vcore := (ViewFail.vcore Σ).
  Local Notation fview := (ViewFail.fview Σ).
  Local Notation VInv := (VInv Σ).

  (** ** Lifecycle runs with [VClear] *)
  Definition vlife (ℓ : @VLabel C) : Prop :=
    (exists n ℓ0, In ℓ0 (lifecycle_labels n) /\ ℓ = VCore ℓ0) \/ (exists n, ℓ = VClear n).

  Inductive VLRun : VState -> VState -> Prop :=
  | vlr_nil vs : VLRun vs vs
  | vlr_cons vs ℓ vs1 vs2 : vlife ℓ -> vstep vs ℓ = Some vs1 -> VLRun vs1 vs2 -> VLRun vs vs2.

  Lemma vlife_core_label ℓ : vlife ℓ -> forall n i, vlabel ℓ <> OReact n i.
  Proof.
    intros [(m & ℓ0 & Hin & ->)|(m & ->)] n i; cbn [vlabel]; [|discriminate].
    exact (lifecycle_not_react ℓ0 (ex_intro _ m Hin) n i).
  Qed.

  Lemma vlstep_static (vs vs' : VState) ℓ :
    CInv (vcore vs) -> vlife ℓ -> vstep vs ℓ = Some vs' -> Static Σ (vcore vs) (vcore vs').
  Proof.
    intros I [(n & ℓ0 & Hin & ->)|(n & ->)] H.
    - exact (lstep_static K_eq_dec Σ prog Kb rank Hrank NoSpawn _ _ ℓ0 I (ex_intro _ n Hin)
               (vstep_core K_eq_dec Σ prog vs vs' _ H)).
    - pose proof (vstep_core K_eq_dec Σ prog vs vs' _ H) as Hs; cbn [vlabel step] in Hs.
      destruct (fibers Σ (vcore vs) n) as [f|] eqn:Hn; [|discriminate].
      destruct (life Σ f) as [[e|]| | |]; try discriminate; injection Hs as Hs.
      split.
      + intros m fm Hm; rewrite <- Hs, fibers_set_life in Hm.
        destruct (Nat.eqb_spec m n) as [->|].
        * injection Hm as <-; exists f; auto.
        * exists fm; auto.
      + intros m f0 Hm _; rewrite <- Hs, fibers_set_life.
        destruct (Nat.eqb_spec m n); [eauto | rewrite Hm; eauto].
  Qed.

  Lemma vlrun_static (vs0 vs : VState) :
    CInv (vcore vs0) -> VInv vs0 -> VLRun vs0 vs ->
    CInv (vcore vs) /\ VInv vs /\ Static Σ (vcore vs0) (vcore vs).
  Proof.
    intros I0 V0 R; induction R as [vs|vs ℓ vs1 vs2 Hl Hs R IH].
    - split; [exact I0|]; split; [exact V0|]; split.
      + intros m fm H; exists fm; auto.
      + intros m f0 H _; eauto.
    - destruct (vlstep_static vs vs1 ℓ I0 Hl Hs) as [S1 S2].
      pose proof (vstep_core K_eq_dec Σ prog vs vs1 _ Hs) as Hc.
      destruct (IH (cinv_step K_eq_dec Σ prog Kb HK NoSpawn Total _ _ _ (vlife_core_label ℓ Hl) I0 Hc)
                   (vinv_step K_eq_dec Σ prog vs vs1 ℓ V0 Hs)) as (I2 & V2 & T1 & T2).
      split; [exact I2|]; split; [exact V2|]; split.
      + intros m fm H; destruct (T1 m fm H) as (f1 & H1 & Hc1 & Hd1).
        destruct (S1 m f1 H1) as (f0 & H0 & Hc0 & Hd0).
        exists f0; split; [exact H0 | split; congruence].
      + intros m f0 H0 Hd; destruct (S2 m f0 H0 Hd) as [f1 H1].
        destruct (S1 m f1 H1) as (f0' & H0' & _ & Hd1).
        rewrite H0 in H0'; injection H0' as <-.
        apply (T2 m f1 H1); congruence.
  Qed.

  (** ** Quiet states *)
  Definition Failed (γ : State) (n : nat) : Prop :=
    exists f e, fibers Σ γ n = Some f /\ life Σ f = Inactive Σ (Some e).

  Lemma vquiet_quiet (vs : VState) : vquiet K_eq_dec Σ prog vs -> quiet K_eq_dec Σ prog (vcore vs).
  Proof.
    intros [QL _] n ℓ Hin.
    destruct (step (vcore vs) ℓ) as [γ'|] eqn:Hs; [|reflexivity].
    destruct (vstep_lifecycle_back K_eq_dec Σ prog vs n ℓ γ' Hin Hs) as [vs' Hv].
    rewrite (QL n ℓ Hin) in Hv; discriminate.
  Qed.

  Lemma vquiet_settled (vs : VState) :
    CInv (vcore vs) -> vquiet K_eq_dec Σ prog vs -> settled Σ prog (vcore vs).
  Proof.
    intros I Q.
    apply (quiet_settled K_eq_dec Σ prog (Hwf Σ prog rank Rb Hrank Hbnd) (vcore vs));
      [exact (t_wf K_eq_dec Σ prog Kb _ (c_t K_eq_dec Σ prog Kb _ I))
      | exact (t_inv2 K_eq_dec Σ prog Kb _ (c_t K_eq_dec Σ prog Kb _ I)) | exact (vquiet_quiet vs Q)].
  Qed.

  (** A settled fiber is Inactive without a target, Active at its target, or
      failed; never retired. *)
  Lemma vsettled_shape (γ : State) n f :
    settled Σ prog γ -> fibers Σ γ n = Some f ->
    disposed Σ f = false /\
    ((life Σ f = Inactive Σ None /\ target γ n = None) \/
     (exists acc w, life Σ f = Active Σ acc w /\ target γ n = Some w) \/
     (exists e, life Σ f = Inactive Σ (Some e))).
  Proof.
    intros St Hn; pose proof (St n f Hn) as Sf; unfold settled_fiber in Sf.
    destruct (life Σ f) as [[e|]|P acc w|acc w|acc w z] eqn:Hl; try contradiction.
    - split; [exact Sf | right; right; eauto].
    - destruct Sf as [Hd Ht]; auto.
    - split; [|right; left; eauto].
      destruct (disposed Σ f) eqn:Hd; [|reflexivity].
      unfold target in Sf; rewrite Hn, Hd in Sf; discriminate.
  Qed.

  (** At a settled state, a fiber that has not failed is Active iff every key
      it declares is provided by an Active fiber. *)
  Lemma vactive_iff (γ : State) n f :
    CInv0 γ -> settled Σ prog γ -> fibers Σ γ n = Some f -> ~ Failed γ n ->
    (is_active Σ (life Σ f) = true <->
     forall k, In k (cdeps (fcomp f)) ->
       exists m fm, fibers Σ γ m = Some fm /\ is_active Σ (life Σ fm) = true /\ In k (cprovs (fcomp fm))).
  Proof.
    intros CI St Hn NF.
    pose proof (t_wf K_eq_dec Σ prog Kb γ (c0_t K_eq_dec Σ prog Kb _ CI)) as W.
    destruct (vsettled_shape γ n f St Hn) as [Hd [[Hl Ht]|[(acc & w & Hl & Ht)|(e & Hl)]]].
    - split; [rewrite Hl; discriminate|].
      intros Hall; exfalso.
      assert (Hv : forall k, In k (cdeps (fcomp f)) -> exists p, visible Σ γ k = Some p).
      { intros k Hk; destruct (Hall k Hk) as (m & fm & Hm & Ha & Hp).
        destruct (active_binds K_eq_dec Σ prog Kb γ m fm k CI Hm Ha Hp) as (b & Hb & Ho).
        exists (pid Σ b); unfold visible; rewrite Hb, Ho, Hm, Ha; reflexivity. }
      destruct (resolve_some Σ γ _ Hv) as [w Hw].
      unfold target in Ht; rewrite Hn, Hd in Ht; congruence.
    - split; [intros _|rewrite Hl; reflexivity].
      intros k Hk.
      pose proof (resolve_spec Σ γ _ w (target_spec Σ prog γ n f w Hn Ht)) as [Hkeys Hvis].
      assert (Hin : exists p, In (k, p) w).
      { unfold fdeps in Hkeys; rewrite <- Hkeys in Hk.
        apply in_map_iff in Hk as ([k' p] & E & Hin); cbn in E; subst k'; eauto. }
      destruct Hin as [p Hin].
      destruct (visible_spec Σ γ k p (Hvis k p Hin)) as (b & fo & Hb & _ & Ho & Ha).
      destruct (wf_bind K_eq_dec Σ prog γ W k b Hb) as (fo' & Ho' & _ & Hko & _).
      rewrite Ho in Ho'; injection Ho' as <-.
      exists (owner Σ b), fo; repeat split; auto.
      exact (kmem_In K_eq_dec k _ Hko).
    - exfalso; apply NF; exists f, e; auto.
  Qed.

  Lemma vowner_iff (γ : State) k m :
    CInv0 γ -> settled Σ prog γ ->
    (option_map (owner Σ) (binds Σ γ k) = Some m <->
     exists fm, fibers Σ γ m = Some fm /\ is_active Σ (life Σ fm) = true /\ In k (cprovs (fcomp fm))).
  Proof.
    intros CI St.
    pose proof (t_wf K_eq_dec Σ prog Kb γ (c0_t K_eq_dec Σ prog Kb _ CI)) as W.
    split.
    - destruct (binds Σ γ k) as [b|] eqn:Hb; cbn; [intros [= <-] | discriminate].
      destruct (wf_bind K_eq_dec Σ prog γ W k b Hb) as (fo & Ho & Hio & Hko & _).
      exists fo; split; [exact Ho|]; split; [|exact (kmem_In K_eq_dec k _ Hko)].
      destruct (vsettled_shape γ _ fo St Ho) as [_ [[Hl _]|[(acc & w & Hl & _)|(e & Hl)]]];
        rewrite Hl in *; [discriminate | reflexivity | discriminate].
    - intros (fm & Hm & Ha & Hk).
      destruct (active_binds K_eq_dec Σ prog Kb γ m fm k CI Hm Ha Hk) as (b & Hb & Ho).
      rewrite Hb; cbn; congruence.
  Qed.

  (** ** The fixpoint, guarded by a fixed set, has one solution *)
  Lemma fix_unique_guard (D : nat -> Prop) (Cm : nat -> C -> Prop) (G S1 S2 : nat -> Prop) :
    (forall n c, D n -> Cm n c ->
       (S1 n <-> G n /\ forall k, In k (cdeps c) ->
          exists m c', D m /\ Cm m c' /\ S1 m /\ In k (cprovs c'))) ->
    (forall n c, D n -> Cm n c ->
       (S2 n <-> G n /\ forall k, In k (cdeps c) ->
          exists m c', D m /\ Cm m c' /\ S2 m /\ In k (cprovs c'))) ->
    forall n c, D n -> Cm n c -> (S1 n <-> S2 n).
  Proof.
    intros H1 H2.
    assert (Gr : forall r n c, rank c < r -> D n -> Cm n c -> (S1 n <-> S2 n)).
    { induction r as [|r IH]; intros n c Hr Hn Hc; [lia|].
      rewrite (H1 n c Hn Hc), (H2 n c Hn Hc).
      split; intros [Hg Hall]; split; [exact Hg| |exact Hg|]; intros k Hk;
        destruct (Hall k Hk) as (m & c' & Hm & Hc' & HS & Hp);
        exists m, c'; (split; [exact Hm | split; [exact Hc'|]]);
        (assert (Hlt : rank c' < rank c) by (apply Hrank; left; exists k; auto));
        (split; [|exact Hp]); apply (IH m c' ltac:(lia) Hm Hc'); exact HS. }
    intros n c; exact (Gr (S (rank c)) n c (Nat.lt_succ_diag_r _)).
  Qed.

  (** ** Control confluence relative to the failed fibers *)
  Theorem vcontrol_confluence (vs0 vs1 vs2 : VState) :
    CInv (vcore vs0) -> VInv vs0 -> VLRun vs0 vs1 -> VLRun vs0 vs2 ->
    vquiet K_eq_dec Σ prog vs1 -> vquiet K_eq_dec Σ prog vs2 ->
    (forall n, Failed (vcore vs1) n <-> Failed (vcore vs2) n) ->
    (forall n, (exists f, fibers Σ (vcore vs1) n = Some f) <-> (exists f, fibers Σ (vcore vs2) n = Some f)) /\
    (forall n f1 f2, fibers Σ (vcore vs1) n = Some f1 -> fibers Σ (vcore vs2) n = Some f2 ->
       fcomp f1 = fcomp f2 /\ is_active Σ (life Σ f1) = is_active Σ (life Σ f2)) /\
    (forall k, option_map (owner Σ) (binds Σ (vcore vs1) k) =
               option_map (owner Σ) (binds Σ (vcore vs2) k)).
  Proof.
    intros I0 V0 R1 R2 Q1 Q2 FF.
    destruct (vlrun_static vs0 vs1 I0 V0 R1) as (C1 & _ & T1 & U1).
    destruct (vlrun_static vs0 vs2 I0 V0 R2) as (C2 & _ & T2 & U2).
    set (γ0 := vcore vs0) in *; set (γ1 := vcore vs1) in *; set (γ2 := vcore vs2) in *.
    pose proof (vquiet_settled vs1 C1 Q1) as St1.
    pose proof (vquiet_settled vs2 C2 Q2) as St2.
    fold γ1 in St1; fold γ2 in St2.
    set (D := fun n => exists f0, fibers Σ γ0 n = Some f0 /\ disposed Σ f0 = false).
    set (Cm := fun n c => exists f0, fibers Σ γ0 n = Some f0 /\ fcomp f0 = c).
    set (G := fun n => ~ Failed γ1 n).
    assert (Pres : forall γ, Static Σ γ0 γ -> settled Σ prog γ ->
              forall n, (exists f, fibers Σ γ n = Some f) <-> D n).
    { intros γ [Ta Ub] St n; split.
      - intros [f Hf]; destruct (Ta n f Hf) as (f0 & H0 & _ & Hd).
        exists f0; split; [exact H0|].
        rewrite <- Hd; exact (proj1 (vsettled_shape γ n f St Hf)).
      - intros (f0 & H0 & Hd); exact (Ub n f0 H0 Hd). }
    assert (Comp : forall γ, Static Σ γ0 γ -> forall n f c, fibers Σ γ n = Some f -> Cm n c ->
              fcomp f = c).
    { intros γ [Ta _] n f c Hf (f0 & H0 & Hc).
      destruct (Ta n f Hf) as (f0' & H0' & Hc' & _); congruence. }
    set (S1 := fun n => exists f, fibers Σ γ1 n = Some f /\ is_active Σ (life Σ f) = true).
    set (S2 := fun n => exists f, fibers Σ γ2 n = Some f /\ is_active Σ (life Σ f) = true).
    assert (Fix : forall γ (S : nat -> Prop), CInv γ -> Static Σ γ0 γ -> settled Σ prog γ ->
              (forall n, Failed γ n <-> Failed γ1 n) ->
              (forall n, S n <-> exists f, fibers Σ γ n = Some f /\ is_active Σ (life Σ f) = true) ->
              forall n c, D n -> Cm n c ->
                (S n <-> G n /\ forall k, In k (cdeps c) ->
                   exists m c', D m /\ Cm m c' /\ S m /\ In k (cprovs c'))).
    { intros γ S CI TS St HF HS n c Hn Hc.
      destruct (proj2 (Pres γ TS St n) Hn) as [f Hf].
      pose proof (Comp γ TS n f c Hf Hc) as Efc.
      rewrite HS; split.
      - intros (f' & Hf' & Ha); rewrite Hf in Hf'; injection Hf' as <-.
        assert (NF : ~ Failed γ n).
        { intros (f' & e & Hf' & Hl); rewrite Hf in Hf'; injection Hf' as <-; rewrite Hl in Ha; discriminate. }
        split; [intros Hfl; apply NF, HF, Hfl|].
        intros k Hk; rewrite <- Efc in Hk.
        destruct (proj1 (vactive_iff γ n f (cinv_0 K_eq_dec Σ prog Kb _ CI) St Hf NF) Ha k Hk)
          as (m & fm & Hm & Ham & Hp).
        assert (Dm : D m) by (apply (Pres γ TS St m); eauto).
        destruct Dm as (f0 & H0 & Hd0).
        exists m, (fcomp f0); split; [exists f0; auto|]; split; [exists f0; auto|].
        split; [apply HS; eauto|].
        rewrite <- (Comp γ TS m fm (fcomp f0) Hm (ex_intro _ f0 (conj H0 eq_refl))); exact Hp.
      - intros [Hg Hall]; exists f; split; [exact Hf|].
        assert (NF : ~ Failed γ n) by (intros Hfl; apply Hg, HF, Hfl).
        apply (proj2 (vactive_iff γ n f (cinv_0 K_eq_dec Σ prog Kb _ CI) St Hf NF)).
        intros k Hk; rewrite Efc in Hk.
        destruct (Hall k Hk) as (m & c' & Hm & Hc' & HSm & Hp).
        apply HS in HSm; destruct HSm as (fm & Hfm & Ha).
        exists m, fm; repeat split; auto.
        rewrite (Comp γ TS m fm c' Hfm Hc'); exact Hp. }
    assert (Same : forall n c, D n -> Cm n c -> (S1 n <-> S2 n)).
    { apply (fix_unique_guard D Cm G).
      - apply (Fix γ1 S1 C1 (conj T1 U1) St1); intros; reflexivity.
      - apply (Fix γ2 S2 C2 (conj T2 U2) St2); [intros n; symmetry; apply FF | intros; reflexivity]. }
    assert (Same' : forall n, D n -> (S1 n <-> S2 n)).
    { intros n Hn; destruct Hn as (f0 & H0 & Hd0).
      apply (Same n (fcomp f0)); [exists f0; auto | exists f0; auto]. }
    split; [|split].
    - intros n; rewrite (Pres γ1 (conj T1 U1) St1 n), (Pres γ2 (conj T2 U2) St2 n).
      reflexivity.
    - intros n f1 f2 H1 H2.
      assert (Dn : D n) by (apply (Pres γ1 (conj T1 U1) St1); eauto).
      destruct (T1 n f1 H1) as (f0 & H0 & Hc1 & _).
      destruct (T2 n f2 H2) as (f0' & H0' & Hc2 & _).
      rewrite H0 in H0'; injection H0' as <-.
      split; [congruence|].
      pose proof (Same' n Dn) as E; unfold S1, S2 in E.
      destruct (is_active Σ (life Σ f1)) eqn:A1, (is_active Σ (life Σ f2)) eqn:A2; try reflexivity.
      + exfalso; destruct (proj1 E (ex_intro _ f1 (conj H1 A1))) as (f2' & H2' & A2').
        rewrite H2 in H2'; injection H2' as <-; congruence.
      + exfalso; destruct (proj2 E (ex_intro _ f2 (conj H2 A2))) as (f1' & H1' & A1').
        rewrite H1 in H1'; injection H1' as <-; congruence.
    - intros k.
      assert (Own : forall m, option_map (owner Σ) (binds Σ γ1 k) = Some m <->
                              option_map (owner Σ) (binds Σ γ2 k) = Some m).
      { intros m.
        rewrite (vowner_iff γ1 k m (cinv_0 K_eq_dec Σ prog Kb _ C1) St1),
                (vowner_iff γ2 k m (cinv_0 K_eq_dec Σ prog Kb _ C2) St2).
        split.
        - intros (fm & Hm & Ha & Hp).
          assert (Dm : D m) by (apply (Pres γ1 (conj T1 U1) St1); eauto).
          destruct (proj1 (Same' m Dm) (ex_intro _ fm (conj Hm Ha))) as (fm2 & Hm2 & Ha2).
          exists fm2; repeat split; auto.
          destruct (T1 m fm Hm) as (f0 & H0 & Hc1 & _).
          destruct (T2 m fm2 Hm2) as (f0' & H0' & Hc2 & _).
          rewrite H0 in H0'; injection H0' as <-; rewrite Hc2, <- Hc1; exact Hp.
        - intros (fm & Hm & Ha & Hp).
          assert (Dm : D m) by (apply (Pres γ2 (conj T2 U2) St2); eauto).
          destruct (proj2 (Same' m Dm) (ex_intro _ fm (conj Hm Ha))) as (fm1 & Hm1 & Ha1).
          exists fm1; repeat split; auto.
          destruct (T2 m fm Hm) as (f0 & H0 & Hc2 & _).
          destruct (T1 m fm1 Hm1) as (f0' & H0' & Hc1 & _).
          rewrite H0 in H0'; injection H0' as <-; rewrite Hc1, <- Hc2; exact Hp. }
      destruct (option_map (owner Σ) (binds Σ γ1 k)) as [m1|] eqn:O1,
               (option_map (owner Σ) (binds Σ γ2 k)) as [m2|] eqn:O2; try reflexivity.
      + pose proof (proj1 (Own m1) eq_refl) as E; congruence.
      + pose proof (proj1 (Own m1) eq_refl) as E; congruence.
      + pose proof (proj2 (Own m2) eq_refl) as E; congruence.
  Qed.
End Classify.
