(** * Confluence with failures under interleaved orchestration (errors/DESIGN.md, section 3)

    The core's [Dynamic.dynamic_confluence] (the paper's Theorem 80(2))
    asks that no fiber has failed at the end. This file gives the same
    results with failures scoped to their view:

    - [DRunV]: an execution of the extended state, with lifecycle steps
      and [VClear] anywhere, and the orchestration inputs in order;
    - the root ledger of [Dynamic.v] ([Ledger]) is kept by every step,
      [VClear] included ([ledger_oreset]); so are the core invariants;
    - final roots are read off the ledger as in the core, without
      [NoFailed] ([final_root], [ledger_rootinj], [ledger_match]);
    - [vdynamic_agree]: two executions from the initial state whose inputs
      leave the same surviving components in the same order, and insert
      only insertable components, agree up to renaming at their quiet
      states, failed fibers included; [vdynamic_confluence] (the same
      inputs) and [vstatic_assembly] (Theorem 80(1)) follow.

    The proof reduces to [SpawnConfF.final_agree], with the failure
    description from [FailCrux.v].

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering
  Recovery Progress Termination Confluence StateInv Episode Dynamic.
From CordisErr Require Import IdealFail ViewFail Classify FailCrux StateConfF SpawnConfF.
Import ListNotations.

Section DynamicF.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).
  Local Notation Fiber := (@Fiber K Σ C).
  Local Notation Label := (@Label C).
  Local Notation S := (St Σ).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation cbody c := (body Σ (prog c)).
  Local Notation cprovs c := (provs Σ (prog c)).
  Local Notation VState := (@ViewFail.VState K Σ C).
  Local Notation vcore := (ViewFail.vcore Σ).
  Local Notation vstep := (ViewFail.vstep K_eq_dec Σ prog).

  Variable Kb : nat.
  Hypothesis HK : forall c, Bounded Σ Kb (cbody c).
  Local Notation PInv := (PInv K_eq_dec Σ prog Kb).
  Variable rank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', Above Σ prog c c' -> rank c < rank c'.
  Hypothesis Hbnd : forall c, rank c <= Rb.
  Hypothesis Total : forall c k, In k (cprovs c) -> AllDoneProv Σ k (cbody c).
  Hypothesis Hwb : forall a t, WellBehaved (Σ := Σ) a t.
  Hypothesis HUI : forall (a : Op Σ) (t : nat) (s1 s2 s1' s2' : S) (g1 g2 : S -> S) (o1 o2 : Out Σ),
    run a t s1 = Some (s1', g1, o1) -> run a t s2 = Some (s2', g2, o2) -> fun_eq (Σ := Σ) g1 g2.
  Hypothesis HTI : forall (a : Op Σ) (t t' : nat) (s : S),
    match run a t s, run a t' s with
    | None, None => True
    | Some (s1, _, o1), Some (s2, _, o2) => @st_eq Σ s1 s2 /\ o1 = o2
    | _, _ => False
    end.
  Hypothesis HRI : forall (k : K) (a b : Op Σ) (ta tb : nat) (g : S -> S), (@CoPair K Σ C prog) k a b -> ta <> tb ->
    yields (Σ := Σ) a ta g ->
    forall x, After ((@CoPair K Σ C prog) k a) a ta x -> shifted_ok (Σ := Σ) g (run b tb x) (run b tb (g x)).
  Hypothesis HCom : forall (k : K) (a b : Op Σ) (ta tb : nat), (@CoPair K Σ C prog) k a b -> ta <> tb ->
    Commute (Σ := Σ) a ta b tb.
  Hypothesis HNoRej : forall (k : K) (a b : Op Σ) (ta tb : nat), (@CoPair K Σ C prog) k a b -> ta <> tb ->
    forall x x' h ob, run a ta x = Some (x', h, ob) -> run b tb x <> None -> run b tb x' <> None.
  Hypothesis HProv : forall c ρ evs k s P, Tr K_eq_dec Σ prog c ρ evs (PProvide k s P) ->
    In k (cprovs c) /\ find_prov K_eq_dec Σ evs k = None.
  Variable rootb : C -> bool.
  Hypothesis HKidDisj : forall p c' d, SpawnIn Σ c' (cbody p) ->
    overlaps K_eq_dec (cprovs c') (cprovs d) = true -> d = c'.
  Hypothesis HKidRoot : forall p c', SpawnIn Σ c' (cbody p) -> rootb c' = true -> cprovs c' = [].
  Hypothesis HKidUnique : forall p p' c', SpawnIn Σ c' (cbody p) -> Spawns Σ prog p' c' ->
    cprovs c' <> [] -> p' = p.
  Hypothesis HKidParent : forall p c', SpawnIn Σ c' (cbody p) -> cprovs c' <> [] -> cprovs p <> [].
  Hypothesis HKidOnce : forall c ρ evs c' P, Tr K_eq_dec Σ prog c ρ evs (PSpawn c' P) -> cprovs c' <> [] ->
    ~ In (TSpawn Σ c') evs.

  (** ** Executions with orchestration *)
  Inductive DRunV : VState -> list nat -> list Input -> VState -> list nat -> Prop :=
  | dv_nil vs rs : DRunV vs rs [] vs rs
  | dv_life vs rs ins ℓ vs1 vs2 rs2 :
      vlife ℓ -> vstep vs ℓ = Some vs1 -> DRunV vs1 rs ins vs2 rs2 -> DRunV vs rs ins vs2 rs2
  | dv_orch vs rs x ins ℓ vs1 vs2 rs2 :
      olabel rs x = Some ℓ -> vstep vs (ViewFail.VCore ℓ) = Some vs1 ->
      DRunV vs1 (radd Σ rs (vcore vs) x) ins vs2 rs2 -> DRunV vs rs (x :: ins) vs2 rs2.

  (** Insertions use insertable components only. *)
  Definition RootIns (ins : list Input) : Prop := forall c, In (IIns c) ins -> rootb c = true.

  (** ** [VClear] keeps the root ledger *)
  Lemma ledger_oreset (γ γ' : State) rs done n :
    Ledger Σ γ rs done -> step γ (OReset n) = Some γ' -> Ledger Σ γ' rs done.
  Proof.
    intros L H; cbn [Calculus.step] in H.
    destruct (fibers Σ γ n) as [f|] eqn:Hn; [|discriminate].
    destruct (life Σ f) as [[e|]| | |] eqn:Hl; try discriminate; injection H as <-.
    destruct L as [Ll Lnd Llt Ld Lat Lr]; split.
    - exact Ll.
    - exact Lnd.
    - exact Llt.
    - exact Ld.
    - intros i m Hm; rewrite fibers_set_life.
      destruct (Lat i m Hm) as [[N D]|(g & Hg & Pg & Cg & Dg)];
        destruct (Nat.eqb_spec m n) as [->|].
      + rewrite Hn in N; discriminate.
      + left; auto.
      + right; rewrite Hn in Hg; injection Hg as <-; eexists; split; [reflexivity|]; cbn; auto.
      + right; eauto.
    - intros m g Hm Pm; rewrite fibers_set_life in Hm.
      destruct (Nat.eqb_spec m n) as [->|]; [injection Hm as <-; cbn in Pm; exact (Lr n f Hn Pm)|].
      exact (Lr m g Hm Pm).
  Qed.

  Lemma drunv_inv (vs vs' : VState) rs ins rs' done :
    DRunV vs rs ins vs' rs' -> Ledger Σ (vcore vs) rs done -> PInv (vcore vs) ->
    SpawnConf.SLInv Σ (vcore vs) ->
    Ledger Σ (vcore vs') rs' (done ++ ins) /\ PInv (vcore vs') /\ SpawnConf.SLInv Σ (vcore vs').
  Proof.
    intros R; revert done;
      induction R as [vs rs|vs rs ins ℓ vs1 vs2 rs2 Hl Hs R IH|vs rs x ins ℓ vs1 vs2 rs2 Ho Hs R IH];
      intros done L P SL.
    - rewrite app_nil_r; auto.
    - pose proof (vstep_core K_eq_dec Σ prog vs vs1 ℓ Hs) as Hc.
      pose proof (pinv_step K_eq_dec Σ prog Kb HK rank Hrank Total Hwb HUI HTI HRI HCom _ _ _
                    (vlife_core_label ℓ Hl) P Hc) as P1.
      destruct Hl as [(n & ℓ0 & Hin & ->)|(n & ->)]; cbn [vlabel] in Hc.
      + apply IH; [exact (ledger_life K_eq_dec Σ prog Kb _ _ rs done ℓ0 L P (ex_intro _ n Hin) Hc)
                  | exact P1 | exact (SpawnConf.sl_step K_eq_dec Σ prog Kb _ _ ℓ0 P SL (ex_intro _ n Hin) Hc)].
      + apply IH; [exact (ledger_oreset _ _ rs done n L Hc) | exact P1
                  | exact (sl_reset K_eq_dec Σ prog _ _ n SL Hc)].
    - pose proof (vstep_core K_eq_dec Σ prog vs vs1 _ Hs) as Hc; cbn [vlabel] in Hc.
      replace (done ++ x :: ins) with ((done ++ [x]) ++ ins) by (rewrite <- app_assoc; reflexivity).
      apply IH; [exact (ledger_orch K_eq_dec Σ prog Kb _ _ rs done x ℓ L P Ho Hc)
                | exact (pinv_step K_eq_dec Σ prog Kb HK rank Hrank Total Hwb HUI HTI HRI HCom _ _ ℓ
                           (olabel_not_react rs x ℓ Ho) P Hc) |].
      destruct x as [c|i|i|i]; cbn [olabel] in Ho.
      + injection Ho as <-; exact (sl_insert K_eq_dec Σ prog Kb _ _ c P SL Hc).
      + destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
        destruct (lg_at Σ _ _ _ L i n Hn) as [[N _]|(f & Hf & Pf & _)].
        * cbn [Calculus.step] in Hc; rewrite N in Hc; discriminate.
        * exact (sl_dispose K_eq_dec Σ prog Kb _ _ n f P SL Hf Pf Hc).
      + destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
        exact (sl_restart K_eq_dec Σ prog _ _ n SL Hc).
      + destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
        exact (sl_reset K_eq_dec Σ prog _ _ n SL Hc).
  Qed.

  (** An execution with orchestration is a run of labels. *)
  Lemma drunv_vrun (vs vs' : VState) rs ins rs' :
    DRunV vs rs ins vs' rs' ->
    exists ls, vrun_labels K_eq_dec Σ prog vs ls = Some vs' /\ NoReact ls /\
      (RootIns ins -> RootOK rootb ls).
  Proof.
    induction 1 as [vs rs|vs rs ins ℓ vs1 vs2 rs2 Hl Hs R IH|vs rs x ins ℓ vs1 vs2 rs2 Ho Hs R IH].
    - exists []; split; [reflexivity|]; split; [intros ℓ []|intros _ ℓ []].
    - destruct IH as (ls & Hr & N & O).
      exists (ℓ :: ls); split; [cbn; rewrite Hs; exact Hr|]; split.
      + intros ℓ' [<-|Hin]; [exact (vlife_core_label ℓ Hl) | exact (N ℓ' Hin)].
      + intros Ri ℓ' [<-|Hin] c Hc; [|exact (O Ri ℓ' Hin c Hc)].
        destruct Hl as [(n & ℓ0 & Hin & ->)|(n & ->)]; cbn [vlabel] in Hc; [|discriminate].
        subst ℓ0; cbn in Hin; intuition discriminate.
    - destruct IH as (ls & Hr & N & O).
      exists (ViewFail.VCore ℓ :: ls); split; [cbn [vrun_labels]; rewrite Hs; exact Hr|]; split.
      + intros ℓ' [<-|Hin]; [exact (olabel_not_react rs x ℓ Ho) | exact (N ℓ' Hin)].
      + intros Ri ℓ' [<-|Hin] c Hc.
        * cbn [vlabel] in Hc; subst ℓ.
          destruct x as [c'|i|i|i]; cbn in Ho;
            [injection Ho as ->; exact (Ri c (or_introl eq_refl))
            | destruct (nth_error rs i); cbn in Ho; discriminate..].
        * exact (O (fun c' H => Ri c' (or_intror H)) ℓ' Hin c Hc).
  Qed.

  (** ** Final roots, failed fibers allowed *)
  Lemma final_root (γ : State) rs ins n f :
    Ledger Σ γ rs ins -> settled Σ prog γ ->
    fibers Σ γ n = Some f -> parent Σ f = None ->
    nth_error rs (pos rs n) = Some n /\ live_ix ins (pos rs n) = true /\
    nth_error (icomps ins) (pos rs n) = Some (comp Σ f).
  Proof.
    intros L St Hn Pn.
    pose proof (nth_pos rs n (lg_root Σ _ _ _ L n f Hn Pn)) as E.
    destruct (vsettled_shape Σ prog γ n f St Hn) as [Hd _].
    destruct (lg_at Σ _ _ _ L _ n E) as [[N _]|(f0 & Hf0 & _ & Cf & Df)]; [congruence|].
    rewrite Hn in Hf0; injection Hf0 as <-.
    split; [exact E|]; split; [|exact Cf].
    apply live_ix_spec; intros A; apply Df in A; congruence.
  Qed.

  Lemma final_slab (γ : State) rs ins n f :
    Ledger Σ γ rs ins -> settled Σ prog γ ->
    fibers Σ γ n = Some f -> parent Σ f = None ->
    nth_error (sroots rs ins) (slab rs ins n) = Some n /\
    slab rs ins n = cnt (live_ix ins) 0 (pos rs n) /\
    nth_error (scomps ins) (slab rs ins n) = Some (comp Σ f).
  Proof.
    intros L St Hn Pn.
    destruct (final_root γ rs ins n f L St Hn Pn) as (E & Lv & Cf).
    pose proof (keepi_nth (live_ix ins) rs 0 _ n E Lv) as En.
    assert (Es : slab rs ins n = cnt (live_ix ins) 0 (pos rs n)).
    { exact (pos_nth _ _ n (keepi_nodup _ _ _ (lg_nodup Σ _ _ _ L)) En). }
    split; [rewrite Es; exact En|]; split; [exact Es|].
    rewrite Es; exact (keepi_nth (live_ix ins) (icomps ins) 0 _ _ Cf Lv).
  Qed.

  Lemma ledger_rootinj (γ : State) rs ins :
    Ledger Σ γ rs ins -> settled Σ prog γ -> RootInj Σ (slab rs ins) γ.
  Proof.
    intros L St n n' f f' Hn Pn Hn' Pn' E.
    destruct (final_slab γ rs ins n f L St Hn Pn) as (A & _).
    destruct (final_slab γ rs ins n' f' L St Hn' Pn') as (B & _).
    rewrite E in A; congruence.
  Qed.

  Lemma ledger_match (γ1 γ2 : State) rs1 rs2 ins1 ins2 :
    Ledger Σ γ1 rs1 ins1 -> Ledger Σ γ2 rs2 ins2 -> scomps ins1 = scomps ins2 ->
    settled Σ prog γ1 -> RootsMatch Σ (slab rs1 ins1) (slab rs2 ins2) γ1 γ2.
  Proof.
    intros L1 L2 Es St n f1 Hn Pn.
    destruct (final_slab γ1 rs1 ins1 n f1 L1 St Hn Pn) as (_ & _ & Cs).
    rewrite Es in Cs.
    destruct (keepi_surj _ _ _ _ _ Cs) as (i & Lv & Ci & Ei); cbn in Lv.
    assert (Hi : i < length rs2) by (rewrite (lg_len Σ _ _ _ L2); apply nth_error_Some; congruence).
    destruct (nth_error rs2 i) as [n2|] eqn:E2; [|apply nth_error_None in E2; lia].
    destruct (lg_at Σ _ _ _ L2 i n2 E2) as [[_ D]|(f2 & Hf2 & Pf2 & Cf2 & _)].
    { apply live_ix_spec in Lv; contradiction. }
    exists n2, f2; split; [exact Hf2|]; split; [exact Pf2|]; split.
    - pose proof (keepi_nth (live_ix ins2) rs2 0 i n2 E2 Lv) as En.
      change (slab rs2 ins2 n2) with (pos (keepi (live_ix ins2) rs2 0) n2).
      rewrite (pos_nth _ _ n2 (keepi_nodup _ _ _ (lg_nodup Σ _ _ _ L2)) En); exact Ci.
    - congruence.
  Qed.

  (** ** Confluence under interleaved orchestration, with failures *)
  Theorem vdynamic_agree ins1 ins2 (vs1 vs2 : VState) rs1 rs2 :
    DRunV (vinit Σ) [] ins1 vs1 rs1 -> DRunV (vinit Σ) [] ins2 vs2 rs2 ->
    scomps ins1 = scomps ins2 -> RootIns ins1 -> RootIns ins2 ->
    vquiet K_eq_dec Σ prog vs1 -> vquiet K_eq_dec Σ prog vs2 ->
    AgreeL Σ (slab rs1 ins1) (slab rs2 ins2) (vcore vs1) (vcore vs2).
  Proof.
    intros R1 R2 Es RI1 RI2 Q1 Q2.
    assert (SL0 : SpawnConf.SLInv Σ (@init K Σ C)) by (split; intros; discriminate).
    assert (Fin : forall ins vs rs, DRunV (vinit Σ) [] ins vs rs -> RootIns ins -> vquiet K_eq_dec Σ prog vs ->
              Ledger Σ (vcore vs) rs ins /\ settled Σ prog (vcore vs) /\
              FinalS K_eq_dec Σ prog Kb (vcore vs) /\ FailChar K_eq_dec Σ prog (vcore vs)).
    { intros ins vs rs R Ri Q.
      destruct (drunv_inv _ _ _ _ _ [] R (ledger_init Σ) (pinv_init K_eq_dec Σ prog Kb) SL0)
        as (L & P & SL); cbn [app] in L.
      destruct (drunv_vrun _ _ _ _ _ R) as (ls & H & N & O).
      destruct (vquiet_current K_eq_dec Σ prog (Hwf Σ prog rank Rb Hrank Hbnd) vs ls H Q) as [St _].
      split; [exact L|]; split; [exact St|]; split.
      - split; [split; [exact P | exact St]|].
        destruct SL as [a b c]; exact (SpawnConfF.Build_SLInv Σ _ a b c).
      - exact (quiet_failed_ideal K_eq_dec Σ prog Kb HK rank Rb Hrank Hbnd Total Hwb HUI HTI HRI HCom
                 HNoRej HProv rootb HKidDisj HKidRoot HKidUnique HKidParent HKidOnce vs ls H N (O Ri) Q). }
    destruct (Fin ins1 vs1 rs1 R1 RI1 Q1) as (L1 & St1 & F1 & FC1).
    destruct (Fin ins2 vs2 rs2 R2 RI2 Q2) as (L2 & St2 & F2 & FC2).
    exact (final_agree K_eq_dec Σ prog Kb rank Rb Hrank Hbnd Hwb HTI HCom _ _ _ _ F1 F2 FC1 FC2
             (ledger_rootinj _ rs1 ins1 L1 St1) (ledger_rootinj _ rs2 ins2 L2 St2)
             (ledger_match _ _ rs1 rs2 ins1 ins2 L1 L2 Es St1)
             (ledger_match _ _ rs2 rs1 ins2 ins1 L2 L1 (eq_sym Es) St2)).
  Qed.

  (** The same inputs, in any interleaving (Theorem 80(2)). *)
  Corollary vdynamic_confluence ins (vs1 vs2 : VState) rs1 rs2 :
    DRunV (vinit Σ) [] ins vs1 rs1 -> DRunV (vinit Σ) [] ins vs2 rs2 -> RootIns ins ->
    vquiet K_eq_dec Σ prog vs1 -> vquiet K_eq_dec Σ prog vs2 ->
    AgreeL Σ (slab rs1 ins) (slab rs2 ins) (vcore vs1) (vcore vs2).
  Proof. intros R1 R2 Ri; exact (vdynamic_agree ins ins vs1 vs2 rs1 rs2 R1 R2 eq_refl Ri Ri). Qed.

  (** Static assembly (Theorem 80(1)): whatever history an execution went
      through, its quiet state agrees with that of an execution that only
      inserts the surviving components, once each, in order. *)
  Corollary vstatic_assembly ins (vs vss : VState) rs rss :
    DRunV (vinit Σ) [] ins vs rs -> DRunV (vinit Σ) [] (map IIns (scomps ins)) vss rss -> RootIns ins ->
    vquiet K_eq_dec Σ prog vs -> vquiet K_eq_dec Σ prog vss ->
    AgreeL Σ (slab rs ins) (slab rss (map IIns (scomps ins))) (vcore vs) (vcore vss).
  Proof.
    intros R Rs Ri.
    assert (Ris : RootIns (map IIns (scomps ins))).
    { intros c Hc; apply in_map_iff in Hc as (c' & E & Hc'); injection E as ->.
      apply Ri; unfold scomps in Hc'; apply keepi_in in Hc'.
      clear -Hc'; induction ins as [|[c0|i|i|i] ins IH]; cbn in *; [destruct Hc'| | | |];
        try (destruct Hc' as [->|Hc']; [left; reflexivity | right; exact (IH Hc')]);
        right; exact (IH Hc'). }
    exact (vdynamic_agree ins _ vs vss rs rss R Rs (eq_sym (scomps_static _)) Ri Ris).
  Qed.
End DynamicF.
