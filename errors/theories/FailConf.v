(** * Confluence with failures, without spawn (errors/DESIGN.md, section 3, layer 2)

    Two quiet runs from the same reachable state end with the same failed
    fibers ([failed_same]): by induction on rank, a fiber's dependencies
    are provided by the same Active fibers with the same ideal traces in
    both runs, so it sees the same initial states, and fails ideally in
    one run iff in the other. With layer 1 ([Classify.vcontrol_confluence])
    this gives confluence with failures ([vconfluence_failures]).

    The failure invariant and the description of quiet states come from
    [FailCrux.v], whose spawn obligation (spawned components provide
    nothing) holds trivially here, since nothing spawns.

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia RelationClasses Permutation Sorted Wf_nat.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering
  Recovery Progress Termination Confluence StateInv Episode.
From CordisErr Require Import IdealFail ViewFail Classify FailCrux.
Import ListNotations.

Section FailConf.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).
  Local Notation Fiber := (@Fiber K Σ C).
  Local Notation Life := (@Life K Σ C).
  Local Notation Undo := (@Undo K Σ).
  Local Notation Prog := (@Prog K Σ C).
  Local Notation S := (St Σ).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation next := (next Σ).
  Local Notation oplog := (oplog Σ).
  Local Notation inilog := (inilog Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation parent := (Calculus.parent Σ).
  Local Notation disposed := (Calculus.disposed Σ).
  Local Notation acc_of := (acc_of Σ).
  Local Notation pid := (pid Σ).
  Local Notation owner := (owner Σ).
  Local Notation bst := (bst Σ).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation WF := (WF K_eq_dec Σ prog).
  Local Notation cbody c := (body Σ (prog c)).
  Local Notation cprovs c := (provs Σ (prog c)).
  Local Notation cdeps c := (deps Σ (prog c)).

  (** ** Hypotheses *)
  Variable Kb : nat.
  Hypothesis HK : forall c, Bounded Σ Kb (cbody c).
  Variable rank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', Above Σ prog c c' -> rank c < rank c'.
  Hypothesis Hbnd : forall c, rank c <= Rb.
  Hypothesis Total : forall c k, In k (cprovs c) -> AllDoneProv Σ k (cbody c).

  Local Notation CInv := (CInv K_eq_dec Σ prog Kb).
  Local Notation CInv0 := (CInv0 K_eq_dec Σ prog Kb).

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

  Local Notation CoPair := (Recovery.CoPair Σ prog).
  Local Notation CoPair_sym := (Recovery.CoPair_sym Σ prog).
  (** Earlier parts, applied to this section's variables. *)
  Local Notation uops := (@uops K Σ) (only parsing).
  Local Notation itok := (@itok K Σ) (only parsing).
  Local Notation in_uops := (@in_uops K Σ) (only parsing).
  Local Notation uacc := (@uacc K Σ C) (only parsing).
  Local Notation GF := (@GF K Σ C prog) (only parsing).
  Local Notation Item := (@Item K Σ C) (only parsing).
  Local Notation PendList := (@PendList K Σ C) (only parsing).
  Local Notation BindInv := (@BindInv K Σ C) (only parsing).
  Local Notation INV := (@INV K Σ C) (only parsing).
  Local Notation SInv := (@SInv K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation sinv_init := (@sinv_init K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation sinv_prov := (@sinv_prov K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation sinv_wf := (@sinv_wf K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation sorted_gt_unique := (@sorted_gt_unique K Σ) (only parsing).
  Local Notation sorted_head_max := (@sorted_head_max K Σ) (only parsing).
  Local Notation sorted_suffix := (@sorted_suffix K Σ) (only parsing).
  Local Notation Sub_OpIn := (@Sub_OpIn K Σ C) (only parsing).
  Local Notation uacc_bound := (@uacc_bound K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation item_lt := (@item_lt K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation item_pid_lt := (@item_pid_lt K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation item_op := (@item_op K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation item_unique := (@item_unique K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation tok_owner := (@tok_owner K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation tokOwner := (@tokOwner K Σ C) (only parsing).
  Local Notation tokOwner_spec := (@tokOwner_spec K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation copair_fibers := (@copair_fibers K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation pend_cross := (@pend_cross K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation item_split := (@item_split K Σ C) (only parsing).
  Local Notation item_relife := (@item_relife K Σ C) (only parsing).
  Local Notation FR := (@FR K Σ C) (only parsing).
  Local Notation FRB := (@FRB K Σ C) (only parsing).
  Local Notation item_back := (@item_back K Σ C) (only parsing).
  Local Notation item_fwd := (@item_fwd K Σ C) (only parsing).
  Local Notation gf_one := (@gf_one K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation gf_nil := (@gf_nil K Σ C prog) (only parsing).
  Local Notation gf_frame := (@gf_frame K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation inv_keep := (@inv_keep K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation inv_frame := (@inv_frame K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation sinv_frame := (@sinv_frame K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation fr_set := (@fr_set K Σ C) (only parsing).
  Local Notation frb_set := (@frb_set K Σ C) (only parsing).
  Local Notation fr_upd := (@fr_upd K Σ C) (only parsing).
  Local Notation sinv_relife := (@sinv_relife K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation sinv_op := (@sinv_op K K_eq_dec Σ C prog Kb Hwb) (only parsing).
  Local Notation sinv_provide := (@sinv_provide K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation item_pop := (@item_pop K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation gf_pop := (@gf_pop K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation sinv_pop_hit := (@sinv_pop_hit K K_eq_dec Σ C prog Kb Hwb HUI HRI) (only parsing).
  Local Notation sinv_pop_miss := (@sinv_pop_miss K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation fr_upd1 := (@fr_upd1 K Σ C) (only parsing).
  Local Notation frb_upd1 := (@frb_upd1 K Σ C) (only parsing).
  Local Notation sinv_step := (@sinv_step K K_eq_dec Σ C prog Kb HK Total Hwb HUI HRI) (only parsing).
  Local Notation Build_SInv := (@Build_SInv K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation s_c := (@s_c K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation s_gf := (@s_gf K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation s_inv := (@s_inv K K_eq_dec Σ C prog Kb) (only parsing).

  Local Notation Itm := (K * nat * nat * (S -> S))%type.
  Local Ltac dif H := match type of H with context [if ?b then _ else _] => destruct b end.

  Local Notation corr_find := (@corr_find K K_eq_dec Σ C prog) (only parsing).
  Local Notation Tr := (Tr K_eq_dec Σ prog).
  Local Notation rho := (rho K_eq_dec Σ).
  Local Notation EPInv := (EPInv K_eq_dec Σ prog).
  Local Notation IdealFails := (IdealFails K_eq_dec Σ prog).
  Local Notation IdealDone := (IdealDone K_eq_dec Σ prog).
  Local Notation VState := (@ViewFail.VState K Σ C).
  Local Notation vcore := (ViewFail.vcore Σ).
  Local Notation PInv := (PInv K_eq_dec Σ prog Kb).
  Local Notation Failed := (Classify.Failed Σ).
  Local Notation VLRun := (Classify.VLRun K_eq_dec Σ prog).

  Hypothesis HNoRej : forall (k : K) (a b : Op Σ) (ta tb : nat), CoPair k a b -> ta <> tb ->
    forall x x' h ob, run a ta x = Some (x', h, ob) -> run b tb x <> None -> run b tb x' <> None.
  Hypothesis NoSpawn : forall c c', ~ SpawnIn Σ c' (cbody c).
  Hypothesis HProv : forall c ρ evs k s P, Tr c ρ evs (PProvide k s P) ->
    In k (cprovs c) /\ find_prov K_eq_dec Σ evs k = None.

  Let HNP : forall c c', SpawnIn Σ c' (cbody c) -> cprovs c' = [] :=
    fun c c' H => False_ind _ (NoSpawn c c' H).

  Local Notation finv_reachable :=
    (FailCrux.finv_reachable K_eq_dec Σ prog Kb HK rank Hrank Total Hwb HUI HTI HRI HCom HNoRej HNP HProv).
  Local Notation quiet_failed_ideal :=
    (FailCrux.quiet_failed_ideal K_eq_dec Σ prog Kb HK rank Rb Hrank Hbnd Total Hwb HUI HTI HRI HCom
       HNoRej HNP HProv).
  Local Notation quiet_active_done :=
    (FailCrux.quiet_active_done K_eq_dec Σ prog Kb HK rank Rb Hrank Hbnd Total Hwb HUI HTI HRI HCom
       HNoRej HNP HProv).
  Local Notation vlrun_reach := (FailCrux.vlrun_reach K_eq_dec Σ prog).
  Local Notation lookup_some := (FailCrux.lookup_some K_eq_dec).

  Lemma cinv_vreach (vs : VState) ls :
    vrun_labels K_eq_dec Σ prog (vinit Σ) ls = Some vs -> NoReact ls -> CInv (vcore vs).
  Proof.
    assert (G : forall vs0 ls vs, CInv (vcore vs0) -> vrun_labels K_eq_dec Σ prog vs0 ls = Some vs ->
                NoReact ls -> CInv (vcore vs)).
    { intros vs0 ls0; revert vs0; induction ls0 as [|ℓ ls0 IH]; cbn; intros vs0 vs1 I0 H NR.
      - injection H as <-; exact I0.
      - destruct (ViewFail.vstep K_eq_dec Σ prog vs0 ℓ) as [vs0'|] eqn:Hs; [|discriminate].
        apply (IH vs0'); [| exact H | intros ℓ' Hin; exact (NR ℓ' (or_intror Hin))].
        exact (cinv_step K_eq_dec Σ prog Kb HK NoSpawn Total _ _ _ (NR ℓ (or_introl eq_refl)) I0
                 (vstep_core K_eq_dec Σ prog vs0 vs0' ℓ Hs)). }
    intros H NR; exact (G (vinit Σ) ls vs (cinv_init K_eq_dec Σ prog Kb) H NR).
  Qed.

  Theorem failed_same (vs0 vs1 vs2 : VState) ls0 :
    vrun_labels K_eq_dec Σ prog (vinit Σ) ls0 = Some vs0 -> NoReact ls0 ->
    VLRun vs0 vs1 -> VLRun vs0 vs2 ->
    vquiet K_eq_dec Σ prog vs1 -> vquiet K_eq_dec Σ prog vs2 ->
    forall n, Failed (vcore vs1) n <-> Failed (vcore vs2) n.
  Proof.
    intros H0 N0 R1 R2 Q1 Q2.
    pose proof (cinv_vreach vs0 ls0 H0 N0) as I0.
    pose proof (vinv_reachable K_eq_dec Σ prog vs0 ls0 H0) as V0.
    destruct (vlrun_static K_eq_dec Σ prog Kb HK rank Hrank NoSpawn Total vs0 vs1 I0 V0 R1) as (C1 & _ & T1 & U1).
    destruct (vlrun_static K_eq_dec Σ prog Kb HK rank Hrank NoSpawn Total vs0 vs2 I0 V0 R2) as (C2 & _ & T2 & U2).
    destruct (vlrun_reach vs0 vs1 ls0 H0 N0 R1) as (ls1 & H1 & N1).
    destruct (vlrun_reach vs0 vs2 ls0 H0 N0 R2) as (ls2 & H2 & N2).
    destruct (finv_reachable vs1 ls1 H1 N1) as [[SI1 EP1] _].
    destruct (finv_reachable vs2 ls2 H2 N2) as [[SI2 EP2] _].
    pose proof (vquiet_settled K_eq_dec Σ prog Kb rank Rb Hrank Hbnd vs1 C1 Q1) as St1.
    pose proof (vquiet_settled K_eq_dec Σ prog Kb rank Rb Hrank Hbnd vs2 C2 Q2) as St2.
    pose proof (sinv_wf _ SI1) as W1; pose proof (sinv_wf _ SI2) as W2.
    pose proof (QF1 := quiet_failed_ideal vs1 ls1 H1 N1 Q1).
    pose proof (QF2 := quiet_failed_ideal vs2 ls2 H2 N2 Q2).
    pose proof (QA1 := quiet_active_done vs1 ls1 H1 N1 Q1).
    pose proof (QA2 := quiet_active_done vs2 ls2 H2 N2 Q2).
    set (γ0 := vcore vs0) in *; set (γ1 := vcore vs1) in *; set (γ2 := vcore vs2) in *.
    (* presence and components come from γ0 *)
    assert (Pr : forall γ, Static Σ γ0 γ -> settled Σ prog γ -> forall n f, fibers γ n = Some f ->
               exists f0, fibers γ0 n = Some f0 /\ fcomp f = fcomp f0 /\ disposed f0 = false).
    { intros γ [Ta _] St n f Hf; destruct (Ta n f Hf) as (f0 & H0' & Hc & Hd).
      exists f0; split; [exact H0'|]; split; [exact Hc|].
      rewrite <- Hd; exact (proj1 (vsettled_shape Σ prog γ n f St Hf)). }
    set (Cl := fun (γ : State) (f : Fiber) =>
                 (is_active Σ (life f), match life f with Inactive _ (Some _) => true | _ => false end)).
    assert (P : forall r n f0, fibers γ0 n = Some f0 -> disposed f0 = false -> rank (fcomp f0) < r ->
              forall f1 f2, fibers γ1 n = Some f1 -> fibers γ2 n = Some f2 ->
                Cl γ1 f1 = Cl γ2 f2 /\
                (forall acc1 w1 acc2 w2 evs1 evs2, life f1 = Active Σ acc1 w1 -> life f2 = Active Σ acc2 w2 ->
                   Tr (fcomp f1) (rho γ1 w1) evs1 PDone -> Tr (fcomp f2) (rho γ2 w2) evs2 PDone -> evs1 = evs2)).
    { induction r as [|r IH]; intros n f0 Hn0 Hd0 Hr f1 f2 Hf1 Hf2; [lia|].
      destruct (T1 n f1 Hf1) as (g1 & Hg1 & Hc1 & _); rewrite Hn0 in Hg1; injection Hg1 as <-.
      destruct (T2 n f2 Hf2) as (g2 & Hg2 & Hc2 & _); rewrite Hn0 in Hg2; injection Hg2 as <-.
      set (c := fcomp f0) in *.
      (* a dependency, seen from both runs *)
      assert (Dep : forall k, In k (cdeps c) ->
                (forall p1, visible Σ γ1 k = Some p1 -> exists p2, visible Σ γ2 k = Some p2 /\
                    inilog γ1 p1 = inilog γ2 p2) /\
                (forall p2, visible Σ γ2 k = Some p2 -> exists p1, visible Σ γ1 k = Some p1)).
      { intros k Hk.
        (* the provider in one run is Active in the other, with the same trace *)
        assert (Side : forall (γa γb : State) (Sa : SInv γa) (Sb : SInv γb) (EPa : EPInv γa) (EPb : EPInv γb),
                  Static Σ γ0 γa -> Static Σ γ0 γb -> settled Σ prog γa -> settled Σ prog γb ->
                  (forall m fa fb, fibers γa m = Some fa -> fibers γb m = Some fb ->
                     forall f0', fibers γ0 m = Some f0' -> disposed f0' = false -> rank (fcomp f0') < r ->
                     Cl γa fa = Cl γb fb /\
                     (forall acca wa accb wb evsa evsb, life fa = Active Σ acca wa -> life fb = Active Σ accb wb ->
                        Tr (fcomp fa) (rho γa wa) evsa PDone -> Tr (fcomp fb) (rho γb wb) evsb PDone ->
                        evsa = evsb)) ->
                  forall pa, visible Σ γa k = Some pa ->
                    exists pb, visible Σ γb k = Some pb /\ inilog γa pa = inilog γb pb).
        { intros γa γb Sa Sb EPa EPb Ta Tb Sta Stb IHab pa Hva.
          pose proof (sinv_wf _ Sa) as Wa; pose proof (sinv_wf _ Sb) as Wb.
          destruct (visible_spec Σ γa k pa Hva) as (ba & fa & Hba & Hpa & Hoa & Haa).
          destruct (wf_bind K_eq_dec Σ prog γa Wa k ba Hba) as (fa' & Hfa' & _ & Hka & Hupa).
          rewrite Hoa in Hfa'; injection Hfa' as <-.
          destruct (Pr γa Ta Sta _ fa Hoa) as (h0 & Hh0 & Hch & Hdh).
          destruct (proj2 Tb (owner ba) h0 Hh0 Hdh) as [fb Hfb].
          destruct (Pr γb Tb Stb _ fb Hfb) as (h0' & Hh0' & Hchb & _).
          rewrite Hh0 in Hh0'; injection Hh0' as <-.
          assert (Hrk : rank (fcomp h0) < r).
          { assert (rank (fcomp h0) < rank c).
            { rewrite <- Hch; apply Hrank; left; exists k; split; [exact (kmem_In K_eq_dec k _ Hka) | exact Hk]. }
            lia. }
          destruct (IHab (owner ba) fa fb Hoa Hfb h0 Hh0 Hdh Hrk) as [Ecl Eev].
          unfold Cl in Ecl; injection Ecl as Eact _.
          rewrite Haa in Eact; symmetry in Eact.
          assert (Hkb : In k (cprovs (fcomp fb))) by (rewrite Hchb, <- Hch; exact (kmem_In K_eq_dec k _ Hka)).
          destruct (active_binds K_eq_dec Σ prog Kb γb (owner ba) fb k (s_c _ Sb) Hfb Eact Hkb) as (bb & Hbb & Hob).
          exists (pid bb); split.
          { unfold visible; rewrite Hbb, Hob, Hfb, Eact; reflexivity. }
          destruct (life fa) as [| |acca wa|] eqn:Hla; try discriminate.
          destruct (life fb) as [| |accb wb|] eqn:Hlb; try discriminate.
          pose proof (EPa _ fa Hoa) as Ea; rewrite Hla in Ea; destruct Ea as (evsa & Tra & Coa).
          pose proof (EPb _ fb Hfb) as Eb; rewrite Hlb in Eb; destruct Eb as (evsb & Trb & Cob).
          pose proof (Eev acca wa accb wb evsa evsb eq_refl eq_refl Tra Trb) as <-.
          pose proof (wf_uprov_unique K_eq_dec Σ prog γa Wa _ fa Hoa) as Ua; rewrite Hla in Ua.
          destruct (wf_bind K_eq_dec Σ prog γb Wb k bb Hbb) as (fb' & Hfb' & _ & _ & Hupb).
          rewrite Hob, Hfb in Hfb'; injection Hfb' as <-; rewrite Hlb in Hupb.
          pose proof (wf_uprov_unique K_eq_dec Σ prog γb Wb _ fb Hfb) as Ub; rewrite Hlb in Ub.
          destruct (corr_find γa _ wa acca evsa k (pid ba) Coa Ua Hupa) as (sa & Hia & Hfa).
          destruct (corr_find γb _ wb accb evsa k (pid bb) Cob Ub Hupb) as (sb & Hib & Hfb2).
          rewrite <- Hpa, Hia, Hib; congruence. }
        split.
        - exact (Side γ1 γ2 SI1 SI2 EP1 EP2 (conj T1 U1) (conj T2 U2) St1 St2
                   (fun m fa fb Ha Hb f0' H0' Hd' Hr' => IH m f0' H0' Hd' Hr' fa fb Ha Hb)).
        - intros p2 Hv2.
          destruct (Side γ2 γ1 SI2 SI1 EP2 EP1 (conj T2 U2) (conj T1 U1) St2 St1
                      (fun m fa fb Ha Hb f0' H0' Hd' Hr' =>
                         let '(conj E1 E2) := IH m f0' H0' Hd' Hr' fb fa Hb Ha in
                         conj (eq_sym E1) (fun a1 b1 a2 b2 e1 e2 L1 L2 X1 X2 => eq_sym (E2 a2 b2 a1 b1 e2 e1 L2 L1 X2 X1)))
                      p2 Hv2) as (p1 & Hv1 & _).
          exists p1; exact Hv1. }
      (* targets agree, and so do the initial states they name *)
      assert (Tgt : forall w1, target Σ prog γ1 n = Some w1 ->
                exists w2, target Σ prog γ2 n = Some w2 /\
                  forall k, In k (cdeps c) -> rho γ1 w1 k = rho γ2 w2 k).
      { intros w1 Ht1.
        assert (Hv2 : forall k, In k (cdeps c) -> exists p, visible Σ γ2 k = Some p).
        { intros k Hk.
          pose proof (resolve_spec Σ γ1 _ w1 (target_spec Σ prog γ1 n f1 w1 Hf1 Ht1)) as [Hkeys Hvis].
          assert (Hkw : In k (map fst w1)) by (unfold fdeps in Hkeys; rewrite Hkeys, Hc1; exact Hk).
          destruct (lookup_some k w1 Hkw) as [p Hp].
          destruct (proj1 (Dep k Hk) p (Hvis k p (lv_In K_eq_dec k w1 p Hp))) as (p2 & Hp2 & _); eauto. }
        assert (Hd2 : disposed f2 = false) by exact (proj1 (vsettled_shape Σ prog γ2 n f2 St2 Hf2)).
        assert (Hv2' : forall k, In k (deps Σ (prog (fcomp f2))) -> exists p, visible Σ γ2 k = Some p)
          by (rewrite Hc2; exact Hv2).
        destruct (resolve_some Σ γ2 _ Hv2') as [w2 Hw2].
        assert (Ht2 : target Σ prog γ2 n = Some w2) by (unfold target; rewrite Hf2, Hd2; exact Hw2).
        exists w2; split; [exact Ht2|].
        intros k Hk.
        pose proof (resolve_spec Σ γ1 _ w1 (target_spec Σ prog γ1 n f1 w1 Hf1 Ht1)) as [Hk1 Hvis1].
        pose proof (resolve_spec Σ γ2 _ w2 (target_spec Σ prog γ2 n f2 w2 Hf2 Ht2)) as [Hk2 Hvis2].
        assert (Hkw1 : In k (map fst w1)) by (unfold fdeps in Hk1; rewrite Hk1, Hc1; exact Hk).
        assert (Hkw2 : In k (map fst w2)) by (unfold fdeps in Hk2; rewrite Hk2, Hc2; exact Hk).
        destruct (lookup_some k w1 Hkw1) as [p1 Hp1].
        destruct (lookup_some k w2 Hkw2) as [p2 Hp2].
        pose proof (Hvis1 k p1 (lv_In K_eq_dec k w1 p1 Hp1)) as V1.
        pose proof (Hvis2 k p2 (lv_In K_eq_dec k w2 p2 Hp2)) as V2.
        destruct (proj1 (Dep k Hk) p1 V1) as (p2' & V2' & Ei).
        rewrite V2 in V2'; injection V2' as <-.
        unfold Episode.rho; rewrite Hp1, Hp2; exact Ei. }
      assert (Tgt2 : forall w2, target Σ prog γ2 n = Some w2 -> exists w1, target Σ prog γ1 n = Some w1).
      { intros w2 Ht2.
        assert (Hv1 : forall k, In k (deps Σ (prog (fcomp f1))) -> exists p, visible Σ γ1 k = Some p).
        { intros k Hk; rewrite Hc1 in Hk.
          pose proof (resolve_spec Σ γ2 _ w2 (target_spec Σ prog γ2 n f2 w2 Hf2 Ht2)) as [Hkeys Hvis].
          assert (Hkw : In k (map fst w2)) by (unfold fdeps in Hkeys; rewrite Hkeys, Hc2; exact Hk).
          destruct (lookup_some k w2 Hkw) as [p Hp].
          exact (proj2 (Dep k Hk) p (Hvis k p (lv_In K_eq_dec k w2 p Hp))). }
        assert (Hd1 : disposed f1 = false) by exact (proj1 (vsettled_shape Σ prog γ1 n f1 St1 Hf1)).
        destruct (resolve_some Σ γ1 _ Hv1) as [w1 Hw1].
        exists w1; unfold target; rewrite Hf1, Hd1; exact Hw1. }
      (* the three shapes of a settled fiber *)
      assert (Shape : forall γ (QF : forall n f e, fibers γ n = Some f -> life f = Inactive Σ (Some e) ->
                         exists w, target Σ prog γ n = Some w /\ IdealFails (fcomp f) (rho γ w))
                         (QA : forall n f acc w, fibers γ n = Some f -> life f = Active Σ acc w ->
                         target Σ prog γ n = Some w /\ IdealDone (fcomp f) (rho γ w))
                         f, settled Σ prog γ -> fibers γ n = Some f ->
                (life f = Inactive Σ None /\ target Σ prog γ n = None) \/
                (exists acc w, life f = Active Σ acc w /\ target Σ prog γ n = Some w /\ IdealDone (fcomp f) (rho γ w)) \/
                (exists e w, life f = Inactive Σ (Some e) /\ target Σ prog γ n = Some w /\ IdealFails (fcomp f) (rho γ w))).
      { intros γ QF QA f St Hf.
        destruct (vsettled_shape Σ prog γ n f St Hf) as [_ [[Hl Ht]|[(acc & w & Hl & Ht)|(e & Hl)]]].
        - left; auto.
        - right; left; exists acc, w; split; [exact Hl|]; exact (QA n f acc w Hf Hl).
        - right; right; destruct (QF n f e Hf Hl) as (w & Ht & Hi); exists e, w; auto. }
      destruct (Shape γ1 QF1 QA1 f1 St1 Hf1) as [[L1 Ht1]|[(acc1 & w1 & L1 & Ht1 & D1)|(e1 & w1 & L1 & Ht1 & F1)]];
      destruct (Shape γ2 QF2 QA2 f2 St2 Hf2) as [[L2 Ht2]|[(acc2 & w2 & L2 & Ht2 & D2)|(e2 & w2 & L2 & Ht2 & F2)]].
      all: try (destruct (Tgt2 _ Ht2) as [w1' Ht1']; congruence).
      all: try (destruct (Tgt _ Ht1) as (w2' & Ht2' & _); congruence).
      all: try (destruct (Tgt _ Ht1) as (w2' & Ht2' & E); rewrite Ht2 in Ht2'; injection Ht2' as <-).
      + split; [unfold Cl; rewrite L1, L2; reflexivity | intros; rewrite L1 in *; discriminate].
      + split; [unfold Cl; rewrite L1, L2; reflexivity|].
        intros a1 v1 a2 v2 e1' e2' La Lb Xa Xb.
        rewrite L1 in La; injection La as <- <-; rewrite L2 in Lb; injection Lb as <- <-.
        rewrite Hc1, Hc2 in *.
        exact (tr_done_eq K_eq_dec Σ prog Hwb _ _ _ e1' e2' E Xa Xb).
      + exfalso; rewrite Hc1 in D1; rewrite Hc2 in F2.
        exact (ideal_excl K_eq_dec Σ prog Hwb _ _ (ideal_done_ext K_eq_dec Σ prog _ _ _ E D1) F2).
      + exfalso; rewrite Hc1 in F1; rewrite Hc2 in D2.
        exact (ideal_excl K_eq_dec Σ prog Hwb _ _ D2 (ideal_fails_ext K_eq_dec Σ prog _ _ _ E F1)).
      + split; [unfold Cl; rewrite L1, L2; reflexivity | intros; rewrite L1 in *; discriminate]. }
    intros n; split.
    - intros (f1 & e & Hf1 & Hl1).
      destruct (Pr γ1 (conj T1 U1) St1 n f1 Hf1) as (f0 & Hn0 & _ & Hd0).
      destruct (U2 n f0 Hn0 Hd0) as [f2 Hf2].
      destruct (P _ n f0 Hn0 Hd0 (Nat.lt_succ_diag_r _) f1 f2 Hf1 Hf2) as [E _].
      unfold Cl in E; rewrite Hl1 in E; injection E as _ E.
      destruct (life f2) as [[e2|]| | |] eqn:Hl2; try discriminate; exists f2, e2; auto.
    - intros (f2 & e & Hf2 & Hl2).
      destruct (Pr γ2 (conj T2 U2) St2 n f2 Hf2) as (f0 & Hn0 & _ & Hd0).
      destruct (U1 n f0 Hn0 Hd0) as [f1 Hf1].
      destruct (P _ n f0 Hn0 Hd0 (Nat.lt_succ_diag_r _) f1 f2 Hf1 Hf2) as [E _].
      unfold Cl in E; rewrite Hl2 in E; injection E as _ E.
      destruct (life f1) as [[e1|]| | |] eqn:Hl1; try discriminate; exists f1, e1; auto.
  Qed.

  (** ** Confluence with failures, without spawn *)
  Theorem vconfluence_failures (vs0 vs1 vs2 : VState) ls0 :
    vrun_labels K_eq_dec Σ prog (vinit Σ) ls0 = Some vs0 -> NoReact ls0 ->
    VLRun vs0 vs1 -> VLRun vs0 vs2 ->
    vquiet K_eq_dec Σ prog vs1 -> vquiet K_eq_dec Σ prog vs2 ->
    (forall n, Failed (vcore vs1) n <-> Failed (vcore vs2) n) /\
    (forall n, (exists f, fibers (vcore vs1) n = Some f) <-> (exists f, fibers (vcore vs2) n = Some f)) /\
    (forall n f1 f2, fibers (vcore vs1) n = Some f1 -> fibers (vcore vs2) n = Some f2 ->
       fcomp f1 = fcomp f2 /\ is_active Σ (life f1) = is_active Σ (life f2)) /\
    (forall k, option_map owner (binds (vcore vs1) k) = option_map owner (binds (vcore vs2) k)).
  Proof.
    intros H0 N0 R1 R2 Q1 Q2.
    pose proof (failed_same vs0 vs1 vs2 ls0 H0 N0 R1 R2 Q1 Q2) as FF.
    split; [exact FF|].
    exact (vcontrol_confluence K_eq_dec Σ prog Kb HK rank Rb Hrank Hbnd NoSpawn Total vs0 vs1 vs2
             (cinv_vreach vs0 ls0 H0 N0) (vinv_reachable K_eq_dec Σ prog vs0 ls0 H0) R1 R2 Q1 Q2 FF).
  Qed.
End FailConf.
