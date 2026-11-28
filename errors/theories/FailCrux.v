(** * Every failure of a load is an ideal failure (errors/DESIGN.md, section 3, layer 2)

    When an operation of a Loading fiber is rejected in the actual state,
    it is rejected on the fiber's ideal trace too ([op_fail_ideal]). The
    actual state is the provision's initial state, then the fiber's own
    operations, then other fibers' operations that may meet it
    ([StateInv]); the core's [outcome_after] gives "succeeds in the actual
    state, then succeeds ideally". The other half needs a new service
    obligation, [HNoRej]: an operation that succeeds at a state still
    succeeds after an operation it may meet ([outcome_before]). [Commute]
    alone does not give it: it allows a and b to reject each other in both
    orders, as two registrations of one name do.

    With two static obligations ([NoSpawn]; [HProv]: a program provides
    only declared keys, each at most once on a path), every way a load
    step fails is an ideal failure ([load_fail_ideal]). Hence the failure
    invariant [FailInv]: an Unloading fiber with an error, and a failed
    fiber under its recorded view, fail ideally; every step keeps it
    ([finv_step], [finv_reachable]). At a quiet reachable state a failed
    fiber fails ideally under its current target ([quiet_failed_ideal]) and
    an Active fiber reaches [Done] ideally under it ([quiet_active_done]);
    by [IdealFail.ideal_excl] the two exclude each other.

    Finally, two quiet runs from the same reachable state end with the
    same failed fibers ([failed_same]): by induction on rank, a fiber's
    dependencies are provided by the same Active fibers with the same
    ideal traces in both runs, so it sees the same initial states, and
    fails ideally in one run iff in the other. With layer 1
    ([Classify.vcontrol_confluence]) this gives confluence with failures
    ([vconfluence_failures]): same failed fibers, same fibers and
    components, same Active fibers, same providers.

    The section header repeats [Episode.v]'s, so that the core's proof of
    [Episode.ep_op] can be followed step by step.

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia RelationClasses Permutation Sorted Wf_nat.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering
  Recovery Progress Termination Confluence StateInv Episode.
From CordisErr Require Import IdealFail ViewFail Classify.
Import ListNotations.

Section FailCrux.
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

  Local Notation itemsF := (@itemsF K K_eq_dec Σ C) (only parsing).
  Local Notation in_itemsF := (@in_itemsF K K_eq_dec Σ C) (only parsing).
  Local Notation itemsF_sorted := (@itemsF_sorted K K_eq_dec Σ C) (only parsing).
  Local Notation corr_find := (@corr_find K K_eq_dec Σ C prog) (only parsing).
  Local Notation corr_item := (@corr_item K K_eq_dec Σ C prog) (only parsing).
  Local Notation corr_ops := (@corr_ops K K_eq_dec Σ C prog) (only parsing).
  Local Notation upu_unique := (@upu_unique K Σ) (only parsing).
  Local Notation Tr := (Tr K_eq_dec Σ prog).
  Local Notation resolveI := (resolveI K_eq_dec Σ prog).
  Local Notation ownIt := (ownIt K_eq_dec Σ).
  Local Notation rho := (rho K_eq_dec Σ).
  Local Notation EPInv := (EPInv K_eq_dec Σ prog).
  Local Notation IdealFails := (IdealFails K_eq_dec Σ prog).

  (** The new obligation: an operation that succeeds at [x] still succeeds
      after an operation it may meet. *)
  Hypothesis HNoRej : forall (k : K) (a b : Op Σ) (ta tb : nat), CoPair k a b -> ta <> tb ->
    forall x x' h ob, run a ta x = Some (x', h, ob) -> run b tb x <> None -> run b tb x' <> None.

  (** ** Succeeding before the operations it meets *)
  Lemma outcome_before k a t l s0 s :
    (forall b u, In (b, u) l -> CoPair k b a /\ u <> t) ->
    Replay l s0 s -> run a t s0 <> None -> run a t s <> None.
  Proof.
    intros Hl H; induction H as [s|b u l s s1 h ob s2 Hr Hl' IH]; intros Ha; [exact Ha|].
    apply IH; [intros b' u' Hin; exact (Hl b' u' (or_intror Hin))|].
    destruct (Hl b u (or_introl eq_refl)) as [Hm Hu].
    exact (HNoRej k b a u t Hm Hu s s1 h ob Hr Ha).
  Qed.

  (** ** A rejected operation is rejected ideally *)
  Lemma op_fail_ideal (γ : State) n f k a κ acc w b :
    SInv γ -> EPInv γ ->
    fibers γ n = Some f -> life f = Loading Σ (POp k a κ) acc w ->
    op_binding K_eq_dec Σ prog γ n f k w = Some b -> run a (next γ) (bst b) = None ->
    IdealFails (fcomp f) (rho γ w).
  Proof.
    intros SI EP Hn Hl Hob Hr.
    pose proof (sinv_wf γ SI) as W.
    pose proof (EP n f Hn) as Ef; rewrite Hl in Ef; destruct Ef as (evs & T & Co).
    pose proof (op_binding_spec K_eq_dec Σ prog γ n f k w b Hob) as Hb.
    destruct (s_inv _ SI k b Hb) as (s0 & L & s & Hi & PL & R & Eq).
    assert (Hres : resolveI (fcomp f) (rho γ w) evs k = Some s0 /\
                   (if kmem K_eq_dec k (cdeps (fcomp f)) then lookup_view K_eq_dec k w = Some (pid b)
                    else In (UProv Σ k (pid b)) acc)).
    { unfold op_binding in Hob; unfold Episode.resolveI, Episode.rho.
      destruct (kmem K_eq_dec k (cdeps (fcomp f))) eqn:Hk.
      - destruct (lookup_view K_eq_dec k w) as [p|] eqn:Hp; [|try rewrite Hb in Hob; discriminate].
        rewrite Hb in Hob; destruct (Nat.eqb_spec (pid b) p) as [<-|]; [|discriminate].
        split; [exact Hi | reflexivity].
      - rewrite Hb in Hob.
        destruct (Nat.eqb_spec (owner b) n) as [Ho|]; [|discriminate].
        destruct (wf_bind K_eq_dec Σ prog γ W k b Hb) as (fo & Hfo & _ & _ & Hup).
        rewrite Ho, Hn in Hfo; injection Hfo as <-; rewrite Hl in Hup; cbn in Hup.
        split; [|exact Hup].
        pose proof (wf_uprov_unique K_eq_dec Σ prog γ W n f Hn) as U; rewrite Hl in U.
        destruct (corr_find γ (fcomp f) w acc evs k (pid b) Co U Hup) as (s1 & Hi1 & Hf1).
        rewrite Hf1; congruence. }
    destruct Hres as [Hres Hif].
    pose proof (proj1 (pv_fib Σ prog γ (sinv_prov γ SI) n f Hn) _ _ _ Hl) as Hsub.
    assert (Hopa : OpAt Σ k a (cbody (fcomp f))) by exact (Sub_OpAt Σ k a _ _ Hsub (at_here Σ k a κ)).
    destruct PL as [Hs HL].
    set (own := flab onat_eq_dec (tokOwner γ) (Some n) L).
    set (oth := fnot onat_eq_dec (tokOwner γ) (Some n) L).
    pose proof (pend_cross γ k (pid b) L SI (conj Hs HL)) as CR.
    destruct (replay_shuffle_ex (CoPair k) Hwb (HCom k) onat_eq_dec (tokOwner γ) L (own ++ oth) s0 s CR
                (flab_partition onat_eq_dec (tokOwner γ) (Some n) L) R) as (sL & R' & Es).
    apply replay_app in R' as (sO & Rown & Roth).
    pose proof (wb_respects a (next γ) (Hwb a (next γ)) (bst b) sL (transitivity Eq Es)) as Hrs; rewrite Hr in Hrs.
    destruct (run a (next γ) sL) as [[[s2 g2] o2]|] eqn:Hr2; [destruct Hrs|].
    assert (Hoth : forall b0 u, In (b0, u) oth -> CoPair k b0 a /\ u <> next γ).
    { intros b0 u Hin; unfold oth, fnot in Hin; apply filter_In in Hin as [Hin Hlab]; cbn in Hlab.
      destruct (onat_eq_dec (tokOwner γ u) (Some n)) as [_|Nl]; [discriminate|].
      destruct (proj1 (HL b0 u) Hin) as [(m & fm & g' & Hm & I') Hb0].
      split; [|pose proof (uacc_bound γ m fm k (pid b) u g' SI Hm I'); lia].
      rewrite (tokOwner_spec γ m fm k (pid b) u g' SI Hm I') in Nl.
      destruct (item_op γ m fm k (pid b) u g' SI Hm I') as (b1 & Hb1 & Hop1).
      rewrite Hb0 in Hb1; injection Hb1 as <-.
      apply (copair_fibers γ m fm n f k b0 a SI); [congruence | exact Hm | exact Hn | exact Hop1 | exact Hopa]. }
    (* the operation is rejected before the others' operations too *)
    assert (HrO : run a (next γ) sO = None).
    { destruct (run a (next γ) sO) eqn:E; [|reflexivity]; exfalso.
      apply (outcome_before k a (next γ) oth sO sL Hoth Roth); [rewrite E; discriminate | exact Hr2]. }
    assert (Eown : own = rev (itemsF γ k (uacc f))).
    { pose proof (wf_uprov_unique K_eq_dec Σ prog γ W n f Hn) as U; rewrite Hl in U.
      apply sorted_items_eq.
      - unfold own, flab; apply ss_filter; exact Hs.
      - rewrite map_rev; apply ss_rev_nat, itemsF_sorted; exact (proj1 (s_gf _ SI n f Hn)).
      - intros [a' t]; rewrite <- in_rev, in_itemsF; unfold own; rewrite in_flab; cbn; split.
        + intros [Hin Hlab].
          apply HL in Hin as [(m & fm & g' & Hm & I') Ho].
          rewrite (tokOwner_spec γ m fm k (pid b) t g' SI Hm I') in Hlab; injection Hlab as ->.
          rewrite Hn in Hm; injection Hm as <-; exists (pid b), g'; auto.
        + intros (q & g' & I' & Ho).
          assert (Hq : q = pid b).
          { assert (Ia : In (UOp Σ k q t g') acc) by (unfold uacc in I'; rewrite Hl in I'; apply in_uops; exact I').
            pose proof (corr_item γ (fcomp f) w acc evs k q t g' Co Ia) as Hc.
            destruct (kmem K_eq_dec k (cdeps (fcomp f))); [congruence|].
            exact (upu_unique acc k q (pid b) U Hc Hif). }
          subst q; split; [apply HL; split; [exists n, f, g'; auto | exact Ho]|].
          exact (tokOwner_spec γ n f k (pid b) t g' SI Hn I'). }
    assert (Ef : map fst own = map fst (ownIt k evs)).
    { rewrite Eown, map_rev; unfold Episode.ownIt; rewrite map_map; cbn; rewrite map_id.
      unfold uacc; rewrite Hl; cbn [Calculus.acc_of]; rewrite (corr_ops γ _ _ _ _ k Co); reflexivity. }
    destruct (replay_tokens Hwb HTI own (ownIt k evs) s0 sO Ef Rown s0 (reflexivity _)) as (s1i & Ri & Ei).
    pose proof (HTI a (next γ) 0 sO) as Ht; rewrite HrO in Ht.
    destruct (run a 0 sO) as [[[s3 g3] o3]|] eqn:Hr3; [destruct Ht|].
    pose proof (wb_respects a 0 (Hwb a 0) sO s1i Ei) as Hrs'; rewrite Hr3 in Hrs'.
    destruct (run a 0 s1i) as [[[s4 g4] o4]|] eqn:Hr4; [destruct Hrs'|].
    exists evs, (POp k a κ); split; [exact T|]; cbn; right.
    exists s0, s1i; auto.
  Qed.

  (** ** Every way a load step fails is an ideal failure *)

  (** Two static obligations, as in layer 1: components do not spawn, and a
      program provides only declared keys, each at most once on a path. *)
  Hypothesis HSpawnNP : forall c c', SpawnIn Σ c' (cbody c) -> cprovs c' = [].
  Hypothesis HProv : forall c ρ evs k s P, Tr c ρ evs (PProvide k s P) ->
    In k (cprovs c) /\ find_prov K_eq_dec Σ evs k = None.

  Lemma corr_find_rev (γ : State) c w acc evs k s :
    Corr K_eq_dec Σ prog γ c w acc evs -> find_prov K_eq_dec Σ evs k = Some s ->
    exists p, In (UProv Σ k p) acc.
  Proof.
    intros H; induction H as [|k' p t g a acc evs H IH Ho Hr|k' p s' acc evs H IH Hi|m c' acc evs H IH Hc];
      cbn; intros Hf; try discriminate.
    - destruct (IH Hf) as [p' Hp]; exists p'; right; exact Hp.
    - destruct (K_eq_dec k k') as [->|]; [exists p; left; reflexivity|].
      destruct (IH Hf) as [p' Hp]; exists p'; right; exact Hp.
    - destruct (IH Hf) as [p' Hp]; exists p'; right; exact Hp.
  Qed.

  Lemma lookup_some k (w : @View K) : In k (map fst w) -> exists p, lookup_view K_eq_dec k w = Some p.
  Proof.
    induction w as [|[k' p'] w IH]; cbn; [intros []|]; intros [E|Hin].
    - subst k'; unfold keqb; destruct (K_eq_dec k k); [eauto | contradiction].
    - unfold keqb; destruct (K_eq_dec k k'); [eauto | exact (IH Hin)].
  Qed.

  Lemma In_kmem k ks : In k ks -> kmem K_eq_dec k ks = true.
  Proof.
    intros Hin; unfold kmem; apply existsb_exists; exists k; split; [exact Hin|].
    unfold keqb; destruct (K_eq_dec k k); [reflexivity | contradiction].
  Qed.

  Lemma overlaps_true k l1 l2 :
    kmem K_eq_dec k l1 = true -> kmem K_eq_dec k l2 = true -> overlaps K_eq_dec l1 l2 = true.
  Proof.
    intros H1 H2; unfold overlaps; apply existsb_exists; exists k; split; [|exact H2].
    exact (kmem_In K_eq_dec k _ H1).
  Qed.

  Theorem load_fail_ideal (γ : State) n f P acc w acc' w' z :
    SInv γ -> EPInv γ -> fibers γ n = Some f -> life f = Loading Σ P acc w ->
    fibers (load_step K_eq_dec Σ prog γ n f P acc w) n =
      Some (mkFiber Σ (fcomp f) (parent f) (disposed f) (Unloading Σ acc' w' (Some z))) ->
    IdealFails (fcomp f) (rho γ w).
  Proof.
    intros SI EP Hn Hl H.
    pose proof (sinv_wf γ SI) as W.
    pose proof (EP n f Hn) as Ef; rewrite Hl in Ef; destruct Ef as (evs & T & Co).
    assert (Rl : forall γ1 l, fibers (set_life Σ γ1 n f l) n =
                   Some (mkFiber Σ (fcomp f) (parent f) (disposed f) l))
      by (intros; rewrite fibers_set_life, Nat.eqb_refl; reflexivity).
    destruct P as [| |k a κ|k s P'|c' P'].
    - cbn [load_step] in H; rewrite Rl in H; discriminate.
    - exists evs, PFail; split; [exact T | exact Logic.I].
    - rewrite load_step_op in H.
      destruct (op_binding K_eq_dec Σ prog γ n f k w) as [b|] eqn:Hob.
      + destruct (run a (next γ) (bst b)) as [[[s' g] o]|] eqn:Hr;
          [rewrite Rl in H; discriminate|].
        exact (op_fail_ideal γ n f k a κ acc w b SI EP Hn Hl Hob Hr).
      + exists evs, (POp k a κ); split; [exact T|]; cbn; left.
        unfold Episode.resolveI.
        destruct (kmem K_eq_dec k (cdeps (fcomp f))) eqn:Hk.
        * exfalso.
          assert (Hkw : In k (map fst w)).
          { pose proof (wf_view_keys K_eq_dec Σ prog γ W n f Hn) as Vk; rewrite Hl in Vk.
            specialize (Vk eq_refl); cbn [view_of] in Vk; rewrite Vk; unfold fdeps; exact (kmem_In K_eq_dec k _ Hk). }
          destruct (lookup_some k w Hkw) as [p Hp].
          assert (Hin : In (k, p) (view_of Σ (life f))) by (rewrite Hl; exact (lv_In K_eq_dec k w p Hp)).
          destruct (wf_view K_eq_dec Σ prog γ W n f k p Hn Hin) as (b & Hb & Hpb & _).
          unfold op_binding in Hob; rewrite Hk, Hp, Hb, Hpb, Nat.eqb_refl in Hob; discriminate.
        * destruct (find_prov K_eq_dec Σ evs k) as [s|] eqn:Hf; [exfalso|reflexivity].
          destruct (corr_find_rev γ _ w acc evs k s Co Hf) as [p Hp].
          assert (Hin : In (UProv Σ k p) (acc_of (life f))) by (rewrite Hl; exact Hp).
          destruct (wf_uprov K_eq_dec Σ prog γ W n f k p Hn Hin) as (b & Hb & Hpb & Hob').
          unfold op_binding in Hob; rewrite Hk, Hb, Hob', Nat.eqb_refl, Nat.eqb_refl in Hob.
          discriminate.
    - destruct (HProv _ _ _ k s P' T) as [Hkp Hfp].
      cbn [load_step] in H.
      rewrite (In_kmem k _ Hkp) in H.
      destruct (binds γ k) as [b|] eqn:Hb; [|rewrite Rl in H; discriminate].
      exfalso.
      destruct (wf_bind K_eq_dec Σ prog γ W k b Hb) as (fo & Ho & _ & Hko & Hup).
      destruct (Nat.eq_dec (owner b) n) as [Eo|Neo].
      + rewrite Eo, Hn in Ho; injection Ho as <-; rewrite Hl in Hup; cbn in Hup.
        pose proof (wf_uprov_unique K_eq_dec Σ prog γ W n f Hn) as U; rewrite Hl in U.
        destruct (corr_find γ (fcomp f) w acc evs k (pid b) Co U Hup) as (s1 & _ & Hf1).
        congruence.
      + pose proof (wf_disjoint K_eq_dec Σ prog γ W (owner b) n fo f Neo Ho Hn) as D.
        unfold fprovs in D, Hko; rewrite (overlaps_true k _ _ Hko (In_kmem k _ Hkp)) in D; discriminate.
    - (* a spawned component provides nothing, so a spawn never conflicts *)
      assert (Hnp : cprovs c' = []).
      { apply (HSpawnNP (fcomp f) c').
        pose proof (proj1 (pv_fib Σ prog γ (sinv_prov γ SI) n f Hn) _ _ _ Hl) as Hsub.
        exact (SpawnIn_Sub Σ c' _ _ Hsub (spi_here Σ c' P')). }
      assert (Hc : conflict K_eq_dec Σ prog γ c' = false).
      { unfold conflict; induction (names Σ γ) as [|m l IH]; cbn; [reflexivity|].
        rewrite IH, orb_false_r; destruct (fibers γ m); [|reflexivity]; rewrite Hnp; reflexivity. }
      cbn [load_step] in H; rewrite Hc, Rl in H; discriminate.
  Qed.

  (** ** Steps keep the initial states of existing provisions *)
  Lemma load_step_inilog (γ : State) n f P acc w :
    next γ <= next (load_step K_eq_dec Σ prog γ n f P acc w) /\
    forall p, p < next γ -> inilog (load_step K_eq_dec Σ prog γ n f P acc w) p = inilog γ p.
  Proof.
    unfold load_step; destruct P; cbn zeta;
      repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
      cbn; (split; [lia | intros p Hp; try (destruct (Nat.eqb_spec p (next γ)); [lia|]); reflexivity]).
  Qed.

  Lemma step_inilog (γ γ' : State) ℓ :
    step γ ℓ = Some γ' -> next γ <= next γ' /\ forall p, p < next γ -> inilog γ' p = inilog γ p.
  Proof.
    intros H; destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [Calculus.step] in H.
    all: repeat match type of H with context [match ?x with _ => _ end] => destruct x eqn:? end;
      try discriminate.
    all: try (unfold undo_step in H;
              repeat match type of H with context [match ?x with _ => _ end] => destruct x eqn:? end;
              try discriminate).
    all: injection H as <-; first [apply load_step_inilog | cbn; split; [lia | intros p Hp; reflexivity]].
  Qed.

  (** ** The failure invariant *)
  Local Notation VState := (@ViewFail.VState K Σ C).
  Local Notation vcore := (ViewFail.vcore Σ).
  Local Notation fview := (ViewFail.fview Σ).
  Local Notation vstep := (ViewFail.vstep K_eq_dec Σ prog).
  Local Notation IdealDone := (IdealDone K_eq_dec Σ prog).

  Definition FailInv (vs : VState) : Prop :=
    (forall n f acc w e, fibers (vcore vs) n = Some f -> life f = Unloading Σ acc w (Some e) ->
       IdealFails (fcomp f) (rho (vcore vs) w)) /\
    (forall n f e, fibers (vcore vs) n = Some f -> life f = Inactive Σ (Some e) ->
       exists w, fview vs n = Some w /\ IdealFails (fcomp f) (rho (vcore vs) w)) /\
    (forall n w, fview vs n = Some w -> forall k p, In (k, p) w -> p < next (vcore vs)).

  Lemma rho_keep (γ γ' : State) w :
    (forall k p, In (k, p) w -> p < next γ) -> (forall p, p < next γ -> inilog γ' p = inilog γ p) ->
    forall k, rho γ' w k = rho γ w k.
  Proof.
    intros Hw Hi k; unfold Episode.rho.
    destruct (lookup_view K_eq_dec k w) as [p|] eqn:Hp; [|reflexivity].
    apply Hi, (Hw k p), (lv_In K_eq_dec k w p Hp).
  Qed.

  Lemma view_pids (γ : State) n f k p :
    WF γ -> fibers γ n = Some f -> In (k, p) (view_of Σ (life f)) -> p < next γ.
  Proof.
    intros W Hn Hin.
    destruct (wf_view K_eq_dec Σ prog γ W n f k p Hn Hin) as (b & Hb & <- & _).
    exact (wf_pids K_eq_dec Σ prog γ W k b Hb).
  Qed.

  Lemma load_step_other (γ : State) n f P acc w m :
    m <> n ->
    fibers (load_step K_eq_dec Σ prog γ n f P acc w) m = fibers γ m \/
    exists c p, fibers (load_step K_eq_dec Σ prog γ n f P acc w) m =
                Some (mkFiber Σ c p false (Inactive Σ None)).
  Proof.
    intros Hmn; unfold load_step; destruct P; cbn zeta;
      repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
      rewrite fibers_set_life; destruct (Nat.eqb_spec m n); try contradiction; cbn; try (left; reflexivity).
    unfold fupd; destruct (Nat.eqb_spec m (next γ)); [right; eauto | left; reflexivity].
  Qed.

  (** A fiber unloading with an error after a step: it was so before, or the
      step was its failing load step. *)
  Lemma unload_after (γ γ' : State) ℓ m fm' acc' w e :
    step γ ℓ = Some γ' -> fibers γ' m = Some fm' -> life fm' = Unloading Σ acc' w (Some e) ->
    (exists fm acc, fibers γ m = Some fm /\ fcomp fm = fcomp fm' /\ life fm = Unloading Σ acc w (Some e)) \/
    (exists fm P acc, fibers γ m = Some fm /\ life fm = Loading Σ P acc w /\
       fibers (load_step K_eq_dec Σ prog γ m fm P acc w) m =
         Some (mkFiber Σ (fcomp fm) (parent fm) (disposed fm) (Unloading Σ acc' w (Some e)))).
  Proof.
    intros H Hm Hl.
    assert (Same : forall fm, fibers γ m = Some fm -> fm' = fm ->
              (exists fm acc, fibers γ m = Some fm /\ fcomp fm = fcomp fm' /\
                 life fm = Unloading Σ acc w (Some e)) \/ False)
      by (intros fm Hf ->; left; exists fm, acc'; auto).
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [Calculus.step] in H.
    - destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      cbn in Hm; unfold fupd in Hm; destruct (Nat.eqb_spec m (next γ)).
      + injection Hm as <-; discriminate.
      + destruct (Same _ Hm eq_refl) as [X|[]]; left; exact X.
    - destruct (fibers γ n) as [fn|] eqn:Hn; [|discriminate]; injection H as <-.
      unfold set_fiber, with_fibers, fupd in Hm; cbn in Hm.
      destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; cbn in Hl; left; exists fn, acc'; auto.
      + destruct (Same _ Hm eq_refl) as [X|[]]; left; exact X.
    - destruct (fibers γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life fn) as [[z|]| | |]; try discriminate; injection H as <-.
      rewrite fibers_set_life in Hm; destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; discriminate.
      + destruct (Same _ Hm eq_refl) as [X|[]]; left; exact X.
    - destruct (fibers γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life fn) as [[z|]| | |]; try discriminate.
      destruct (target Σ prog γ n); [|discriminate]; injection H as <-.
      rewrite fibers_set_life in Hm; destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; discriminate.
      + destruct (Same _ Hm eq_refl) as [X|[]]; left; exact X.
    - destruct (fibers γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life fn) as [|P acc w0| |] eqn:Hl0; try discriminate.
      destruct (may_step K_eq_dec Σ prog γ n P w0); [|discriminate]; injection H as <-.
      destruct (Nat.eq_dec m n) as [->|Hmn].
      + right; exists fn, P, acc.
        assert (Ew : w0 = w).
        { assert (V : forall γ1 l, fibers (set_life Σ γ1 n fn l) n = Some fm' -> fm' = mkFiber Σ (fcomp fn) (parent fn) (disposed fn) l)
            by (intros γ1 l E; rewrite fibers_set_life, Nat.eqb_refl in E; injection E as <-; reflexivity).
          unfold load_step in Hm; destruct P; cbn zeta in Hm;
            repeat match type of Hm with context [match ?x with _ => _ end] => destruct x end;
            apply V in Hm; subst fm'; cbn in Hl; congruence. }
        subst w0; split; [exact Hn|]; split; [exact Hl0|].
        rewrite Hm; destruct fm' as [c' p' d' l']; cbn in Hl; subst l'.
        f_equal.
        assert (V : forall γ1 l, fibers (set_life Σ γ1 n fn l) n = Some (mkFiber Σ c' p' d' (Unloading Σ acc' w (Some e))) ->
                    c' = fcomp fn /\ p' = parent fn /\ d' = disposed fn)
          by (intros γ1 l E; rewrite fibers_set_life, Nat.eqb_refl in E; injection E; auto).
        assert (X : c' = fcomp fn /\ p' = parent fn /\ d' = disposed fn).
        { unfold load_step in Hm; destruct P; cbn zeta in Hm;
            repeat match type of Hm with context [match ?x with _ => _ end] => destruct x end;
            exact (V _ _ Hm). }
        destruct X as (-> & -> & ->); reflexivity.
      + destruct (load_step_other γ n fn P acc w0 m Hmn) as [E|(c & p & E)]; rewrite E in Hm.
        * destruct (Same _ Hm eq_refl) as [X|[]]; left; exact X.
        * injection Hm as <-; discriminate.
    - destruct (fibers γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life fn) as [|P acc w0| |]; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w0); [discriminate|]; injection H as <-.
      rewrite fibers_set_life in Hm; destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; discriminate.
      + destruct (Same _ Hm eq_refl) as [X|[]]; left; exact X.
    - destruct (fibers γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life fn) as [| |acc w0|]; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w0); [discriminate|]; injection H as <-.
      rewrite fibers_set_life in Hm; destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; discriminate.
      + destruct (Same _ Hm eq_refl) as [X|[]]; left; exact X.
    - destruct (fibers γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life fn) as [| | |[|u acc] w0 z] eqn:Hl0; try discriminate.
      destruct (held Σ γ n (u :: acc)); [discriminate|].
      destruct (undo_step_shape K_eq_dec Σ γ γ' n fn u acc w0 z H) as (γ1 & -> & E).
      rewrite fibers_set_life in Hm; destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; cbn in Hl; injection Hl as _ -> ->.
        left; exists fn, (u :: acc); auto.
      + rewrite E in Hm; destruct (Same _ Hm eq_refl) as [X|[]]; left; exact X.
    - destruct (fibers γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life fn) as [| | |[|[| |m'] acc] w0 z]; try discriminate.
      destruct (fibers γ m') as [g|] eqn:Hg; [|discriminate].
      destruct (held Σ γ n (USpawn Σ m' :: acc) || disposed g); [discriminate|]; injection H as <-.
      unfold set_fiber, with_fibers, fupd in Hm; cbn in Hm.
      destruct (Nat.eqb_spec m m') as [->|].
      + injection Hm as <-; cbn in Hl; left; exists g, acc'; auto.
      + destruct (Same _ Hm eq_refl) as [X|[]]; left; exact X.
    - destruct (fibers γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life fn) as [| | |[|u acc] w0 z]; try discriminate; injection H as <-.
      rewrite fibers_set_life in Hm; destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; discriminate.
      + destruct (Same _ Hm eq_refl) as [X|[]]; left; exact X.
    - destruct (fibers γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life fn); try discriminate.
      destruct (disposed fn && negb (has_child Σ γ n)); [|discriminate]; injection H as <-.
      cbn in Hm; unfold fupd in Hm; destruct (Nat.eqb_spec m n); [discriminate|].
      destruct (Same _ Hm eq_refl) as [X|[]]; left; exact X.
    - destruct (fibers γ n) as [fn|] eqn:Hn; [|discriminate].
      destruct (life fn) as [| |acc w0|]; try discriminate.
      destruct (nth_error (reacts Σ (prog (fcomp fn))) i) as [c|]; [|discriminate].
      destruct (disposed fn || conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      rewrite fibers_set_life in Hm; destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; discriminate.
      + cbn in Hm; unfold fupd in Hm; destruct (Nat.eqb_spec m (next γ)).
        * injection Hm as <-; discriminate.
        * destruct (Same _ Hm eq_refl) as [X|[]]; left; exact X.
    - fold (step γ (ORestart n)) in H.
      apply restart_shape in H as (fn & acc & w0 & Hn & _ & _ & ->).
      rewrite fibers_set_life in Hm; destruct (Nat.eqb_spec m n) as [->|].
      + injection Hm as <-; discriminate.
      + destruct (Same _ Hm eq_refl) as [X|[]]; left; exact X.
  Qed.

  Local Notation PInv := (PInv K_eq_dec Σ prog Kb).

  Lemma same_comp (γ γ' : State) ℓ m f fm' :
    SInv γ -> step γ ℓ = Some γ' -> fibers γ m = Some f -> fibers γ' m = Some fm' -> fcomp fm' = fcomp f.
  Proof.
    intros SI H Hf Hm.
    pose proof (sinv_wf γ SI) as W.
    destruct (step_names K_eq_dec Σ prog Kb rank Hrank γ γ' ℓ (c0_t K_eq_dec Σ prog Kb _ (s_c γ SI)) H
                m fm' Hm (wf_names K_eq_dec Σ prog γ W m f Hf)) as (f0 & Hf0 & Hc).
    rewrite Hf in Hf0; injection Hf0 as <-; congruence.
  Qed.

  (** ** Every step keeps the failure invariant *)
  Theorem finv_step (vs vs' : VState) ℓ :
    PInv (vcore vs) -> FailInv vs -> vstep vs ℓ = Some vs' -> FailInv vs'.
  Proof.
    intros [SI EP] (F1 & F2 & F3) H.
    pose proof (vstep_core K_eq_dec Σ prog vs vs' ℓ H) as Hs.
    pose proof (vstep_fview K_eq_dec Σ prog vs vs' ℓ H) as HF.
    destruct (step_inilog _ _ _ Hs) as [Hnx Hini].
    pose proof (sinv_wf _ SI) as W.
    set (γ := vcore vs) in *; set (γ' := vcore vs') in *.
    assert (Keep : forall w, (forall k p, In (k, p) w -> p < next γ) ->
              forall c, IdealFails c (rho γ w) -> IdealFails c (rho γ' w)).
    { intros w Hw c; apply ideal_fails_ext; intros k _; exact (eq_sym (rho_keep γ γ' w Hw Hini k)). }
    assert (VP : forall m f, fibers γ m = Some f -> forall k p, In (k, p) (view_of Σ (life f)) -> p < next γ)
      by (intros m f Hf k p Hin; exact (view_pids γ m f k p W Hf Hin)).
    (* recorded views name provisions below the old counter *)
    assert (F3' : forall n w, fview vs' n = Some w -> forall k p, In (k, p) w -> p < next γ).
    { intros n w Hw; rewrite HF in Hw.
      destruct ℓ as [[c|n0|n0|n0|n0|n0|n0|n0|n0|n0|n0|n0 i|n0]|n0]; try exact (F3 n w Hw).
      unfold vupd in Hw; destruct (Nat.eqb_spec n n0) as [->|]; [|exact (F3 n w Hw)].
      unfold unloading_view in Hw; fold γ in Hw.
      destruct (fibers γ n0) as [f0|] eqn:Hf0; [|discriminate].
      destruct (life f0) as [| | |[|u acc] w0 z] eqn:Hl0; try discriminate; injection Hw as <-.
      intros k p Hin; apply (VP n0 f0 Hf0 k); rewrite Hl0; exact Hin. }
    split; [|split].
    - intros m fm' acc' w e Hm Hl.
      destruct (unload_after γ γ' _ m fm' acc' w e Hs Hm Hl)
        as [(fm & acc & Hf & Hc & Hlf)|(fm & P & acc & Hf & Hlf & Hls)].
      + rewrite <- Hc; apply Keep; [|exact (F1 m fm acc w e Hf Hlf)].
        intros k p Hin; apply (VP m fm Hf k); rewrite Hlf; exact Hin.
      + rewrite (same_comp γ γ' _ m fm fm' SI Hs Hf Hm).
        apply Keep; [|exact (load_fail_ideal γ m fm P acc w acc' w e SI EP Hf Hlf Hls)].
        intros k p Hin; apply (VP m fm Hf k); rewrite Hlf; exact Hin.
    - intros m fm' e Hm Hl.
      destruct (failed_after K_eq_dec Σ prog γ γ' _ m fm' e Hs Hm Hl) as [(f & Hf & Hlf)|HU].
      + destruct (F2 m f e Hf Hlf) as (w & Hw & Hid).
        exists w; split.
        * rewrite HF.
          destruct ℓ as [[c|n0|n0|n0|n0|n0|n0|n0|n0|n0|n0|n0 i|n0]|n0]; try exact Hw.
          unfold vupd; destruct (Nat.eqb_spec m n0) as [->|]; [|exact Hw].
          exfalso; cbn [vlabel Calculus.step] in Hs; fold γ in Hs; rewrite Hf, Hlf in Hs; discriminate.
        * rewrite (same_comp γ γ' _ m f fm' SI Hs Hf Hm).
          exact (Keep w (F3 m w Hw) _ Hid).
      + destruct ℓ as [ℓ0|n0]; cbn [vlabel] in HU; [|discriminate]; subst ℓ0.
        pose proof Hs as Hs0; cbn [vlabel Calculus.step] in Hs0.
        destruct (fibers γ m) as [f0|] eqn:Hf0; [|discriminate].
        destruct (life f0) as [| | |[|u acc] w0 z0] eqn:Hl0; try discriminate.
        injection Hs0 as Hs0.
        assert (Hz : z0 = Some e /\ fcomp fm' = fcomp f0).
        { unfold γ' in Hs0; rewrite <- Hs0 in Hm; rewrite fibers_set_life, Nat.eqb_refl in Hm; injection Hm as <-; cbn in Hl.
          injection Hl as ->; auto. }
        destruct Hz as [-> Hc].
        exists w0; split.
        * rewrite HF; unfold vupd; rewrite Nat.eqb_refl.
          unfold unloading_view; fold γ; rewrite Hf0, Hl0; reflexivity.
        * rewrite Hc; apply Keep; [|exact (F1 m f0 [] w0 e Hf0 Hl0)].
          intros k p Hin; apply (VP m f0 Hf0 k); rewrite Hl0; exact Hin.
    - intros n w Hw k p Hin; pose proof (F3' n w Hw k p Hin); unfold γ, γ' in *; lia.
  Qed.

  (** ** From the initial state *)
  Definition NoReact (ls : list (@VLabel C)) : Prop :=
    forall ℓ, In ℓ ls -> forall n i, vlabel ℓ <> OReact n i.

  Corollary finv_reachable (vs : VState) ls :
    vrun_labels K_eq_dec Σ prog (vinit Σ) ls = Some vs -> NoReact ls ->
    PInv (vcore vs) /\ FailInv vs.
  Proof.
    assert (G : forall vs0 ls vs, PInv (vcore vs0) -> FailInv vs0 ->
                vrun_labels K_eq_dec Σ prog vs0 ls = Some vs -> NoReact ls ->
                PInv (vcore vs) /\ FailInv vs).
    { intros vs0 ls0; revert vs0; induction ls0 as [|ℓ ls0 IH]; cbn; intros vs0 vs1 P0 F0 H NR.
      - injection H as <-; auto.
      - destruct (ViewFail.vstep K_eq_dec Σ prog vs0 ℓ) as [vs0'|] eqn:Hs; [|discriminate].
        apply (IH vs0'); [| exact (finv_step vs0 vs0' ℓ P0 F0 Hs) | exact H |].
        + exact (pinv_step K_eq_dec Σ prog Kb HK rank Hrank Total Hwb HUI HTI HRI HCom _ _ _
                   (NR ℓ (or_introl eq_refl)) P0 (vstep_core K_eq_dec Σ prog vs0 vs0' ℓ Hs)).
        + intros ℓ' Hin; exact (NR ℓ' (or_intror Hin)). }
    intros H NR; apply (G (vinit Σ) ls vs); [exact (pinv_init K_eq_dec Σ prog Kb) | | exact H | exact NR].
    split; [intros n f acc w e Hn; discriminate|]; split; [intros n f e Hn; discriminate|].
    intros n w Hw; discriminate.
  Qed.

  (** ** Quiet states: failed fibers fail ideally, Active ones reach [Done] *)
  Theorem quiet_failed_ideal (vs : VState) ls :
    vrun_labels K_eq_dec Σ prog (vinit Σ) ls = Some vs -> NoReact ls -> vquiet K_eq_dec Σ prog vs ->
    forall n f e, fibers (vcore vs) n = Some f -> life f = Inactive Σ (Some e) ->
      exists w, target Σ prog (vcore vs) n = Some w /\ IdealFails (fcomp f) (rho (vcore vs) w).
  Proof.
    intros H NR Q n f e Hn Hl.
    destruct (vquiet_current K_eq_dec Σ prog (Confluence.Hwf Σ prog rank Rb Hrank Hbnd) vs ls H Q)
      as [_ Cur].
    destruct (Cur n f e Hn Hl) as (w & Hw & Ht).
    destruct (finv_reachable vs ls H NR) as [_ (_ & F2 & _)].
    destruct (F2 n f e Hn Hl) as (w' & Hw' & Hid).
    rewrite Hw in Hw'; injection Hw' as <-; eauto.
  Qed.

  Theorem quiet_active_done (vs : VState) ls :
    vrun_labels K_eq_dec Σ prog (vinit Σ) ls = Some vs -> NoReact ls -> vquiet K_eq_dec Σ prog vs ->
    forall n f acc w, fibers (vcore vs) n = Some f -> life f = Active Σ acc w ->
      target Σ prog (vcore vs) n = Some w /\ IdealDone (fcomp f) (rho (vcore vs) w).
  Proof.
    intros H NR Q n f acc w Hn Hl.
    destruct (vquiet_current K_eq_dec Σ prog (Confluence.Hwf Σ prog rank Rb Hrank Hbnd) vs ls H Q)
      as [St _].
    pose proof (St n f Hn) as Sf; unfold settled_fiber in Sf; rewrite Hl in Sf.
    split; [exact Sf|].
    destruct (finv_reachable vs ls H NR) as [[_ EP] _].
    pose proof (EP n f Hn) as E; rewrite Hl in E; destruct E as (evs & T & _).
    exists evs; exact T.
  Qed.

  (** ** Two runs end with the same failed fibers *)
  Local Notation Failed := (Classify.Failed Σ).
  Local Notation VLRun := (Classify.VLRun K_eq_dec Σ prog).

  Lemma vrun_snoc (vs0 vs vs' : VState) ls ℓ :
    vrun_labels K_eq_dec Σ prog vs0 ls = Some vs -> ViewFail.vstep K_eq_dec Σ prog vs ℓ = Some vs' ->
    vrun_labels K_eq_dec Σ prog vs0 (ls ++ [ℓ]) = Some vs'.
  Proof.
    revert vs0; induction ls as [|ℓ0 ls IH]; cbn; intros vs0 H Hs.
    - injection H as <-; rewrite Hs; reflexivity.
    - destruct (ViewFail.vstep K_eq_dec Σ prog vs0 ℓ0); [exact (IH _ H Hs) | discriminate].
  Qed.

  Lemma vlrun_reach (vs0 vs : VState) ls0 :
    vrun_labels K_eq_dec Σ prog (vinit Σ) ls0 = Some vs0 -> NoReact ls0 -> VLRun vs0 vs ->
    exists ls, vrun_labels K_eq_dec Σ prog (vinit Σ) ls = Some vs /\ NoReact ls.
  Proof.
    intros H0 N0 R; revert ls0 H0 N0; induction R as [vs|vs ℓ vs1 vs2 Hl Hs R IH]; intros ls0 H0 N0.
    - exists ls0; auto.
    - apply (IH (ls0 ++ [ℓ])); [exact (vrun_snoc _ _ _ ls0 ℓ H0 Hs)|].
      intros ℓ' Hin; apply in_app_or in Hin as [Hin|[<-|[]]]; [exact (N0 ℓ' Hin)|].
      exact (vlife_core_label ℓ Hl).
  Qed.


  Lemma declarer_unique (γ : State) k m m' f f' :
    WF γ -> fibers γ m = Some f -> fibers γ m' = Some f' ->
    In k (cprovs (fcomp f)) -> In k (cprovs (fcomp f')) -> m = m'.
  Proof.
    intros W Hm Hm' Hk Hk'; destruct (Nat.eq_dec m m') as [|Ne]; [assumption|exfalso].
    pose proof (wf_disjoint K_eq_dec Σ prog γ W m m' f f' Ne Hm Hm') as D; unfold fprovs in D.
    rewrite (overlaps_true k _ _ (In_kmem k _ Hk) (In_kmem k _ Hk')) in D; discriminate.
  Qed.

End FailCrux.
