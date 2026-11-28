(** * Confluence with failures: service states (errors/DESIGN.md, section 3)

    The core's service-state confluence ([StateConf.state_confluence])
    assumes no failed fiber at the end only through one lemma: a final
    fiber is Inactive without error, or Active with a complete ideal trace
    ([StateConf.final_fiber]). A failed fiber is Inactive too, with an
    empty accumulator, so nothing else in the proof depends on it. This
    file repeats [StateConf.v] up to [final_evs] with [Final] no longer
    asking for [NoFailed] and [final_fiber] allowing any error mark; the
    proof of [state_confluence] becomes [state_agree], which takes the
    control-level agreement as premises. [vstate_confluence] combines it
    with [FailCrux.vconfluence_failures]: two quiet runs from the same
    reachable state, with failures scoped to their view, leave every bound
    key with service states related by ≃.

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia RelationClasses Permutation Sorted Wf_nat.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering
  Recovery Progress Termination Confluence StateInv Episode.
From CordisErr Require Import ViewFail Classify FailCrux FailConf.
Import ListNotations.

Section StateConfF.
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
  Hypothesis NoSpawn : forall c c', ~ SpawnIn Σ c' (cbody c).
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
  Local Notation itemsF := (@itemsF K K_eq_dec Σ C) (only parsing).
  Local Notation in_itemsF := (@in_itemsF K K_eq_dec Σ C) (only parsing).
  Local Notation itemsF_sorted := (@itemsF_sorted K K_eq_dec Σ C) (only parsing).
  Local Notation Ev := (@Ev K Σ C) (only parsing).
  Local Notation find_prov := (@find_prov K K_eq_dec Σ C) (only parsing).
  Local Notation evOps := (@evOps K K_eq_dec Σ C) (only parsing).
  Local Notation ownIt := (@ownIt K K_eq_dec Σ C) (only parsing).
  Local Notation resolveI := (@resolveI K K_eq_dec Σ C prog) (only parsing).
  Local Notation Tr := (@Tr K K_eq_dec Σ C prog) (only parsing).
  Local Notation tr_ext := (@tr_ext K K_eq_dec Σ C prog) (only parsing).
  Local Notation tr_det := (@tr_det K K_eq_dec Σ C prog Hwb) (only parsing).
  Local Notation tr_drop := (@tr_drop K K_eq_dec Σ C prog) (only parsing).
  Local Notation tr_done_len := (@tr_done_len K K_eq_dec Σ C prog Hwb) (only parsing).
  Local Notation tr_done_eq := (@tr_done_eq K K_eq_dec Σ C prog Hwb) (only parsing).
  Local Notation lv_In := (@lv_In K K_eq_dec) (only parsing).
  Local Notation rho := (@rho K K_eq_dec Σ C) (only parsing).
  Local Notation Corr := (@Corr K K_eq_dec Σ C prog) (only parsing).
  Local Notation NamesFixed := (@NamesFixed K Σ C) (only parsing).
  Local Notation corr_mono := (@corr_mono K K_eq_dec Σ C prog) (only parsing).
  Local Notation upu_tail := (@upu_tail K Σ) (only parsing).
  Local Notation corr_find := (@corr_find K K_eq_dec Σ C prog) (only parsing).
  Local Notation corr_item := (@corr_item K K_eq_dec Σ C prog) (only parsing).
  Local Notation corr_ops := (@corr_ops K K_eq_dec Σ C prog) (only parsing).
  Local Notation upu_unique := (@upu_unique K Σ) (only parsing).
  Local Notation epl := (@epl K K_eq_dec Σ C prog) (only parsing).
  Local Notation EPInv := (@EPInv K K_eq_dec Σ C prog) (only parsing).
  Local Notation ep_keep := (@ep_keep K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation ep_relife := (@ep_relife K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation ep_frame := (@ep_frame K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation ep_op := (@ep_op K K_eq_dec Σ C prog Kb Hwb HTI HCom) (only parsing).
  Local Notation ep_provide := (@ep_provide K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation PInv := (@PInv K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation pinv_init := (@pinv_init K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation step_names := (@step_names K K_eq_dec Σ C prog Kb rank Hrank) (only parsing).
  Local Notation ep_spawn := (@ep_spawn K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation pinv_step := (@pinv_step K K_eq_dec Σ C prog Kb HK rank Hrank Total Hwb HUI HTI HRI HCom) (only parsing).
  Local Notation lrun_pinv := (@lrun_pinv K K_eq_dec Σ C prog Kb HK rank Hrank Total Hwb HUI HTI HRI HCom) (only parsing).
  Local Notation TOp := (@TOp K Σ C) (only parsing).
  Local Notation TProv := (@TProv K Σ C) (only parsing).
  Local Notation TSpawn := (@TSpawn K Σ C) (only parsing).
  Local Notation tr_nil := (@tr_nil K K_eq_dec Σ C prog) (only parsing).
  Local Notation tr_op := (@tr_op K K_eq_dec Σ C prog) (only parsing).
  Local Notation tr_prov := (@tr_prov K K_eq_dec Σ C prog) (only parsing).
  Local Notation tr_spawn := (@tr_spawn K K_eq_dec Σ C prog) (only parsing).
  Local Notation co_nil := (@co_nil K K_eq_dec Σ C prog) (only parsing).
  Local Notation co_op := (@co_op K K_eq_dec Σ C prog) (only parsing).
  Local Notation co_prov := (@co_prov K K_eq_dec Σ C prog) (only parsing).
  Local Notation co_spawn := (@co_spawn K K_eq_dec Σ C prog) (only parsing).
  Local Notation Build_PInv := (@Build_PInv K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation p_s := (@p_s K K_eq_dec Σ C prog Kb) (only parsing).

  Local Notation Itm := (K * nat * nat * (S -> S))%type.
  Local Ltac dif H := match type of H with context [if ?b then _ else _] => destruct b end.

  (** ** Final states *)
  Definition itemsAt (γ : State) (k : K) (n : nat) : list (Op Σ * nat) :=
    match fibers γ n with Some f => itemsF γ k (uacc f) | None => [] end.

  (** A fiber's operations at [k], oldest first. *)
  Definition blockAt (γ : State) (k : K) (n : nat) : list (Op Σ * nat) := rev (itemsAt γ k n).

  Lemma flab_concat (lab : nat -> option nat) λ (F : nat -> list (Op Σ * nat)) l :
    flab onat_eq_dec lab λ (concat (map F l)) = concat (map (fun n => flab onat_eq_dec lab λ (F n)) l).
  Proof. induction l as [|n l IH]; [reflexivity|]; cbn [map concat]; rewrite flab_app, IH; reflexivity. Qed.

  Lemma concat_all_nil {A} (F : nat -> list A) l : (forall n, In n l -> F n = []) -> concat (map F l) = [].
  Proof.
    induction l as [|n l IH]; intros H; cbn; [reflexivity|].
    rewrite (H n (or_introl eq_refl)), IH; [reflexivity|]; intros n' Hn'; exact (H n' (or_intror Hn')).
  Qed.

  Lemma concat_single {A} (F : nat -> list A) l m :
    NoDup l -> In m l -> (forall n, In n l -> n <> m -> F n = []) -> concat (map F l) = F m.
  Proof.
    induction l as [|n l IH]; intros N Hm Hz; [destruct Hm|].
    apply NoDup_cons_iff in N as [Nn N]; cbn.
    destruct Hm as [->|Hm].
    - rewrite concat_all_nil; [apply app_nil_r|].
      intros n' Hn'; apply Hz; [right; exact Hn' | intros ->; contradiction].
    - rewrite (Hz n (or_introl eq_refl)); [cbn; apply IH; auto|].
      + intros n' Hn' Ne; apply Hz; [right; exact Hn' | exact Ne].
      + intros ->; contradiction.
  Qed.

  Lemma flab_const (lab : nat -> option nat) λ0 μ (l : list (Op Σ * nat)) :
    (forall x, In x l -> lab (snd x) = λ0) ->
    flab onat_eq_dec lab μ l = if onat_eq_dec μ λ0 then l else [].
  Proof.
    induction l as [|x l IH]; intros H; [destruct (onat_eq_dec μ λ0); reflexivity|].
    unfold flab in *; cbn; rewrite (H x (or_introl eq_refl)), IH by (intros y Hy; exact (H y (or_intror Hy))).
    destruct (onat_eq_dec λ0 μ), (onat_eq_dec μ λ0); congruence.
  Qed.

  Lemma flab_empty (lab : nat -> option nat) μ (l : list (Op Σ * nat)) :
    (forall x, In x l -> lab (snd x) <> μ) -> flab onat_eq_dec lab μ l = [].
  Proof.
    induction l as [|x l IH]; intros H; [reflexivity|].
    unfold flab in *; cbn; destruct (onat_eq_dec (lab (snd x)) μ) as [E|_];
      [exfalso; exact (H x (or_introl eq_refl) E) | apply IH; intros y Hy; exact (H y (or_intror Hy))].
  Qed.

  Lemma flab_block (γ : State) k n μ :
    SInv γ -> flab onat_eq_dec (tokOwner γ) μ (blockAt γ k n) =
              if onat_eq_dec μ (Some n) then blockAt γ k n else [].
  Proof.
    intros SI; unfold blockAt, itemsAt; destruct (fibers γ n) as [f|] eqn:Hf;
      [|destruct (onat_eq_dec μ (Some n)); reflexivity].
    apply flab_const; intros [a t] Hx; apply in_rev, in_itemsF in Hx as (p & g & I & _).
    exact (tokOwner_spec γ n f k p t g SI Hf I).
  Qed.

  Lemma tokOwner_some (γ : State) t m : tokOwner γ t = Some m -> exists f, fibers γ m = Some f.
  Proof.
    unfold tokOwner; intros E; apply find_some in E as [_ E]; cbv beta in E.
    destruct (fibers γ m) as [f|]; [exists f; reflexivity | discriminate].
  Qed.

  (** At a final state every fiber is Inactive (no items) or Active, with
      an ideal trace run to completion. *)
  Definition Final (γ : State) : Prop :=
    PInv γ /\ settled Σ prog γ.

  Lemma final_fiber (γ : State) n f : Final γ -> fibers γ n = Some f ->
    (exists z, life f = Inactive Σ z) \/ exists acc w evs, life f = Active Σ acc w /\
      Tr (fcomp f) (rho γ w) evs PDone /\ Corr γ (fcomp f) w acc evs.
  Proof.
    intros ([SI EP] & St) Hn.
    destruct (vsettled_shape Σ prog γ n f St Hn) as [_ [[Hl _]|[(acc & w & Hl & _)|(e & Hl)]]].
    - left; eauto.
    - right; pose proof (EP n f Hn) as E; rewrite Hl in E; destruct E as (evs & T & Co).
      exists acc, w, evs; auto.
    - left; eauto.
  Qed.

  (** At a final state every item on a bound key is pending on its binding. *)
  Lemma final_items (γ : State) k b p t :
    Final γ -> binds γ k = Some b -> Item γ k p t -> p = pid b.
  Proof.
    intros Fi Hb (m & fm & g & Hm & I).
    pose proof (sinv_wf γ (p_s _ (proj1 Fi))) as W.
    destruct (final_fiber γ m fm Fi Hm) as [[?z E]|(acc & w & evs & Hl & T & Co)];
      [unfold uacc in I; rewrite E in I; destruct I|].
    unfold uacc in I; rewrite Hl in I; cbn [acc_of] in I; apply in_uops in I.
    pose proof (corr_item γ _ w acc evs k p t g Co I) as Hc.
    destruct (kmem K_eq_dec k (cdeps (fcomp fm))).
    - apply lv_In in Hc.
      assert (Hc' : In (k, p) (view_of Σ (life fm))) by (rewrite Hl; exact Hc).
      destruct (wf_view K_eq_dec Σ prog γ W m fm k p Hm Hc') as (b' & Hb' & <- & _); congruence.
    - assert (Hc' : In (UProv Σ k p) (acc_of (life fm))) by (rewrite Hl; exact Hc).
      destruct (wf_uprov K_eq_dec Σ prog γ W m fm k p Hm Hc') as (b' & Hb' & <- & _); congruence.
  Qed.

  (** At a final state, a bound key's pending list replays like the
      fibers' operations at that key, fiber after fiber. *)
  Lemma final_blocks (γ : State) k b L B s0 s :
    Final γ -> next γ <= B -> binds γ k = Some b -> PendList γ k (pid b) L -> Replay L s0 s ->
    exists s', Replay (concat (map (blockAt γ k) (seq 0 B))) s0 s' /\ s ≃ s'.
  Proof.
    intros Fi HB Hb [Hs HL] R.
    pose proof (p_s _ (proj1 Fi)) as SI.
    apply (replay_shuffle_ex (CoPair k) Hwb (HCom k) onat_eq_dec (tokOwner γ) L _ s0 s
             (pend_cross γ k (pid b) L SI (conj Hs HL))); [|exact R].
    assert (Own : forall a t, In (a, t) L -> exists m f, tokOwner γ t = Some m /\ fibers γ m = Some f).
    { intros a t Hin; apply HL in Hin as [(m & fm & g & Hm & I) _].
      exists m, fm; split; [exact (tokOwner_spec γ m fm k (pid b) t g SI Hm I) | exact Hm]. }
    intros μ; rewrite flab_concat.
    destruct μ as [m|].
    - destruct (fibers γ m) as [fm|] eqn:Hm.
      + rewrite (concat_single _ (seq 0 B) m (seq_NoDup _ _)); cbv beta.
        * rewrite flab_block by exact SI; destruct (onat_eq_dec (Some m) (Some m)) as [_|N]; [|contradiction].
          apply sorted_items_eq.
          -- apply ss_filter; exact Hs.
          -- unfold blockAt, itemsAt; rewrite Hm, map_rev; apply ss_rev_nat, itemsF_sorted.
             exact (proj1 (s_gf _ SI m fm Hm)).
          -- intros [a t]; rewrite in_flab; unfold blockAt, itemsAt; rewrite Hm, <- in_rev, in_itemsF; cbn; split.
             ++ intros [Hin Hlab]; apply HL in Hin as [(m' & fm' & g & Hm' & I) Ho].
                rewrite (tokOwner_spec γ m' fm' k (pid b) t g SI Hm' I) in Hlab; injection Hlab as ->.
                rewrite Hm in Hm'; injection Hm' as <-; exists (pid b), g; auto.
             ++ intros (p & g & I & Ho).
                assert (It : Item γ k p t) by (exists m, fm, g; auto).
                pose proof (final_items γ k b p t Fi Hb It) as Ep; subst p.
                split; [apply HL; auto | exact (tokOwner_spec γ m fm k (pid b) t g SI Hm I)].
        * apply in_seq; pose proof (wf_names K_eq_dec Σ prog γ (sinv_wf γ SI) m fm Hm); lia.
        * intros n _ Hn; rewrite flab_block by exact SI.
          destruct (onat_eq_dec (Some m) (Some n)); [congruence | reflexivity].
      + rewrite concat_all_nil.
        * apply flab_empty; intros [a t] Hin; cbn; destruct (Own a t Hin) as (m' & f' & Ho & Hf').
          rewrite Ho; intros E; injection E as ->; congruence.
        * intros n _; rewrite flab_block by exact SI.
          destruct (onat_eq_dec (Some m) (Some n)) as [E|_]; [|reflexivity].
          injection E as <-; unfold blockAt, itemsAt; rewrite Hm; reflexivity.
    - rewrite concat_all_nil.
      + apply flab_empty; intros [a t] Hin; cbn; destruct (Own a t Hin) as (m' & f' & Ho & _).
        rewrite Ho; discriminate.
      + intros n _; rewrite flab_block by exact SI; destruct (onat_eq_dec None (Some n)); [discriminate | reflexivity].
  Qed.

  Lemma lv_some k (w : @View K) : In k (map fst w) -> exists p, lookup_view K_eq_dec k w = Some p.
  Proof.
    induction w as [|[k' p'] w IH]; cbn; [intros []|].
    unfold keqb; destruct (K_eq_dec k k') as [->|Hne]; [eauto|].
    intros [E|Hin]; [symmetry in E; contradiction | exact (IH Hin)].
  Qed.

  (** ** Final traces coincide *)
  Lemma final_evs (γ1 γ2 : State) :
    Final γ1 -> Final γ2 ->
    (forall n f1 f2, fibers γ1 n = Some f1 -> fibers γ2 n = Some f2 ->
       fcomp f1 = fcomp f2 /\ is_active Σ (life f1) = is_active Σ (life f2)) ->
    (forall k, option_map owner (binds γ1 k) = option_map owner (binds γ2 k)) ->
    forall n f1 f2 acc1 w1 acc2 w2 evs1 evs2,
      fibers γ1 n = Some f1 -> fibers γ2 n = Some f2 ->
      life f1 = Active Σ acc1 w1 -> life f2 = Active Σ acc2 w2 ->
      Tr (fcomp f1) (rho γ1 w1) evs1 PDone -> Corr γ1 (fcomp f1) w1 acc1 evs1 ->
      Tr (fcomp f2) (rho γ2 w2) evs2 PDone -> Corr γ2 (fcomp f2) w2 acc2 evs2 ->
      evs1 = evs2.
  Proof.
    intros F1 F2 Hcomp Hown.
    pose proof (sinv_wf γ1 (p_s _ (proj1 F1))) as W1.
    pose proof (sinv_wf γ2 (p_s _ (proj1 F2))) as W2.
    assert (G : forall r n f1 f2 acc1 w1 acc2 w2 evs1 evs2,
      rank (fcomp f1) < r ->
      fibers γ1 n = Some f1 -> fibers γ2 n = Some f2 ->
      life f1 = Active Σ acc1 w1 -> life f2 = Active Σ acc2 w2 ->
      Tr (fcomp f1) (rho γ1 w1) evs1 PDone -> Corr γ1 (fcomp f1) w1 acc1 evs1 ->
      Tr (fcomp f2) (rho γ2 w2) evs2 PDone -> Corr γ2 (fcomp f2) w2 acc2 evs2 ->
      evs1 = evs2).
    2: { intros n f1 f2 acc1 w1 acc2 w2 evs1 evs2; exact (G (Datatypes.S (rank (fcomp f1))) n f1 f2 acc1 w1 acc2 w2 evs1 evs2 (Nat.lt_succ_diag_r _)). }
    induction r as [|r IH]; intros n f1 f2 acc1 w1 acc2 w2 evs1 evs2 Hr H1 H2 L1 L2 T1 C1 T2 C2; [lia|].
    destruct (Hcomp n f1 f2 H1 H2) as [Hc _].
    rewrite <- Hc in T2.
    apply (tr_done_eq (fcomp f1) (rho γ1 w1) (rho γ2 w2)); [|exact T1 | exact T2].
    intros k Hk.
    (* the views name the current bindings *)
    assert (Hv : forall γ (W : WF γ) n f acc w, fibers γ n = Some f -> life f = Active Σ acc w ->
              In k (cdeps (fcomp f)) ->
              exists b, lookup_view K_eq_dec k w = Some (pid b) /\ binds γ k = Some b).
    { intros γ W n0 f acc w Hn Hl Hk0.
      pose proof (wf_view_keys K_eq_dec Σ prog γ W n0 f Hn ltac:(rewrite Hl; reflexivity)) as Hkeys.
      rewrite Hl in Hkeys; cbn [view_of] in Hkeys; unfold fdeps in Hkeys.
      rewrite <- Hkeys in Hk0; destruct (lv_some k w Hk0) as (p & Hp).
      assert (Hp' : In (k, p) (view_of Σ (life f))) by (rewrite Hl; exact (lv_In k w p Hp)).
      destruct (wf_view K_eq_dec Σ prog γ W n0 f k p Hn Hp') as (b & Hb & <- & _).
      exists b; auto. }
    destruct (Hv γ1 W1 n f1 acc1 w1 H1 L1 Hk) as (b1 & Hw1 & Hb1).
    destruct (Hv γ2 W2 n f2 acc2 w2 H2 L2 ltac:(rewrite <- Hc; exact Hk)) as (b2 & Hw2 & Hb2).
    unfold rho; rewrite Hw1, Hw2.
    assert (Ho : owner b1 = owner b2) by (pose proof (Hown k) as E; rewrite Hb1, Hb2 in E; injection E; auto).
    (* the owner is Active in both, below in rank *)
    destruct (wf_bind K_eq_dec Σ prog γ1 W1 k b1 Hb1) as (fo1 & Hfo1 & _ & Hkp1 & Hup1).
    destruct (wf_bind K_eq_dec Σ prog γ2 W2 k b2 Hb2) as (fo2 & Hfo2 & _ & _ & Hup2).
    rewrite <- Ho in Hfo2.
    destruct (final_fiber γ1 _ fo1 F1 Hfo1) as [[?z E]|(acc1' & w1' & evs1' & L1' & T1' & C1')];
      [rewrite E in Hup1; destruct Hup1|].
    destruct (final_fiber γ2 _ fo2 F2 Hfo2) as [[?z E]|(acc2' & w2' & evs2' & L2' & T2' & C2')];
      [rewrite E in Hup2; destruct Hup2|].
    assert (Hrk : rank (fcomp fo1) < rank (fcomp f1)).
    { apply Hrank; left; exists k; split; [exact (kmem_In K_eq_dec k _ Hkp1) | exact Hk]. }
    pose proof (IH (owner b1) fo1 fo2 acc1' w1' acc2' w2' evs1' evs2' ltac:(lia)
                  Hfo1 Hfo2 L1' L2' T1' C1' T2' C2') as Eev.
    pose proof (wf_uprov_unique K_eq_dec Σ prog γ1 W1 _ fo1 Hfo1) as U1; rewrite L1' in U1, Hup1.
    pose proof (wf_uprov_unique K_eq_dec Σ prog γ2 W2 _ fo2 Hfo2) as U2; rewrite L2' in U2, Hup2.
    destruct (corr_find γ1 _ w1' acc1' evs1' k (pid b1) C1' U1 Hup1) as (s1 & Hi1 & Hf1).
    destruct (corr_find γ2 _ w2' acc2' evs2' k (pid b2) C2' U2 Hup2) as (s2 & Hi2 & Hf2).
    rewrite Hi1, Hi2; rewrite Eev in Hf1; congruence.
  Qed.

  (** ** State confluence *)
  Theorem state_agree (γ1 γ2 : State) :
    Final γ1 -> Final γ2 ->
    (forall n, (exists f, fibers γ1 n = Some f) <-> (exists f, fibers γ2 n = Some f)) ->
    (forall n f1 f2, fibers γ1 n = Some f1 -> fibers γ2 n = Some f2 ->
       fcomp f1 = fcomp f2 /\ is_active Σ (life f1) = is_active Σ (life f2)) ->
    (forall k, option_map owner (binds γ1 k) = option_map owner (binds γ2 k)) ->
    forall k b1 b2, binds γ1 k = Some b1 -> binds γ2 k = Some b2 -> bst b1 ≃ bst b2.
  Proof.
    intros F1 F2 Hex Hcomp Hown k b1 b2 Hb1 Hb2.
    pose proof (proj1 F1) as P1; pose proof (proj1 F2) as P2.
    pose proof (final_evs γ1 γ2 F1 F2 Hcomp Hown) as Hev.
    pose proof (sinv_wf γ1 (p_s _ P1)) as W1.
    pose proof (sinv_wf γ2 (p_s _ P2)) as W2.
    destruct (s_inv _ (p_s _ P1) k b1 Hb1) as (s01 & L1 & s1 & Hi1 & PL1 & Rp1 & E1).
    destruct (s_inv _ (p_s _ P2) k b2 Hb2) as (s02 & L2 & s2 & Hi2 & PL2 & Rp2 & E2).
    assert (Ho : owner b1 = owner b2) by (pose proof (Hown k) as E; rewrite Hb1, Hb2 in E; injection E; auto).
    destruct (wf_bind K_eq_dec Σ prog γ1 W1 k b1 Hb1) as (fo1 & Hfo1 & _ & _ & Hup1).
    destruct (wf_bind K_eq_dec Σ prog γ2 W2 k b2 Hb2) as (fo2 & Hfo2 & _ & _ & Hup2).
    rewrite <- Ho in Hfo2.
    destruct (final_fiber γ1 _ fo1 F1 Hfo1) as [[z E]|(acc1' & w1' & evs1' & L1' & T1' & C1')];
      [rewrite E in Hup1; destruct Hup1|].
    destruct (final_fiber γ2 _ fo2 F2 Hfo2) as [[z E]|(acc2' & w2' & evs2' & L2' & T2' & C2')];
      [rewrite E in Hup2; destruct Hup2|].
    pose proof (Hev _ fo1 fo2 acc1' w1' acc2' w2' evs1' evs2' Hfo1 Hfo2 L1' L2' T1' C1' T2' C2') as Eev.
    pose proof (wf_uprov_unique K_eq_dec Σ prog γ1 W1 _ fo1 Hfo1) as U1; rewrite L1' in U1, Hup1.
    pose proof (wf_uprov_unique K_eq_dec Σ prog γ2 W2 _ fo2 Hfo2) as U2; rewrite L2' in U2, Hup2.
    destruct (corr_find γ1 _ w1' acc1' evs1' k (pid b1) C1' U1 Hup1) as (s1' & Hi1' & Hf1).
    destruct (corr_find γ2 _ w2' acc2' evs2' k (pid b2) C2' U2 Hup2) as (s2' & Hi2' & Hf2).
    assert (s02 = s01) by (rewrite Eev in Hf1; congruence); subst s02.
    set (B := next γ1 + next γ2).
    destruct (final_blocks γ1 k b1 L1 B s01 s1 F1 ltac:(unfold B; lia) Hb1 PL1 Rp1) as (x1 & X1 & Ex1).
    destruct (final_blocks γ2 k b2 L2 B s01 s2 F2 ltac:(unfold B; lia) Hb2 PL2 Rp2) as (x2 & X2 & Ex2).
    assert (EM : map fst (concat (map (blockAt γ1 k) (seq 0 B))) = map fst (concat (map (blockAt γ2 k) (seq 0 B)))).
    { rewrite !concat_map, !map_map; f_equal; apply map_ext_in; intros n _.
      unfold blockAt; rewrite !map_rev; f_equal; unfold itemsAt.
      destruct (fibers γ1 n) as [f1|] eqn:H1; destruct (fibers γ2 n) as [f2|] eqn:H2.
      - pose proof (Hcomp n f1 f2 H1 H2) as [_ Ha].
        destruct (final_fiber γ1 n f1 F1 H1) as [[z1 E1']|(acc1 & w1 & evs1 & L1'' & T1 & C1)];
          destruct (final_fiber γ2 n f2 F2 H2) as [[z2 E2']|(acc2 & w2 & evs2 & L2'' & T2 & C2)].
        + unfold uacc; rewrite E1', E2'; reflexivity.
        + rewrite E1', L2'' in Ha; discriminate.
        + rewrite L1'', E2' in Ha; discriminate.
        + unfold uacc; rewrite L1'', L2''; cbn [acc_of].
          rewrite (corr_ops γ1 _ _ _ _ k C1), (corr_ops γ2 _ _ _ _ k C2); f_equal.
          exact (Hev n f1 f2 acc1 w1 acc2 w2 evs1 evs2 H1 H2 L1'' L2'' T1 C1 T2 C2).
      - destruct (proj1 (Hex n) (ex_intro _ f1 H1)) as [f2 H2']; congruence.
      - destruct (proj2 (Hex n) (ex_intro _ f2 H2)) as [f1 H1']; congruence.
      - reflexivity. }
    destruct (replay_tokens Hwb HTI _ _ s01 x1 EM X1 s01 (reflexivity _)) as (x3 & X3 & E13).
    pose proof (replay_det _ s01 x3 x2 X3 X2) as E32.
    transitivity s1; [exact E1|]; transitivity x1; [exact Ex1|]; transitivity x3; [exact E13|].
    transitivity x2; [exact E32|]; transitivity s2; symmetry; assumption.
  Qed.

  (** ** With failures scoped to their view *)
  Hypothesis HNoRej : forall (k : K) (a b : Op Σ) (ta tb : nat), CoPair k a b -> ta <> tb ->
    forall x x' h ob, run a ta x = Some (x', h, ob) -> run b tb x <> None -> run b tb x' <> None.
  Hypothesis HProv : forall c ρ evs k s P, Tr c ρ evs (PProvide k s P) ->
    In k (cprovs c) /\ find_prov evs k = None.

  Theorem vstate_confluence (vs0 vs1 vs2 : ViewFail.VState Σ) ls0 :
    vrun_labels K_eq_dec Σ prog (vinit Σ) ls0 = Some vs0 -> NoReact ls0 ->
    VLRun K_eq_dec Σ prog vs0 vs1 -> VLRun K_eq_dec Σ prog vs0 vs2 ->
    vquiet K_eq_dec Σ prog vs1 -> vquiet K_eq_dec Σ prog vs2 ->
    forall k b1 b2, binds (vcore Σ vs1) k = Some b1 -> binds (vcore Σ vs2) k = Some b2 -> bst b1 ≃ bst b2.
  Proof.
    intros H0 N0 R1 R2 Q1 Q2.
    destruct (vconfluence_failures K_eq_dec Σ prog Kb HK rank Rb Hrank Hbnd Total Hwb HUI HTI HRI HCom
                HNoRej NoSpawn HProv vs0 vs1 vs2 ls0 H0 N0 R1 R2 Q1 Q2) as (_ & Hex & Hcomp & Hown).
    assert (Fin : forall vs, VLRun K_eq_dec Σ prog vs0 vs -> vquiet K_eq_dec Σ prog vs -> Final (vcore Σ vs)).
    { intros vs R Q.
      destruct (vlrun_reach K_eq_dec Σ prog (fun _ => true) vs0 vs ls0 H0 N0 (fun _ _ _ _ => eq_refl) R)
        as (ls & H & N & _).
      assert (G : forall ws0 ls ws, PInv (vcore Σ ws0) -> vrun_labels K_eq_dec Σ prog ws0 ls = Some ws ->
                  NoReact ls -> PInv (vcore Σ ws)).
      { intros ws0 ls1; revert ws0; induction ls1 as [|ℓ ls1 IH]; cbn; intros ws0 ws P0 Hr NR.
        - injection Hr as <-; exact P0.
        - destruct (ViewFail.vstep K_eq_dec Σ prog ws0 ℓ) as [ws1|] eqn:Hs; [|discriminate].
          apply (IH ws1); [| exact Hr | intros ℓ' Hin; exact (NR ℓ' (or_intror Hin))].
          exact (pinv_step _ _ _ (NR ℓ (or_introl eq_refl)) P0 (vstep_core K_eq_dec Σ prog ws0 ws1 ℓ Hs)). }
      split; [exact (G (vinit Σ) ls vs pinv_init H N)|].
      exact (vquiet_settled K_eq_dec Σ prog Kb rank Rb Hrank Hbnd vs
               (cinv_vreach K_eq_dec Σ prog Kb HK Total NoSpawn vs ls H N) Q). }
    exact (state_agree _ _ (Fin vs1 R1 Q1) (Fin vs2 R2 Q2) Hex Hcomp Hown).
  Qed.
End StateConfF.
