(** * Confluence, part 4: systems with spawn

    Two lifecycle executions from a common state that end quiet with no
    fiber failed agree up to renaming ([spawn_confluence], conclusion
    [Agree]):
    - canonical names ([CN]) name every fiber exactly once: a root keeps its
      name, a child is named by its parent and its position among the
      parent's spawns;
    - the same names occur, with the same components and activity;
    - corresponding fibers own each key, and each key's states are ≃.

    Extra invariant: children of Loading and Active fibers stay alive
    ([SLInv]). The proof is by induction on rank ([corr_step]), since
    whether a parent spawns depends on the outcomes of its operations. *)

From Stdlib Require Import List PeanoNat Bool Lia RelationClasses Permutation Sorted Wf_nat.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering
  Recovery Progress Termination Confluence StateInv Episode StateConf.
Import ListNotations.

Section SpawnConf.
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
  Local Notation itemsAt := (@itemsAt K K_eq_dec Σ C) (only parsing).
  Local Notation blockAt := (@blockAt K K_eq_dec Σ C) (only parsing).
  Local Notation flab_concat := (@flab_concat Σ) (only parsing).
  Local Notation flab_const := (@flab_const Σ) (only parsing).
  Local Notation flab_empty := (@flab_empty Σ) (only parsing).
  Local Notation flab_block := (@flab_block K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation tokOwner_some := (@tokOwner_some K Σ C) (only parsing).
  Local Notation Final := (@Final K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation final_fiber := (@final_fiber K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation final_items := (@final_items K K_eq_dec Σ C prog Kb) (only parsing).
  Local Notation final_blocks := (@final_blocks K K_eq_dec Σ C prog Kb Hwb HCom) (only parsing).
  Local Notation lv_some := (@lv_some K K_eq_dec) (only parsing).
  Local Notation final_evs := (@final_evs K K_eq_dec Σ C prog Kb rank Hrank Hwb) (only parsing).

  Local Notation Itm := (K * nat * nat * (S -> S))%type.
  Local Ltac dif H := match type of H with context [if ?b then _ else _] => destruct b end.

  (** * Layer 3: systems with spawn *)

  (** ** Children of Loading and Active fibers stay alive *)
  Fixpoint spawns (l : list Undo) : list nat :=
    match l with
    | [] => []
    | USpawn _ m :: l' => m :: spawns l'
    | _ :: l' => spawns l'
    end.

  Lemma in_spawns m l : In m (spawns l) <-> In (USpawn Σ m) l.
  Proof.
    induction l as [|u l IH]; cbn; [tauto|].
    destruct u as [k p t g|k p|m']; cbn; rewrite IH; split; intros H; try tauto;
      try (destruct H as [H|H]; [discriminate|tauto]).
    - destruct H as [<-|H]; [left; reflexivity | right; exact H].
    - destruct H as [H|H]; [injection H as ->; left; reflexivity | right; exact H].
  Qed.

  Definition Live (γ : State) (m : nat) : Prop :=
    exists fm, fibers γ m = Some fm /\ disposed fm = false.

  (** The one child that may be gone: the one an Unloading fiber is about to
      withdraw. *)
  Definition HeadSpawn (l : Life) (m : nat) : Prop :=
    exists acc w z, l = Unloading Σ (USpawn Σ m :: acc) w z.

  Record SLInv (γ : State) : Prop := {
    sl_live : forall n f m, fibers γ n = Some f -> In m (spawns (acc_of (life f))) ->
      HeadSpawn (life f) m \/ Live γ m;
    sl_nodup : forall n f, fibers γ n = Some f -> NoDup (spawns (acc_of (life f)));
    sl_par : forall m fm q, fibers γ m = Some fm -> parent fm = Some q -> q < m
  }.

  Lemma live_kept (γ : State) x f m :
    SLInv γ -> fibers γ x = Some f -> In m (spawns (acc_of (life f))) -> ~ HeadSpawn (life f) m ->
    Live γ m.
  Proof. intros SL Hx Hin Hh; destruct (sl_live _ SL x f m Hx Hin) as [H|H]; [contradiction | exact H]. Qed.

  Lemma sl_relife (γ γ1 : State) x f (l : Life) :
    SLInv γ -> fibers γ1 = fibers γ -> fibers γ x = Some f ->
    (forall m, In m (spawns (acc_of l)) -> HeadSpawn l m \/ Live γ m) ->
    NoDup (spawns (acc_of l)) ->
    SLInv (set_life Σ γ1 x f l).
  Proof.
    intros SL E Hx Hl Hnd.
    assert (LV : forall m, Live γ m -> Live (set_life Σ γ1 x f l) m).
    { intros m (fm & Hm & Hd); unfold Live, set_life, set_fiber, with_fibers, fupd; cbn.
      destruct (Nat.eqb_spec m x) as [->|Hne].
      - rewrite Hx in Hm; injection Hm as <-; eexists; split; [reflexivity | exact Hd].
      - rewrite E; exists fm; auto. }
    split.
    - intros n fn m Hn Hin; unfold set_life, set_fiber, with_fibers, fupd in Hn; cbn in Hn.
      destruct (Nat.eqb_spec n x) as [->|Hne].
      + injection Hn as <-; destruct (Hl m Hin) as [H|H]; [left; exact H | right; exact (LV m H)].
      + rewrite E in Hn; destruct (sl_live _ SL n fn m Hn Hin) as [H|H]; [left; exact H | right; exact (LV m H)].
    - intros n fn Hn; unfold set_life, set_fiber, with_fibers, fupd in Hn; cbn in Hn.
      destruct (Nat.eqb_spec n x); [injection Hn as <-; exact Hnd | rewrite E in Hn; exact (sl_nodup _ SL n fn Hn)].
    - intros m fm q Hm Hq; unfold set_life, set_fiber, with_fibers, fupd in Hm; cbn in Hm.
      destruct (Nat.eqb_spec m x) as [->|];
        [injection Hm as <-; exact (sl_par _ SL x f q Hx Hq) | rewrite E in Hm; exact (sl_par _ SL m fm q Hm Hq)].
  Qed.

  (** Re-life with the same spawn items, from a life holding no exception. *)
  Lemma sl_same (γ γ1 : State) x f (l : Life) :
    SLInv γ -> fibers γ1 = fibers γ -> fibers γ x = Some f ->
    (forall m, ~ HeadSpawn (life f) m) -> spawns (acc_of l) = spawns (acc_of (life f)) ->
    SLInv (set_life Σ γ1 x f l).
  Proof.
    intros SL E Hx Hh Es.
    apply (sl_relife γ γ1 x f l SL E Hx); [|rewrite Es; exact (sl_nodup _ SL x f Hx)].
    intros m Hin; right; rewrite Es in Hin; exact (live_kept γ x f m SL Hx Hin (Hh m)).
  Qed.

  Lemma sl_spawn (γ : State) x f c' P' acc w :
    SInv γ -> SLInv γ -> fibers γ x = Some f -> life f = Loading Σ (PSpawn c' P') acc w ->
    SLInv (set_life Σ (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ)
             (Some (mkFiber Σ c' (Some x) false (Inactive Σ None)))))) x f
           (Loading Σ P' (USpawn Σ (next γ) :: acc) w)).
  Proof.
    intros SI SL Hx Hl.
    pose proof (sinv_wf γ SI) as W.
    pose proof (wf_names K_eq_dec Σ prog γ W x f Hx) as Hxlt.
    set (ch := mkFiber Σ c' (Some x) false (Inactive Σ None)).
    set (γ1 := bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ) (Some ch)))).
    assert (F1 : forall m, fibers γ1 m = if Nat.eqb m (next γ) then Some ch else fibers γ m)
      by (intros; reflexivity).
    assert (LV : forall m, Live γ m -> Live γ1 m).
    { intros m (fm & Hm & Hd); exists fm; split; [|exact Hd]; rewrite F1.
      pose proof (wf_names K_eq_dec Σ prog γ W m fm Hm).
      rewrite (proj2 (Nat.eqb_neq m (next γ)) ltac:(lia)); exact Hm. }
    assert (SL1 : SLInv γ1).
    { split.
      - intros n fn m Hn Hin; rewrite F1 in Hn; destruct (Nat.eqb_spec n (next γ)).
        + injection Hn as <-; cbn in Hin; destruct Hin.
        + destruct (sl_live _ SL n fn m Hn Hin) as [H|H]; [left; exact H | right; exact (LV m H)].
      - intros n fn Hn; rewrite F1 in Hn; destruct (Nat.eqb_spec n (next γ));
          [injection Hn as <-; constructor | exact (sl_nodup _ SL n fn Hn)].
      - intros m fm q Hm Hq; rewrite F1 in Hm; destruct (Nat.eqb_spec m (next γ)) as [->|].
        + injection Hm as <-; cbn in Hq; injection Hq as <-; exact Hxlt.
        + exact (sl_par _ SL m fm q Hm Hq). }
    apply (sl_relife γ1 γ1 x f); [exact SL1 | reflexivity | | |].
    - rewrite F1, (proj2 (Nat.eqb_neq x (next γ)) ltac:(lia)); exact Hx.
    - intros m [<-|Hin]; right.
      + exists ch; split; [rewrite F1, Nat.eqb_refl; reflexivity | reflexivity].
      + apply LV; apply (live_kept γ x f m SL Hx); [rewrite Hl; exact Hin|].
        rewrite Hl; intros (a1 & w1 & z1 & E); discriminate.
    - cbn [acc_of spawns]; constructor.
      + intros Hin; apply in_spawns in Hin.
        assert (Hin' : In (USpawn Σ (next γ)) (acc_of (life f))) by (rewrite Hl; exact Hin).
        pose proof (wf_spawn_lt K_eq_dec Σ prog γ W x f (next γ) Hx Hin'); lia.
      + pose proof (sl_nodup _ SL x f Hx) as N; rewrite Hl in N; exact N.
  Qed.

  Theorem sl_step (γ γ' : State) ℓ :
    PInv γ -> SLInv γ -> is_lifecycle ℓ -> step γ ℓ = Some γ' -> SLInv γ'.
  Proof.
    intros [SI EP] SL (n0 & Hlab) H.
    pose proof (sinv_wf γ SI) as W.
    pose proof (c0_t K_eq_dec Σ prog Kb γ (s_c _ SI)) as TI.
    pose proof (t_so K_eq_dec Σ prog Kb γ TI) as SO.
    assert (NotHead : forall f, (forall acc w z u, life f <> Unloading Σ (u :: acc) w z) ->
                        forall m, ~ HeadSpawn (life f) m).
    { intros f Hf m (acc & w & z & E); exact (Hf acc w z _ E). }
    destruct ℓ as [c|x|x|x|x|x|x|x|x|x|x|x i|x];
      try (exfalso; cbn in Hlab; intuition discriminate); cbn [step] in H.
    - (* LBegin *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]|P acc w|acc w|acc w z] eqn:Hl;
        repeat match type of H with context [match ?e with _ => _ end] => destruct e end;
        try discriminate; injection H as <-.
      apply (sl_relife γ γ x f); [exact SL | reflexivity | exact Hx | intros m [] | constructor].
    - (* LStep *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      dif H; [injection H as <- | discriminate].
      assert (Nh : forall m, ~ HeadSpawn (life f) m) by (apply NotHead; rewrite Hl; discriminate).
      assert (Same : forall γ1 (l : Life), fibers γ1 = fibers γ -> spawns (acc_of l) = spawns acc ->
                SLInv (set_life Σ γ1 x f l)).
      { intros γ1 l E Es; apply (sl_same γ γ1 x f l SL E Hx Nh); rewrite Hl; exact Es. }
      destruct P as [| |k a κ|k s P'|c P'].
      + apply Same; reflexivity.
      + apply Same; reflexivity.
      + rewrite (load_step_op K_eq_dec Σ prog γ x f k a κ acc w).
        destruct (op_binding K_eq_dec Σ prog γ x f k w) as [b|]; [|apply Same; reflexivity].
        destruct (run a (next γ) (bst b)) as [[[s' g] o]|]; apply Same; reflexivity.
      + cbn [load_step].
        destruct (kmem K_eq_dec k (provs Σ (prog (fcomp f)))); [|apply Same; reflexivity].
        destruct (binds γ k); apply Same; reflexivity.
      + cbn [load_step]; destruct (conflict K_eq_dec Σ prog γ c); [apply Same; reflexivity|].
        exact (sl_spawn γ x f c P' acc w SI SL Hx Hl).
    - (* LDivert *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      dif H; [discriminate | injection H as <-].
      apply (sl_same γ γ x f); [exact SL | reflexivity | exact Hx | apply NotHead; rewrite Hl; discriminate
                               | rewrite Hl; reflexivity].
    - (* LLeave *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      dif H; [discriminate | injection H as <-].
      apply (sl_same γ γ x f); [exact SL | reflexivity | exact Hx | apply NotHead; rewrite Hl; discriminate
                               | rewrite Hl; reflexivity].
    - (* LUndo *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      destruct (undo_step_shape K_eq_dec Σ γ γ' x f u acc w z H) as (γ1 & -> & E).
      pose proof (sl_nodup _ SL x f Hx) as N; rewrite Hl in N.
      assert (Nt : NoDup (spawns acc) /\ (forall m, u = USpawn Σ m -> ~ In m (spawns acc))).
      { destruct u as [k p t g|k p|m0]; cbn in N; [split; [exact N | discriminate] | split; [exact N | discriminate]|].
        apply NoDup_cons_iff in N as [N1 N2]; split; [exact N2 | intros m [= <-]; exact N1]. }
      apply (sl_relife γ γ1 x f); [exact SL | exact E | exact Hx | | exact (proj1 Nt)].
      intros m Hin; right; apply (live_kept γ x f m SL Hx).
      + rewrite Hl; destruct u as [k p t g|k p|m0]; cbn; [exact Hin | exact Hin | right; exact Hin].
      + rewrite Hl; intros (a1 & w1 & z1 & E1); injection E1 as Eu _ _ _.
        exact (proj2 Nt m Eu Hin).
    - (* LRetireChild *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|[|u acc] w z] eqn:Hl; try discriminate.
      destruct u as [k p t g|k p|m0]; try discriminate.
      destruct (fibers γ m0) as [g|] eqn:Hm0; [|discriminate].
      dif H; [discriminate | injection H as <-].
      assert (Hx0 : In (USpawn Σ m0) (acc_of (life f))) by (rewrite Hl; left; reflexivity).
      pose proof (SO x f m0 g Hx Hx0 Hm0) as Pg.
      assert (F : forall m, fibers (set_fiber Σ γ m0 (mkFiber Σ (fcomp g) (parent g) true (life g))) m =
                  if Nat.eqb m m0 then Some (mkFiber Σ (fcomp g) (parent g) true (life g)) else fibers γ m)
        by (intros; reflexivity).
      assert (LV : forall m, m <> m0 -> Live γ m ->
                 Live (set_fiber Σ γ m0 (mkFiber Σ (fcomp g) (parent g) true (life g))) m).
      { intros m Hne (fm & Hm & Hd); exists fm; rewrite F, (proj2 (Nat.eqb_neq m m0) Hne); auto. }
      split.
      + intros n fn m Hn Hin; rewrite F in Hn; destruct (Nat.eqb_spec n m0) as [->|Hne].
        * injection Hn as <-; cbn in Hin.
          destruct (sl_live _ SL m0 g m Hm0 Hin) as [Hh|Hlv]; [left; exact Hh | right].
          apply LV; [|exact Hlv]; intros ->.
          destruct Hlv as (fm & Hm & _); rewrite Hm0 in Hm; injection Hm as <-.
          apply in_spawns in Hin; pose proof (SO m0 g m0 g Hm0 Hin Hm0) as Pm.
          pose proof (sl_par _ SL m0 g m0 Hm0 Pm); lia.
        * destruct (sl_live _ SL n fn m Hn Hin) as [Hh|Hlv]; [left; exact Hh|].
          destruct (Nat.eq_dec m m0) as [->|Hne'].
          -- apply in_spawns in Hin; pose proof (SO n fn m0 g Hn Hin Hm0) as Pn.
             rewrite Pg in Pn; injection Pn as <-; rewrite Hx in Hn; injection Hn as <-.
             left; rewrite Hl; do 3 eexists; reflexivity.
          -- right; exact (LV m Hne' Hlv).
      + intros n fn Hn; rewrite F in Hn; destruct (Nat.eqb_spec n m0) as [->|];
          [injection Hn as <-; exact (sl_nodup _ SL m0 g Hm0) | exact (sl_nodup _ SL n fn Hn)].
      + intros m fm q Hm Hq; rewrite F in Hm; destruct (Nat.eqb_spec m m0) as [->|];
          [injection Hm as <-; exact (sl_par _ SL m0 g q Hm0 Hq) | exact (sl_par _ SL m fm q Hm Hq)].
    - (* LUnloaded *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|[|u acc] w z] eqn:Hl; try discriminate; injection H as <-.
      apply (sl_relife γ γ x f); [exact SL | reflexivity | exact Hx | intros m [] | constructor].
    - (* LRemove *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      destruct (disposed f) eqn:Hd; [|discriminate].
      dif H; [injection H as <- | discriminate].
      assert (F : forall m, fibers (with_fibers Σ γ (fupd Σ (fibers γ) x None)) m =
                  if Nat.eqb m x then None else fibers γ m) by (intros; reflexivity).
      split.
      + intros n fn m Hn Hin; rewrite F in Hn; destruct (Nat.eqb_spec n x); [discriminate|].
        destruct (sl_live _ SL n fn m Hn Hin) as [Hh|(fm & Hm & Hdm)]; [left; exact Hh | right].
        destruct (Nat.eqb_spec m x) as [->|Hne].
        * rewrite Hx in Hm; injection Hm as <-; congruence.
        * exists fm; rewrite F, (proj2 (Nat.eqb_neq m x) Hne); auto.
      + intros n fn Hn; rewrite F in Hn; destruct (Nat.eqb_spec n x); [discriminate | exact (sl_nodup _ SL n fn Hn)].
      + intros m fm q Hm Hq; rewrite F in Hm; destruct (Nat.eqb_spec m x); [discriminate | exact (sl_par _ SL m fm q Hm Hq)].
  Qed.

  Lemma lrun_sl (γ0 γ : State) : PInv γ0 -> SLInv γ0 -> LRun K_eq_dec Σ prog γ0 γ -> PInv γ /\ SLInv γ.
  Proof.
    intros P S R; induction R as [γ|γ ℓ γ1 γ2 Hlc Hs _ IH]; [auto|].
    exact (IH (pinv_step γ γ1 ℓ (lifecycle_not_react ℓ Hlc) P Hs) (sl_step γ γ1 ℓ P S Hlc Hs)).
  Qed.

  (** ** Canonical names

      A root keeps its name; a child is named by its parent's canonical
      name and its position among the parent's spawns, oldest first. *)
  Inductive CName : Type := CRoot (n : nat) | CChild (x : CName) (j : nat).

  Definition SpawnAt (l : list Undo) (m j : nat) : Prop := nth_error (rev (spawns l)) j = Some m.

  (** [rt] labels the roots: [CRoot (rt n)] names the root [n]. Runs from
      one start state label a root by its own name ([rt] the identity);
      runs with different schedules label it by its insertion index
      ([Dynamic.v]). *)
  Inductive CN (rt : nat -> nat) (γ : State) : nat -> CName -> Prop :=
  | cn_root n f : fibers γ n = Some f -> parent f = None -> CN rt γ n (CRoot (rt n))
  | cn_child n f p fp x j : fibers γ n = Some f -> parent f = Some p -> fibers γ p = Some fp ->
      CN rt γ p x -> SpawnAt (acc_of (life fp)) n j -> CN rt γ n (CChild x j).

  (** Distinct roots carry distinct labels. *)
  Definition RootInj (rt : nat -> nat) (γ : State) : Prop :=
    forall n n' f f', fibers γ n = Some f -> parent f = None ->
      fibers γ n' = Some f' -> parent f' = None -> rt n = rt n' -> n = n'.

  Lemma cn_present rt (γ : State) n x : CN rt γ n x -> exists f, fibers γ n = Some f.
  Proof. intros H; destruct H; eauto. Qed.

  Lemma cn_inj rt (γ : State) n n' x : RootInj rt γ -> CN rt γ n x -> CN rt γ n' x -> n = n'.
  Proof.
    intros RI H; revert n'; induction H as [n f Hn Hp|n f p fp x j Hn Hp Hfp Hx IH Hj]; intros n' H'.
    - inversion H'; subst; eapply RI; eauto using eq_sym.
    - inversion H' as [|n'' f' p' fp' x' j' Hn' Hp' Hfp' Hx' Hj']; subst.
      pose proof (IH p' Hx') as <-; rewrite Hfp in Hfp'; injection Hfp' as <-.
      unfold SpawnAt in Hj, Hj'; congruence.
  Qed.

  Lemma cn_fun rt (γ : State) n x x' : SLInv γ -> CN rt γ n x -> CN rt γ n x' -> x = x'.
  Proof.
    intros SL H; revert x'; induction H as [n f Hn Hp|n f p fp x j Hn Hp Hfp Hx IH Hj]; intros x' H'.
    - inversion H' as [n' f' Hn' Hp'|n' f' p' fp' x'' j' Hn' Hp' Hfp' Hx' Hj']; subst; [reflexivity|].
      rewrite Hn in Hn'; injection Hn' as <-; congruence.
    - inversion H' as [n' f' Hn' Hp'|n' f' p' fp' x'' j' Hn' Hp' Hfp' Hx' Hj']; subst.
      + rewrite Hn in Hn'; injection Hn' as <-; congruence.
      + rewrite Hn in Hn'; injection Hn' as <-; rewrite Hp in Hp'; injection Hp' as <-.
        rewrite Hfp in Hfp'; injection Hfp' as <-.
        rewrite (IH x'' Hx'); f_equal.
        pose proof (NoDup_rev (sl_nodup _ SL p fp Hfp)) as N.
        unfold SpawnAt in Hj, Hj'.
        apply (proj1 (NoDup_nth_error _) N); [apply nth_error_Some; congruence | congruence].
  Qed.

  Lemma cn_total rt (γ : State) n f : SInv γ -> SLInv γ -> fibers γ n = Some f -> exists x, CN rt γ n x.
  Proof.
    intros SI SL; revert f; induction n as [n IH] using (well_founded_induction lt_wf); intros f Hn.
    destruct (parent f) as [p|] eqn:Hp; [|exists (CRoot (rt n)); exact (cn_root rt γ n f Hn Hp)].
    pose proof (sinv_wf γ SI) as W.
    destruct (wf_parent K_eq_dec Σ prog γ W n f p Hn Hp) as (fp & Hfp & _ & Hin).
    destruct (IH p (sl_par _ SL n f p Hn Hp) fp Hfp) as [x Hx].
    apply in_spawns, in_rev, In_nth_error in Hin as [j Hj].
    exists (CChild x j); exact (cn_child rt γ n f p fp x j Hn Hp Hfp Hx Hj).
  Qed.

  (** ** Spawn events against spawn items *)
  Fixpoint evsp (evs : list Ev) : list C :=
    match evs with [] => [] | @Episode.TSpawn _ _ _ c' :: e => c' :: evsp e | _ :: e => evsp e end.

  Definition CompAt (γ : State) (m : nat) (c' : C) : Prop :=
    forall fm, fibers γ m = Some fm -> fcomp fm = c'.

  Lemma corr_f2 (γ : State) c w acc evs :
    Corr γ c w acc evs -> Forall2 (CompAt γ) (spawns acc) (evsp evs).
  Proof.
    intros H; induction H as [|k p t g a acc evs H IH Ho Hr|k p s acc evs H IH Hi|m c' acc evs H IH Hc];
      cbn; [constructor | exact IH | exact IH | constructor; [exact Hc | exact IH]].
  Qed.

  Lemma f2_rev {A B} (R : A -> B -> Prop) l1 l2 : Forall2 R l1 l2 -> Forall2 R (rev l1) (rev l2).
  Proof.
    intros H; induction H as [|x y l1 l2 Hxy H IH]; cbn; [constructor|].
    apply Forall2_app; [exact IH | constructor; [exact Hxy | constructor]].
  Qed.

  Lemma f2_nth {A B} (R : A -> B -> Prop) l1 l2 i a :
    Forall2 R l1 l2 -> nth_error l1 i = Some a -> exists b, nth_error l2 i = Some b /\ R a b.
  Proof.
    intros H; revert i; induction H as [|x y l1 l2 Hxy H IH]; intros [|i] E; cbn in E; try discriminate.
    - injection E as <-; exists y; split; [reflexivity | exact Hxy].
    - exact (IH i E).
  Qed.

  Lemma f2_nth_r {A B} (R : A -> B -> Prop) l1 l2 i b :
    Forall2 R l1 l2 -> nth_error l2 i = Some b -> exists a, nth_error l1 i = Some a /\ R a b.
  Proof.
    intros H; revert i; induction H as [|x y l1 l2 Hxy H IH]; intros [|i] E; cbn in E; try discriminate.
    - injection E as <-; exists x; split; [reflexivity | exact Hxy].
    - exact (IH i E).
  Qed.

  Lemma tr_sub c ρ evs P : Tr c ρ evs P -> Sub Σ P (cbody c).
  Proof.
    intros H; induction H as [|evs k a κ s0 s1 s' g o T IH R Rp X|evs k s P T IH|evs c' P T IH].
    - apply sub_refl.
    - eapply Sub_trans; [|exact IH]; eapply sub_op; apply sub_refl.
    - eapply Sub_trans; [|exact IH]; apply sub_prov; apply sub_refl.
    - eapply Sub_trans; [|exact IH]; apply sub_spawn; apply sub_refl.
  Qed.

  Lemma tr_spawnin c ρ evs P c' : Tr c ρ evs P -> In c' (evsp evs) -> SpawnIn Σ c' (cbody c).
  Proof.
    intros H; induction H as [|evs k a κ s0 s1 s' g o T IH R Rp X|evs k s P T IH|evs c'' P T IH]; cbn; intros Hin.
    - destruct Hin.
    - exact (IH Hin).
    - exact (IH Hin).
    - destruct Hin as [<-|Hin]; [|exact (IH Hin)].
      eapply SpawnIn_Sub; [exact (tr_sub _ _ _ _ T) | constructor].
  Qed.

  Lemma view_bind (γ : State) n f acc w k :
    WF γ -> fibers γ n = Some f -> life f = Active Σ acc w -> In k (cdeps (fcomp f)) ->
    exists b, lookup_view K_eq_dec k w = Some (pid b) /\ binds γ k = Some b.
  Proof.
    intros W Hn Hl Hk.
    pose proof (wf_view_keys K_eq_dec Σ prog γ W n f Hn ltac:(rewrite Hl; reflexivity)) as Hkeys.
    rewrite Hl in Hkeys; cbn [view_of] in Hkeys; unfold fdeps in Hkeys.
    rewrite <- Hkeys in Hk; destruct (lv_some k w Hk) as (p & Hp).
    assert (Hp' : In (k, p) (view_of Σ (life f))) by (rewrite Hl; exact (lv_In k w p Hp)).
    destruct (wf_view K_eq_dec Σ prog γ W n f k p Hn Hp') as (b & Hb & <- & _).
    exists b; auto.
  Qed.

  (** ** Corresponding final states *)
  Definition FinalS (γ : State) : Prop := Final γ /\ SLInv γ.

  Definition Corresp (la lb : nat -> nat) (γa γb : State) (r : nat) : Prop :=
    forall x na fa, CN la γa na x -> fibers γa na = Some fa -> rank (fcomp fa) < r ->
      exists nb fb, CN lb γb nb x /\ fibers γb nb = Some fb /\ fcomp fb = fcomp fa /\
        is_active Σ (life fb) = is_active Σ (life fa) /\
        forall acca wa evsa accb wb evsb, life fa = Active Σ acca wa -> life fb = Active Σ accb wb ->
          Tr (fcomp fa) (rho γa wa) evsa PDone -> Corr γa (fcomp fa) wa acca evsa ->
          Tr (fcomp fb) (rho γb wb) evsb PDone -> Corr γb (fcomp fb) wb accb evsb -> evsa = evsb.

  (** Every root of [γa] has a root of [γb] with the same label and component. *)
  Definition RootsMatch (la lb : nat -> nat) (γa γb : State) : Prop :=
    forall n fa, fibers γa n = Some fa -> parent fa = None ->
      exists nb fb, fibers γb nb = Some fb /\ parent fb = None /\ lb nb = la n /\ fcomp fb = fcomp fa.

  (** Two fibers with the same component, whose lower-ranked fibers
      correspond, have the same activity and the same trace. *)
  Lemma corr_pair la lb (γa γb : State) r na fa nb fb :
    FinalS γa -> FinalS γb -> Corresp la lb γa γb r -> Corresp lb la γb γa r ->
    fibers γa na = Some fa -> fibers γb nb = Some fb -> fcomp fb = fcomp fa -> rank (fcomp fa) <= r ->
    is_active Σ (life fb) = is_active Σ (life fa) /\
    forall acca wa evsa accb wb evsb, life fa = Active Σ acca wa -> life fb = Active Σ accb wb ->
      Tr (fcomp fa) (rho γa wa) evsa PDone -> Corr γa (fcomp fa) wa acca evsa ->
      Tr (fcomp fb) (rho γb wb) evsb PDone -> Corr γb (fcomp fb) wb accb evsb -> evsa = evsb.
  Proof.
    intros Fa Fb IHab IHba Ha Hb Hc Hr.
    pose proof (p_s _ (proj1 (proj1 Fa))) as SIa; pose proof (p_s _ (proj1 (proj1 Fb))) as SIb.
    pose proof (proj1 (proj2 (proj1 Fa))) as Sta; pose proof (proj1 (proj2 (proj1 Fb))) as Stb.
    pose proof (proj2 (proj2 (proj1 Fa))) as NFa; pose proof (proj2 (proj2 (proj1 Fb))) as NFb.
    pose proof (sinv_wf γa SIa) as Wa; pose proof (sinv_wf γb SIb) as Wb.
    assert (Prov : forall lx ly (γx γy : State), SInv γx -> SLInv γx -> Corresp lx ly γx γy r ->
              forall k c, rank c <= r -> In k (cdeps c) ->
              (exists m fm, fibers γx m = Some fm /\ is_active Σ (life fm) = true /\ In k (cprovs (fcomp fm))) ->
              exists m fm, fibers γy m = Some fm /\ is_active Σ (life fm) = true /\ In k (cprovs (fcomp fm))).
    { intros lx ly γx γy Sx SLx IH k c Hrc Hk (m & fm & Hm & Ham & Hk').
      assert (Hrk : rank (fcomp fm) < r).
      { pose proof (Hrank (fcomp fm) c (or_introl (ex_intro _ k (conj Hk' Hk)))); lia. }
      destruct (cn_total lx γx m fm Sx SLx Hm) as [y Hy].
      destruct (IH y m fm Hy Hm Hrk) as (mb & fmb & _ & Hmb & Hcb & Hab & _).
      exists mb, fmb; rewrite Hcb, Hab; auto. }
    pose proof (active_iff K_eq_dec Σ prog Kb γa na fa (s_c _ SIa) Sta NFa Ha) as Aa.
    pose proof (active_iff K_eq_dec Σ prog Kb γb nb fb (s_c _ SIb) Stb NFb Hb) as Ab.
    rewrite Hc in Ab.
    split.
    - destruct (is_active Σ (life fa)) eqn:Ea, (is_active Σ (life fb)) eqn:Eb; try reflexivity.
      + apply (proj2 Ab); intros k Hk.
        apply (Prov la lb γa γb SIa (proj2 Fa) IHab k (fcomp fa) Hr Hk); exact (proj1 Aa eq_refl k Hk).
      + symmetry; apply (proj2 Aa); intros k Hk.
        apply (Prov lb la γb γa SIb (proj2 Fb) IHba k (fcomp fa) Hr Hk); exact (proj1 Ab eq_refl k Hk).
    - intros acca wa evsa accb wb evsb La Lb Ta Coa Tb Cob.
      rewrite Hc in Tb.
      apply (tr_done_eq (fcomp fa) (rho γa wa) (rho γb wb)); [|exact Ta | exact Tb].
      intros k Hk.
      destruct (view_bind γa na fa acca wa k Wa Ha La Hk) as (ba & Hwa & Hba).
      destruct (view_bind γb nb fb accb wb k Wb Hb Lb ltac:(rewrite Hc; exact Hk)) as (bb & Hvb & Hbb).
      unfold rho; rewrite Hwa, Hvb.
      destruct (wf_bind K_eq_dec Σ prog γa Wa k ba Hba) as (foa & Hfoa & _ & Hkpa & Hupa).
      destruct (final_fiber γa _ foa (proj1 Fa) Hfoa) as [E|(acco & wo & evso & Lo & To & Co)];
        [rewrite E in Hupa; destruct Hupa|].
      assert (Hrk : rank (fcomp foa) < r).
      { pose proof (Hrank (fcomp foa) (fcomp fa)
          (or_introl (ex_intro _ k (conj (kmem_In K_eq_dec k _ Hkpa) Hk)))); lia. }
      destruct (cn_total la γa _ foa SIa (proj2 Fa) Hfoa) as [y Hy].
      destruct (IHab y _ foa Hy Hfoa Hrk) as (ob & fob & _ & Hfob & Hcob & Haob & Hevo).
      rewrite Lo in Haob; cbn in Haob.
      destruct (final_fiber γb ob fob (proj1 Fb) Hfob) as [E|(accob & wob & evsob & Lob & Tob & Cob')];
        [rewrite E in Haob; discriminate|].
      assert (Hown : owner bb = ob).
      { assert (Hkb : In k (cprovs (fcomp fob))) by (rewrite Hcob; exact (kmem_In K_eq_dec k _ Hkpa)).
        pose proof (proj2 (owner_iff K_eq_dec Σ prog Kb γb k ob (s_c _ SIb) Stb NFb)
          (ex_intro _ fob (conj Hfob (conj Haob Hkb)))) as E.
        rewrite Hbb in E; injection E; auto. }
      destruct (wf_bind K_eq_dec Σ prog γb Wb k bb Hbb) as (fob' & Hfob' & _ & _ & Hupb).
      rewrite Hown, Hfob in Hfob'; injection Hfob' as <-.
      pose proof (Hevo acco wo evso accob wob evsob Lo Lob To Co Tob Cob') as Eev.
      pose proof (wf_uprov_unique K_eq_dec Σ prog γa Wa _ foa Hfoa) as Ua; rewrite Lo in Ua, Hupa.
      pose proof (wf_uprov_unique K_eq_dec Σ prog γb Wb _ fob Hfob) as Ub; rewrite Lob in Ub, Hupb.
      destruct (corr_find γa _ wo acco evso k (pid ba) Co Ua Hupa) as (s1 & Hi1 & Hf1).
      destruct (corr_find γb _ wob accob evsob k (pid bb) Cob' Ub Hupb) as (s2 & Hi2 & Hf2).
      rewrite Hi1, Hi2; rewrite Eev in Hf1; congruence.
  Qed.

  Lemma corr_step la lb (γa γb : State) r :
    FinalS γa -> FinalS γb -> RootsMatch la lb γa γb ->
    Corresp la lb γa γb r -> Corresp lb la γb γa r -> Corresp la lb γa γb (Datatypes.S r).
  Proof.
    intros Fa Fb RM IHab IHba x na fa CNa Ha Hr.
    assert (Hr' : rank (fcomp fa) <= r) by lia.
    pose proof (p_s _ (proj1 (proj1 Fb))) as SIb.
    assert (Find : exists nb fb, CN lb γb nb x /\ fibers γb nb = Some fb /\ fcomp fb = fcomp fa).
    { inversion CNa as [n f Hn Hp|n f p fp y j Hn Hp Hfp Hy Hj]; subst; rewrite Ha in Hn; injection Hn as <-.
      - destruct (RM na fa Ha Hp) as (nb & fb & Hfb & Hpb & Hl & Hcb).
        exists nb, fb; split; [rewrite <- Hl; exact (cn_root lb γb nb fb Hfb Hpb) | auto].
      - destruct (final_fiber γa p fp (proj1 Fa) Hfp) as [E|(accp & wp & evp & Lp & Tp & Cp)].
        { unfold SpawnAt in Hj; rewrite E in Hj; cbn in Hj; destruct j; discriminate. }
        unfold SpawnAt in Hj; rewrite Lp in Hj; cbn [acc_of] in Hj.
        destruct (f2_nth _ _ _ j na (f2_rev _ _ _ (corr_f2 _ _ _ _ _ Cp)) Hj) as (c' & Hc' & Hca).
        pose proof (Hca fa Ha) as Ec.
        assert (Hsp : SpawnIn Σ c' (cbody (fcomp fp))).
        { apply (tr_spawnin _ _ _ _ c' Tp); apply (proj2 (in_rev _ _)); exact (nth_error_In _ _ Hc'). }
        assert (Hrp : rank (fcomp fp) < r).
        { pose proof (Hrank (fcomp fp) c' (or_intror (or_introl Hsp))); rewrite <- Ec in *; lia. }
        destruct (IHab y p fp Hy Hfp Hrp) as (pb & fpb & CNpb & Hfpb & Hcpb & Hapb & Hevp).
        rewrite Lp in Hapb; cbn in Hapb.
        destruct (final_fiber γb pb fpb (proj1 Fb) Hfpb) as [E|(accpb & wpb & evpb & Lpb & Tpb & Cpb)];
          [rewrite E in Hapb; discriminate|].
        pose proof (Hevp accp wp evp accpb wpb evpb Lp Lpb Tp Cp Tpb Cpb) as Eev.
        rewrite Eev in Hc'.
        destruct (f2_nth_r _ _ _ j c' (f2_rev _ _ _ (corr_f2 _ _ _ _ _ Cpb)) Hc') as (nb & Hnb & Hcb).
        assert (Inb : In nb (spawns (acc_of (life fpb)))).
        { rewrite Lpb; apply (proj2 (in_rev _ _)); exact (nth_error_In _ _ Hnb). }
        destruct (sl_live _ (proj2 Fb) pb fpb nb Hfpb Inb) as [(a1 & w1 & z1 & E)|(fb & Hfb & _)];
          [rewrite Lpb in E; discriminate|].
        pose proof (t_so K_eq_dec Σ prog Kb γb (c0_t K_eq_dec Σ prog Kb γb (s_c _ SIb)) pb fpb nb fb Hfpb
                      (proj1 (in_spawns _ _) Inb) Hfb) as Hpar.
        exists nb, fb; split; [|split; [exact Hfb | rewrite (Hcb fb Hfb); exact (eq_sym Ec)]].
        apply (cn_child lb γb nb fb pb fpb y j Hfb Hpar Hfpb CNpb); unfold SpawnAt; rewrite Lpb; exact Hnb. }
    destruct Find as (nb & fb & CNb & Hb & Hc).
    destruct (corr_pair la lb γa γb r na fa nb fb Fa Fb IHab IHba Ha Hb Hc Hr') as [Hact Htr].
    exists nb, fb; auto.
  Qed.

  Lemma corresp_all l1 l2 (γ1 γ2 : State) :
    FinalS γ1 -> FinalS γ2 -> RootsMatch l1 l2 γ1 γ2 -> RootsMatch l2 l1 γ2 γ1 ->
    forall r, Corresp l1 l2 γ1 γ2 r /\ Corresp l2 l1 γ2 γ1 r.
  Proof.
    intros F1 F2 R12 R21 r; induction r as [|r [IH12 IH21]].
    - split; intros x na fa _ _ Hr; lia.
    - split; [exact (corr_step l1 l2 γ1 γ2 r F1 F2 R12 IH12 IH21) | exact (corr_step l2 l1 γ2 γ1 r F2 F1 R21 IH21 IH12)].
  Qed.

  (** ** Roots persist *)
  Definition RootKeep (γ γ' : State) : Prop :=
    (forall m f', fibers γ' m = Some f' -> parent f' = None ->
       exists f, fibers γ m = Some f /\ parent f = None /\ fcomp f = fcomp f' /\ disposed f = disposed f') /\
    (forall m f, fibers γ m = Some f -> parent f = None -> disposed f = false ->
       exists f', fibers γ' m = Some f' /\ parent f' = None /\ disposed f' = false).

  Lemma rk_refl (γ : State) : RootKeep γ γ.
  Proof. split; intros m f H P; [exists f; auto | intros D; exists f; auto]. Qed.

  Lemma rk_trans (γ1 γ2 γ3 : State) : RootKeep γ1 γ2 -> RootKeep γ2 γ3 -> RootKeep γ1 γ3.
  Proof.
    intros [A1 B1] [A2 B2]; split.
    - intros m f3 H3 P3; destruct (A2 m f3 H3 P3) as (f2 & H2 & P2 & C2 & D2).
      destruct (A1 m f2 H2 P2) as (f1 & H1 & P1 & C1 & D1); exists f1; repeat split; congruence.
    - intros m f1 H1 P1 D1; destruct (B1 m f1 H1 P1 D1) as (f2 & H2 & P2 & D2); exact (B2 m f2 H2 P2 D2).
  Qed.

  Lemma rk_relife (γ γ1 : State) x f (l : Life) :
    fibers γ1 = fibers γ -> fibers γ x = Some f -> RootKeep γ (set_life Σ γ1 x f l).
  Proof.
    intros E Hx; split.
    - intros m f' Hm Hp; unfold set_life, set_fiber, with_fibers, fupd in Hm; cbn in Hm.
      destruct (Nat.eqb_spec m x) as [->|].
      + injection Hm as <-; exists f; split; [exact Hx | split; [exact Hp | split; reflexivity]].
      + rewrite E in Hm; exists f'; auto.
    - intros m f0 Hm Hp Hd; unfold set_life, set_fiber, with_fibers, fupd; cbn.
      destruct (Nat.eqb_spec m x) as [->|].
      + rewrite Hx in Hm; injection Hm as <-.
        exists (mkFiber Σ (fcomp f) (parent f) (disposed f) l); split; [reflexivity | split; [exact Hp | exact Hd]].
      + rewrite E; exists f0; auto.
  Qed.

  Theorem rk_step (γ γ' : State) ℓ : PInv γ -> is_lifecycle ℓ -> step γ ℓ = Some γ' -> RootKeep γ γ'.
  Proof.
    intros [SI EP] (n0 & Hlab) H.
    pose proof (sinv_wf γ SI) as W.
    pose proof (c0_t K_eq_dec Σ prog Kb γ (s_c _ SI)) as TI.
    pose proof (t_so K_eq_dec Σ prog Kb γ TI) as SO.
    destruct ℓ as [c|x|x|x|x|x|x|x|x|x|x|x i|x];
      try (exfalso; cbn in Hlab; intuition discriminate); cbn [step] in H.
    - (* LBegin *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]|P acc w|acc w|acc w z] eqn:Hl;
        repeat match type of H with context [match ?e with _ => _ end] => destruct e end;
        try discriminate; injection H as <-.
      exact (rk_relife γ γ x f _ eq_refl Hx).
    - (* LStep *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      dif H; [injection H as <- | discriminate].
      destruct P as [| |k a κ|k s P'|c P'].
      + exact (rk_relife γ γ x f _ eq_refl Hx).
      + exact (rk_relife γ γ x f _ eq_refl Hx).
      + rewrite (load_step_op K_eq_dec Σ prog γ x f k a κ acc w).
        destruct (op_binding K_eq_dec Σ prog γ x f k w) as [b|]; [|exact (rk_relife γ γ x f _ eq_refl Hx)].
        destruct (run a (next γ) (bst b)) as [[[s' g] o]|]; apply (rk_relife γ); [reflexivity | exact Hx | reflexivity | exact Hx].
      + cbn [load_step].
        destruct (kmem K_eq_dec k (provs Σ (prog (fcomp f)))); [|exact (rk_relife γ γ x f _ eq_refl Hx)].
        destruct (binds γ k); apply (rk_relife γ); [reflexivity | exact Hx | reflexivity | exact Hx].
      + cbn [load_step]; destruct (conflict K_eq_dec Σ prog γ c); [exact (rk_relife γ γ x f _ eq_refl Hx)|].
        set (γ1 := bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ)
                     (Some (mkFiber Σ c (Some x) false (Inactive Σ None)))))).
        pose proof (wf_names K_eq_dec Σ prog γ W x f Hx) as Hxlt.
        apply (rk_trans γ γ1).
        * split.
          -- intros m f' Hm Hp; unfold γ1, bump, with_fibers, fupd in Hm; cbn in Hm.
             destruct (Nat.eqb_spec m (next γ)); [injection Hm as <-; discriminate | exists f'; auto].
          -- intros m f0 Hm Hp Hd; exists f0; split; [|auto].
             pose proof (wf_names K_eq_dec Σ prog γ W m f0 Hm).
             unfold γ1, bump, with_fibers, fupd; cbn; rewrite (proj2 (Nat.eqb_neq m (next γ)) ltac:(lia)); exact Hm.
        * apply (rk_relife γ1 γ1); [reflexivity|].
          unfold γ1, bump, with_fibers, fupd; cbn; rewrite (proj2 (Nat.eqb_neq x (next γ)) ltac:(lia)); exact Hx.
    - (* LDivert *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      dif H; [discriminate | injection H as <-]; exact (rk_relife γ γ x f _ eq_refl Hx).
    - (* LLeave *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      dif H; [discriminate | injection H as <-]; exact (rk_relife γ γ x f _ eq_refl Hx).
    - (* LUndo *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      destruct (undo_step_shape K_eq_dec Σ γ γ' x f u acc w z H) as (γ1 & -> & E).
      exact (rk_relife γ γ1 x f _ E Hx).
    - (* LRetireChild *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|[|u acc] w z] eqn:Hl; try discriminate.
      destruct u as [k p t g|k p|m0]; try discriminate.
      destruct (fibers γ m0) as [g|] eqn:Hm0; [|discriminate].
      dif H; [discriminate | injection H as <-].
      assert (Hx0 : In (USpawn Σ m0) (acc_of (life f))) by (rewrite Hl; left; reflexivity).
      pose proof (SO x f m0 g Hx Hx0 Hm0) as Pg.
      split.
      + intros m f' Hm Hp; unfold set_fiber, with_fibers, fupd in Hm; cbn in Hm.
        destruct (Nat.eqb_spec m m0) as [->|]; [injection Hm as <-; cbn in Hp; congruence | exists f'; auto].
      + intros m f0 Hm Hp Hd; unfold set_fiber, with_fibers, fupd; cbn.
        destruct (Nat.eqb_spec m m0) as [->|]; [congruence | exists f0; auto].
    - (* LUnloaded *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|[|u acc] w z] eqn:Hl; try discriminate; injection H as <-.
      exact (rk_relife γ γ x f _ eq_refl Hx).
    - (* LRemove *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      destruct (disposed f) eqn:Hd; [|discriminate].
      dif H; [injection H as <- | discriminate].
      split.
      + intros m f' Hm Hp; unfold with_fibers, fupd in Hm; cbn in Hm.
        destruct (Nat.eqb_spec m x); [discriminate | exists f'; auto].
      + intros m f0 Hm Hp Hd0; unfold with_fibers, fupd; cbn.
        destruct (Nat.eqb_spec m x) as [->|]; [congruence | exists f0; auto].
  Qed.

  Lemma lrun_rk (γ0 γ : State) : PInv γ0 -> LRun K_eq_dec Σ prog γ0 γ -> RootKeep γ0 γ.
  Proof.
    intros P R; induction R as [γ|γ ℓ γ1 γ2 Hlc Hs _ IH]; [exact (rk_refl γ)|].
    exact (rk_trans γ γ1 γ2 (rk_step γ γ1 ℓ P Hlc Hs) (IH (pinv_step γ γ1 ℓ (lifecycle_not_react ℓ Hlc) P Hs))).
  Qed.

  Lemma roots_match (γ0 γ1 γ2 : State) :
    RootKeep γ0 γ1 -> RootKeep γ0 γ2 -> Final γ1 -> RootsMatch (fun n => n) (fun n => n) γ1 γ2.
  Proof.
    intros [A1 _] [A2 B2] F1 n fa Ha Hp.
    destruct (A1 n fa Ha Hp) as (f0 & H0 & P0 & C0 & D0).
    destruct (settled_shape Σ prog γ1 n fa (proj1 (proj2 F1)) (proj2 (proj2 F1)) Ha) as [Hd _].
    destruct (B2 n f0 H0 P0 ltac:(congruence)) as (fb & Hb & Pb & _).
    destruct (A2 n fb Hb Pb) as (f0' & H0' & _ & C0' & _).
    rewrite H0 in H0'; injection H0' as <-.
    exists n, fb; split; [exact Hb|]; split; [exact Pb | split; [reflexivity | congruence]].
  Qed.

  (** ** Multisets along a bijection *)
  Lemma filter_nonnil_nil {A} (F : nat -> list A) l :
    (forall b, In b l -> F b = []) -> filter nonnil (map F l) = [].
  Proof.
    induction l as [|b l IH]; intros H; cbn; [reflexivity|].
    rewrite (H b (or_introl eq_refl)); cbn; apply IH; intros b' Hb'; exact (H b' (or_intror Hb')).
  Qed.

  (** Blocks matched by a bijection of names are a permutation of each
      other, once empty blocks are dropped. *)
  Lemma perm_bij_blocks {A} (F1 F2 : nat -> list A) (R : nat -> nat -> Prop) l1 l2 :
    NoDup l1 -> NoDup l2 ->
    (forall a, In a l1 -> F1 a = [] \/ exists b, In b l2 /\ R a b) ->
    (forall b, In b l2 -> F2 b = [] \/ exists a, In a l1 /\ R a b) ->
    (forall a b b', R a b -> R a b' -> b = b') ->
    (forall a a' b, R a b -> R a' b -> a = a') ->
    (forall a b, R a b -> F1 a = F2 b) ->
    Permutation (filter nonnil (map F1 l1)) (filter nonnil (map F2 l2)).
  Proof.
    revert l2; induction l1 as [|a l1 IH]; intros l2 N1 N2 C1 C2 Fn Inj E.
    - cbn; rewrite filter_nonnil_nil; [constructor|].
      intros b Hb; destruct (C2 b Hb) as [H|(a & [] & _)]; exact H.
    - apply NoDup_cons_iff in N1 as [Na N1].
      destruct (F1 a) as [|x B] eqn:Ea.
      + cbn [map filter]; rewrite Ea; cbn [nonnil].
        apply IH; auto.
        * intros a' Ha'; apply C1; right; exact Ha'.
        * intros b Hb; destruct (C2 b Hb) as [H|(a' & [<-|Ha'] & Rab)]; [left; exact H | | right; eauto].
          left; rewrite <- (E a b Rab); exact Ea.
      + destruct (C1 a (or_introl eq_refl)) as [Ha|(b & Hb & Rab)]; [congruence|].
        apply in_split in Hb as (l2a & l2b & ->).
        cbn [map filter]; rewrite Ea; cbn [nonnil].
        rewrite map_app, filter_app; cbn [map filter]; rewrite <- (E a b Rab), Ea; cbn [nonnil].
        apply (Permutation_trans (l' := (x :: B) :: (filter nonnil (map F2 l2a) ++ filter nonnil (map F2 l2b)))).
        * apply perm_skip; rewrite <- filter_app, <- map_app; apply IH.
          -- exact N1.
          -- exact (NoDup_remove_1 _ _ _ N2).
          -- intros a' Ha'; destruct (C1 a' (or_intror Ha')) as [H|(b' & Hb' & R')]; [left; exact H | right].
             exists b'; split; [|exact R'].
             apply in_app_iff in Hb' as [Hb'|[<-|Hb']]; apply in_app_iff; [left; exact Hb' | | right; exact Hb'].
             exfalso; apply Na; rewrite (Inj a' a b R' Rab) in Ha'; exact Ha'.
          -- intros b' Hb'; assert (Hb2 : In b' (l2a ++ b :: l2b))
               by (apply in_app_iff in Hb' as [H|H]; apply in_app_iff; [left | right; right]; exact H).
             destruct (C2 b' Hb2) as [H|(a' & [<-|Ha'] & R')]; [left; exact H | | right; eauto].
             exfalso; apply (NoDup_remove_2 _ _ _ N2); rewrite <- (Fn a b b' Rab R') in Hb'; exact Hb'.
          -- exact Fn.
          -- exact Inj.
          -- exact E.
        * apply Permutation_middle.
  Qed.

  (** Operations in different fibers' blocks may meet. *)
  Lemma blocks_cross (γ : State) k l : SInv γ -> NoDup l -> CrossB (CoPair k) (map (blockAt γ k) l).
  Proof.
    intros SI; induction l as [|n l IH]; intros N; cbn; [exact I|].
    apply NoDup_cons_iff in N as [Nn N]; split; [|exact (IH N)].
    intros [a t] [b u] Hx Hy; cbn.
    unfold blockAt, itemsAt in Hx; destruct (fibers γ n) as [fn|] eqn:Hn; [|destruct Hx].
    apply in_rev, in_itemsF in Hx as (p & g & Ix & Hoa).
    apply in_concat in Hy as (B' & HB & Hy); apply in_map_iff in HB as (m & <- & Hm).
    unfold blockAt, itemsAt in Hy; destruct (fibers γ m) as [fm|] eqn:Hfm; [|destruct Hy].
    apply in_rev, in_itemsF in Hy as (p' & g' & Iy & Hob).
    assert (Hne : n <> m) by (intros ->; contradiction).
    destruct (item_op γ n fn k p t g SI Hn Ix) as (a' & Ha' & Hopa); rewrite Hoa in Ha'; injection Ha' as <-.
    destruct (item_op γ m fm k p' u g' SI Hfm Iy) as (b' & Hb' & Hopb); rewrite Hob in Hb'; injection Hb' as <-.
    split; [exact (copair_fibers γ n fn m fm k a b SI Hne Hn Hfm Hopa Hopb)|].
    intros Etu; subst u; destruct (item_unique γ n fn m fm k p g k p' g' t SI Hn Hfm Ix Iy) as (E & _); contradiction.
  Qed.

  (** What two final states agree on, up to renaming; roots are named by
      the labels [l1] and [l2]. *)
  Definition AgreeL (l1 l2 : nat -> nat) (γ1 γ2 : State) : Prop :=
    (forall n f, fibers γ1 n = Some f -> exists x, CN l1 γ1 n x) /\
    (forall n f, fibers γ2 n = Some f -> exists x, CN l2 γ2 n x) /\
    (forall n x x', CN l1 γ1 n x -> CN l1 γ1 n x' -> x = x') /\
    (forall n x x', CN l2 γ2 n x -> CN l2 γ2 n x' -> x = x') /\
    (forall x n1 f1, CN l1 γ1 n1 x -> fibers γ1 n1 = Some f1 ->
       exists n2 f2, CN l2 γ2 n2 x /\ fibers γ2 n2 = Some f2 /\ fcomp f2 = fcomp f1 /\
                     is_active Σ (life f2) = is_active Σ (life f1)) /\
    (forall x n2 f2, CN l2 γ2 n2 x -> fibers γ2 n2 = Some f2 ->
       exists n1 f1, CN l1 γ1 n1 x /\ fibers γ1 n1 = Some f1 /\ fcomp f1 = fcomp f2 /\
                     is_active Σ (life f1) = is_active Σ (life f2)) /\
    (forall k b1 x, binds γ1 k = Some b1 -> CN l1 γ1 (owner b1) x ->
       exists b2, binds γ2 k = Some b2 /\ CN l2 γ2 (owner b2) x) /\
    (forall k b2 x, binds γ2 k = Some b2 -> CN l2 γ2 (owner b2) x ->
       exists b1, binds γ1 k = Some b1 /\ CN l1 γ1 (owner b1) x) /\
    (forall k b1 b2, binds γ1 k = Some b1 -> binds γ2 k = Some b2 -> bst b1 ≃ bst b2).

  (** Runs from one start state keep root names. *)
  Definition Agree (γ1 γ2 : State) : Prop := AgreeL (fun n => n) (fun n => n) γ1 γ2.

  (** ** Confluence at the level of states

      Two final states whose roots correspond, label for label and
      component for component, agree up to renaming. Nothing here mentions
      how the two states were reached. *)
  Theorem final_agree l1 l2 (γ1 γ2 : State) :
    FinalS γ1 -> FinalS γ2 -> RootInj l1 γ1 -> RootInj l2 γ2 ->
    RootsMatch l1 l2 γ1 γ2 -> RootsMatch l2 l1 γ2 γ1 ->
    AgreeL l1 l2 γ1 γ2.
  Proof.
    intros F1 F2 RI1 RI2 RM12 RM21; unfold AgreeL.
    pose proof (proj2 F1) as S1; pose proof (proj2 F2) as S2.
    pose proof (proj1 (proj1 F1)) as P1; pose proof (proj1 (proj1 F2)) as P2.
    destruct (corresp_all l1 l2 γ1 γ2 F1 F2 RM12 RM21 (Datatypes.S Rb)) as [C12 C21].
    assert (Hr : forall c, rank c < Datatypes.S Rb) by (intros c; pose proof (Hbnd c); lia).
    pose proof (p_s _ P1) as SI1; pose proof (p_s _ P2) as SI2.
    pose proof (sinv_wf γ1 SI1) as W1; pose proof (sinv_wf γ2 SI2) as W2.
    (* owners correspond *)
    assert (Own : forall la lb (γa γb : State) (Fa : FinalS γa) (Fb : FinalS γb),
              Corresp la lb γa γb (Datatypes.S Rb) ->
              forall k ba x, binds γa k = Some ba -> CN la γa (owner ba) x ->
              exists bb, binds γb k = Some bb /\ CN lb γb (owner bb) x).
    { intros la lb γa γb Fa Fb Cab k ba x Hba Hx.
      pose proof (p_s _ (proj1 (proj1 Fa))) as SIa; pose proof (p_s _ (proj1 (proj1 Fb))) as SIb.
      destruct (wf_bind K_eq_dec Σ prog γa (sinv_wf γa SIa) k ba Hba) as (fo & Hfo & _ & Hkp & Hup).
      destruct (final_fiber γa _ fo (proj1 Fa) Hfo) as [E|(acc & w & evs & Lo & _ & _)];
        [rewrite E in Hup; destruct Hup|].
      destruct (Cab x _ fo Hx Hfo (Hr _)) as (ob & fob & CNb & Hfob & Hc & Ha & _).
      rewrite Lo in Ha; cbn in Ha.
      assert (Hkb : In k (cprovs (fcomp fob))) by (rewrite Hc; exact (kmem_In K_eq_dec k _ Hkp)).
      pose proof (proj2 (owner_iff K_eq_dec Σ prog Kb γb k ob (s_c _ SIb) (proj1 (proj2 (proj1 Fb)))
                           (proj2 (proj2 (proj1 Fb)))) (ex_intro _ fob (conj Hfob (conj Ha Hkb)))) as E.
      destruct (binds γb k) as [bb|]; [|discriminate]; injection E as E.
      exists bb; split; [reflexivity | rewrite E; exact CNb]. }
    split; [intros n f H; exact (cn_total l1 γ1 n f SI1 S1 H)|].
    split; [intros n f H; exact (cn_total l2 γ2 n f SI2 S2 H)|].
    split; [intros n x x'; exact (cn_fun l1 γ1 n x x' S1)|].
    split; [intros n x x'; exact (cn_fun l2 γ2 n x x' S2)|].
    split.
    { intros x n1 f1 Hx H1; destruct (C12 x n1 f1 Hx H1 (Hr _)) as (n2 & f2 & A & B & C' & D & _).
      exists n2, f2; auto. }
    split.
    { intros x n2 f2 Hx H2; destruct (C21 x n2 f2 Hx H2 (Hr _)) as (n1 & f1 & A & B & C' & D & _).
      exists n1, f1; auto. }
    split; [exact (Own l1 l2 γ1 γ2 F1 F2 C12)|].
    split; [exact (Own l2 l1 γ2 γ1 F2 F1 C21)|].
    (* service states *)
    intros k b1 b2 Hb1 Hb2.
    destruct (s_inv _ SI1 k b1 Hb1) as (s01 & L1 & s1 & Hi1 & PL1 & Rp1 & E1).
    destruct (s_inv _ SI2 k b2 Hb2) as (s02 & L2 & s2 & Hi2 & PL2 & Rp2 & E2).
    (* the same initial state *)
    destruct (wf_bind K_eq_dec Σ prog γ1 W1 k b1 Hb1) as (fo1 & Hfo1 & _ & _ & Hup1).
    destruct (wf_bind K_eq_dec Σ prog γ2 W2 k b2 Hb2) as (fo2 & Hfo2 & _ & _ & Hup2).
    destruct (cn_total l1 γ1 _ fo1 SI1 S1 Hfo1) as [x Hx].
    destruct (Own l1 l2 γ1 γ2 F1 F2 C12 k b1 x Hb1 Hx) as (b2' & Hb2' & Hx2).
    rewrite Hb2 in Hb2'; injection Hb2' as <-.
    destruct (C12 x _ fo1 Hx Hfo1 (Hr _)) as (o2 & fo2' & CN2 & Hfo2' & Hc0 & Ha0 & Htr).
    rewrite <- (cn_inj l2 γ2 _ _ x RI2 Hx2 CN2) in Hfo2'; rewrite Hfo2 in Hfo2'; injection Hfo2' as <-.
    destruct (final_fiber γ1 _ fo1 (proj1 F1) Hfo1) as [E|(acc1 & w1 & evs1 & L1' & T1 & C1)];
      [rewrite E in Hup1; destruct Hup1|].
    destruct (final_fiber γ2 _ fo2 (proj1 F2) Hfo2) as [E|(acc2 & w2 & evs2 & L2' & T2 & C2)];
      [rewrite E in Hup2; destruct Hup2|].
    pose proof (Htr acc1 w1 evs1 acc2 w2 evs2 L1' L2' T1 C1 T2 C2) as Eev.
    pose proof (wf_uprov_unique K_eq_dec Σ prog γ1 W1 _ fo1 Hfo1) as U1; rewrite L1' in U1, Hup1.
    pose proof (wf_uprov_unique K_eq_dec Σ prog γ2 W2 _ fo2 Hfo2) as U2; rewrite L2' in U2, Hup2.
    destruct (corr_find γ1 _ w1 acc1 evs1 k (pid b1) C1 U1 Hup1) as (s1' & Hi1' & Hf1).
    destruct (corr_find γ2 _ w2 acc2 evs2 k (pid b2) C2 U2 Hup2) as (s2' & Hi2' & Hf2).
    assert (s02 = s01) by (rewrite Eev in Hf1; congruence); subst s02.
    (* the same operations, along the renaming, fiber by fiber *)
    destruct (final_blocks γ1 k b1 L1 (next γ1) s01 s1 (proj1 F1) (le_n _) Hb1 PL1 Rp1) as (x1 & X1 & Ex1).
    destruct (final_blocks γ2 k b2 L2 (next γ2) s01 s2 (proj1 F2) (le_n _) Hb2 PL2 Rp2) as (x2 & X2 & Ex2).
    assert (EM : Permutation (filter nonnil (map (map fst) (map (blockAt γ1 k) (seq 0 (next γ1)))))
                             (filter nonnil (map (map fst) (map (blockAt γ2 k) (seq 0 (next γ2)))))).
    { rewrite !map_map.
      apply (perm_bij_blocks _ _ (fun a b => exists x, CN l1 γ1 a x /\ CN l2 γ2 b x));
        [apply seq_NoDup | apply seq_NoDup | | | | |].
      - intros a _; unfold blockAt, itemsAt; destruct (fibers γ1 a) as [fa|] eqn:Ha; [|left; reflexivity].
        right; destruct (cn_total l1 γ1 a fa SI1 S1 Ha) as [y Hy].
        destruct (C12 y a fa Hy Ha (Hr _)) as (b & fb & Hyb & Hb & _).
        exists b; split; [apply in_seq; pose proof (wf_names K_eq_dec Σ prog γ2 W2 b fb Hb); lia | exists y; auto].
      - intros b _; unfold blockAt, itemsAt; destruct (fibers γ2 b) as [fb|] eqn:Hb; [|left; reflexivity].
        right; destruct (cn_total l2 γ2 b fb SI2 S2 Hb) as [y Hy].
        destruct (C21 y b fb Hy Hb (Hr _)) as (a & fa & Hya & Ha & _).
        exists a; split; [apply in_seq; pose proof (wf_names K_eq_dec Σ prog γ1 W1 a fa Ha); lia | exists y; auto].
      - intros a b b' (y & Ha & Hb) (y' & Ha' & Hb').
        rewrite (cn_fun l1 γ1 a y y' S1 Ha Ha') in Hb; exact (cn_inj l2 γ2 b b' y' RI2 Hb Hb').
      - intros a a' b (y & Ha & Hb) (y' & Ha' & Hb').
        rewrite (cn_fun l2 γ2 b y y' S2 Hb Hb') in Ha; exact (cn_inj l1 γ1 a a' y' RI1 Ha Ha').
      - intros a b (y & Ha & Hb).
        destruct (cn_present l1 γ1 a y Ha) as [fa Hfa]; destruct (cn_present l2 γ2 b y Hb) as [fb Hfb].
        destruct (C12 y a fa Ha Hfa (Hr _)) as (b' & fb' & Hb' & Hfb' & _ & Hact & Htr').
        rewrite <- (cn_inj l2 γ2 _ _ y RI2 Hb Hb') in Hfb'; rewrite Hfb in Hfb'; injection Hfb' as <-.
        unfold blockAt, itemsAt; rewrite Hfa, Hfb, !map_rev; f_equal.
        destruct (final_fiber γ1 a fa (proj1 F1) Hfa) as [Ea|(acca & wa & evsa & La & Ta & Ca)];
          destruct (final_fiber γ2 b fb (proj1 F2) Hfb) as [Eb|(accb & wb & evsb & Lb & Tb & Cb)].
        + unfold uacc; rewrite Ea, Eb; reflexivity.
        + rewrite Ea, Lb in Hact; discriminate.
        + rewrite La, Eb in Hact; discriminate.
        + unfold uacc; rewrite La, Lb; cbn [acc_of].
          rewrite (corr_ops γ1 _ _ _ _ k Ca), (corr_ops γ2 _ _ _ _ k Cb); f_equal.
          exact (Htr' acca wa evsa accb wb evsb La Lb Ta Ca Tb Cb). }
    pose proof (replay_blocks (CoPair k) Hwb HTI (CoPair_sym k) (HCom k) _ _ s01 x1 x2
                  (blocks_cross γ1 k _ SI1 (seq_NoDup _ _)) EM X1 X2) as Es.
    transitivity s1; [exact E1|]; transitivity x1; [exact Ex1|]; transitivity x2; [exact Es|].
    transitivity s2; symmetry; assumption.
  Qed.

  (** A quiet state that keeps the invariants and has no failed fiber is final. *)
  Lemma quiet_final (γ : State) :
    PInv γ -> SLInv γ -> quiet K_eq_dec Σ prog γ -> NoFailed Σ γ -> FinalS γ.
  Proof.
    intros P SL Q NF; split; [|exact SL]; split; [exact P|]; split; [|exact NF].
    pose proof (c0_t K_eq_dec Σ prog Kb γ (s_c _ (p_s _ P))) as T.
    exact (quiet_settled K_eq_dec Σ prog (Hwf Σ prog rank Rb Hrank Hbnd) γ
             (t_wf K_eq_dec Σ prog Kb γ T) (t_inv2 K_eq_dec Σ prog Kb γ T) Q).
  Qed.

  (** ** Confluence with spawn

      From a state satisfying the invariants, two lifecycle runs that end
      quiet with no failed fiber agree up to renaming: canonical names
      name every fiber exactly once; the same names occur, with the same
      components and activity; corresponding fibers own each key; and each
      key's service states are related by ≃. *)
  Theorem spawn_confluence (γ0 γ1 γ2 : State) :
    PInv γ0 -> SLInv γ0 -> LRun K_eq_dec Σ prog γ0 γ1 -> LRun K_eq_dec Σ prog γ0 γ2 ->
    quiet K_eq_dec Σ prog γ1 -> quiet K_eq_dec Σ prog γ2 -> NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    Agree γ1 γ2.
  Proof.
    intros P0 S0 R1 R2 Q1 Q2 NF1 NF2.
    destruct (lrun_sl γ0 γ1 P0 S0 R1) as [P1 S1].
    destruct (lrun_sl γ0 γ2 P0 S0 R2) as [P2 S2].
    pose proof (quiet_final γ1 P1 S1 Q1 NF1) as F1; pose proof (quiet_final γ2 P2 S2 Q2 NF2) as F2.
    pose proof (lrun_rk γ0 γ1 P0 R1) as K1; pose proof (lrun_rk γ0 γ2 P0 R2) as K2.
    assert (RI : forall γ, RootInj (fun n => n) γ) by (intros γ n n' f f' _ _ _ _ E; exact E).
    exact (final_agree _ _ γ1 γ2 F1 F2 (RI γ1) (RI γ2)
             (roots_match γ0 γ1 γ2 K1 K2 (proj1 F1)) (roots_match γ0 γ2 γ1 K2 K1 (proj1 F2))).
  Qed.
End SpawnConf.
