(** * Confluence, part 2: ideal traces

    An ideal trace ([Tr]) runs a component's program on its own, answering
    each operation from the initial state of the provision it resolves to.
    Ideal traces are determined by the program and those initial states
    ([tr_done_eq]). Every Loading or Active fiber's accumulator corresponds
    to an ideal trace ([EPInv]), and every step keeps this ([pinv_step]). *)

From Stdlib Require Import List PeanoNat Bool Lia RelationClasses Permutation Sorted Wf_nat.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering
  Recovery Progress Termination Confluence StateInv.
Import ListNotations.

Section Episode.
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

  (** ** Path determinism: ideal traces

      An ideal trace runs a component's program on its own, answering each
      operation from the initial state of the provision it resolves to:
      through [ρ] for a declared dependency, through the trace's own earlier
      provide otherwise. Events are listed newest first, as accumulators
      are. *)
  Definition itemsF (γ : State) (k : K) (l : list Itm) : list (Op Σ * nat) :=
    flat_map (fun x => match x with (k', _, t, _) =>
      if K_eq_dec k' k then match oplog γ t with Some a => [(a, t)] | None => [] end else [] end) l.

  Lemma in_itemsF (γ : State) k l a t :
    In (a, t) (itemsF γ k l) <-> exists p g, In (k, p, t, g) l /\ oplog γ t = Some a.
  Proof.
    unfold itemsF; rewrite in_flat_map; split.
    - intros ((((k', p), t'), g) & Hin & H).
      destruct (K_eq_dec k' k) as [->|]; [|destruct H].
      destruct (oplog γ t') as [a'|] eqn:E; [|destruct H].
      destruct H as [E'|[]]; injection E' as <- <-; exists p, g; auto.
    - intros (p & g & Hin & Ho); exists (k, p, t, g); split; [exact Hin|].
      destruct (K_eq_dec k k); [|contradiction]; rewrite Ho; left; reflexivity.
  Qed.

  Lemma ss_gt_nodup (l : list nat) : StronglySorted gt l -> NoDup l.
  Proof.
    induction l as [|x l IH]; intros Hs; constructor.
    - apply StronglySorted_inv in Hs as [_ Hf]; rewrite Forall_forall in Hf.
      intros Hx; specialize (Hf x Hx); lia.
    - apply StronglySorted_inv in Hs as [Hs _]; exact (IH Hs).
  Qed.

  Lemma itemsF_sorted (γ : State) k l :
    StronglySorted gt (map itok l) -> StronglySorted gt (map snd (itemsF γ k l)).
  Proof.
    induction l as [|x l IH]; intros Hs; [constructor|].
    cbn in Hs; apply StronglySorted_inv in Hs as [Hs Hf].
    destruct x as [[[k' p] t] g].
    change (itemsF γ k ((k', p, t, g) :: l)) with
      ((if K_eq_dec k' k then match oplog γ t with Some a => [(a, t)] | None => [] end else [])
       ++ itemsF γ k l).
    destruct (K_eq_dec k' k) as [->|]; [destruct (oplog γ t) as [a|]|]; cbn [app]; try exact (IH Hs).
    cbn [map]; constructor; [exact (IH Hs)|].
    rewrite Forall_forall in *; intros y Hy.
    apply in_map_iff in Hy as ([a' t'] & <- & Hy); apply in_itemsF in Hy as (p' & g' & Hy & _).
    exact (Hf t' (in_map itok _ _ Hy)).
  Qed.

  Inductive Ev : Type := TOp (k : K) (a : Op Σ) | TProv (k : K) (s : S) | TSpawn (c : C).

  Fixpoint find_prov (evs : list Ev) (k : K) : option S :=
    match evs with
    | [] => None
    | TProv k' s :: evs' => if K_eq_dec k k' then Some s else find_prov evs' k
    | TOp _ _ :: evs' => find_prov evs' k
    | TSpawn _ :: evs' => find_prov evs' k
    end.

  Definition evOps (k : K) (evs : list Ev) : list (Op Σ) :=
    flat_map (fun e => match e with TOp k' a => if K_eq_dec k' k then [a] else [] | TProv _ _ => [] | TSpawn _ => [] end) evs.

  (** A trace's own operations at [k], oldest first, under token 0. *)
  Definition ownIt (k : K) (evs : list Ev) : list (Op Σ * nat) := map (fun a => (a, 0)) (rev (evOps k evs)).


  Definition resolveI (c : C) (ρ : K -> option S) (evs : list Ev) (k : K) : option S :=
    if kmem K_eq_dec k (cdeps c) then ρ k else find_prov evs k.

  Inductive Tr (c : C) (ρ : K -> option S) : list Ev -> Prog -> Prop :=
  | tr_nil : Tr c ρ [] (cbody c)
  | tr_op evs k a κ s0 s1 s' g o :
      Tr c ρ evs (POp k a κ) -> resolveI c ρ evs k = Some s0 ->
      Replay (ownIt k evs) s0 s1 ->
      run a 0 s1 = Some (s', g, o) -> Tr c ρ (TOp k a :: evs) (κ o)
  | tr_prov evs k s P :
      Tr c ρ evs (PProvide k s P) -> Tr c ρ (TProv k s :: evs) P
  | tr_spawn evs c' P :
      Tr c ρ evs (PSpawn c' P) -> Tr c ρ (TSpawn c' :: evs) P.

  Lemma tr_ext c ρ1 ρ2 evs P : (forall k, ρ1 k = ρ2 k) -> Tr c ρ1 evs P -> Tr c ρ2 evs P.
  Proof.
    intros E H; induction H as [|evs k a κ s0 s1 s' g o T IH R Rp X|evs k s P T IH|evs c' P T IH].
    - constructor.
    - eapply tr_op; [exact IH | | exact Rp | exact X].
      unfold resolveI in *; destruct (kmem K_eq_dec k (cdeps c)); [rewrite <- E|]; exact R.
    - apply tr_prov; exact IH.
    - apply tr_spawn; exact IH.
  Qed.

  Lemma tr_det c ρ1 ρ2 e1 e2 P1 P2 :
    (forall k, In k (cdeps c) -> ρ1 k = ρ2 k) ->
    Tr c ρ1 e1 P1 -> Tr c ρ2 e2 P2 -> length e1 = length e2 -> e1 = e2 /\ P1 = P2.
  Proof.
    intros E H1; revert e2 P2.
    induction H1 as [|e1 k a κ s0 s1 s' g o T1 IH R1 Rp1 X1|e1 k s P T1 IH|e1 c' P T1 IH];
      intros e2 P2 H2 L.
    - destruct e2; [|discriminate]; inversion H2; auto.
    - destruct e2 as [|x e2]; [discriminate|]; cbn in L; injection L as L.
      inversion H2 as [|e2' k' a' κ' s0' s1' s'' g' o' T2 R2 Rp2 X2|e2' k' s'' P' T2|e2' c'' P' T2]; subst;
        destruct (IH _ _ T2 L) as [<- E2]; try discriminate.
      injection E2 as <- <- <-.
      assert (s0' = s0).
      { unfold resolveI in R1, R2.
        destruct (kmem K_eq_dec k (cdeps c)) eqn:Hk; [rewrite E in R1 by exact (kmem_In K_eq_dec k _ Hk)|];
          congruence. }
      subst s0'.
      pose proof (replay_det _ _ _ _ Rp1 Rp2) as E12.
      pose proof (wb_respects a 0 (Hwb a 0) s1 s1' E12) as Hres; rewrite X1, X2 in Hres; cbn in Hres.
      destruct Hres as (_ & _ & <-); auto.
    - destruct e2 as [|x e2]; [discriminate|]; cbn in L; injection L as L.
      inversion H2 as [|e2' k' a' κ' s0' s1' s'' g' o' T2 R2 Rp2 X2|e2' k' s'' P' T2|e2' c'' P' T2]; subst;
        destruct (IH _ _ T2 L) as [<- E2]; try discriminate.
      injection E2 as <- <- <-; auto.
    - destruct e2 as [|x e2]; [discriminate|]; cbn in L; injection L as L.
      inversion H2 as [|e2' k' a' κ' s0' s1' s'' g' o' T2 R2 Rp2 X2|e2' k' s'' P' T2|e2' c'' P' T2]; subst;
        destruct (IH _ _ T2 L) as [<- E2]; try discriminate.
      injection E2 as <- <-; auto.
  Qed.

  Lemma tr_drop c ρ pre l P : Tr c ρ (pre ++ l) P -> exists P', Tr c ρ l P'.
  Proof.
    revert P; induction pre as [|x pre IH]; intros P H; [exists P; exact H|].
    cbn in H; inversion H; subst; eapply IH; eassumption.
  Qed.

  Lemma tr_done_len c ρ1 ρ2 e1 e2 P2 :
    (forall k, In k (cdeps c) -> ρ1 k = ρ2 k) ->
    Tr c ρ1 e1 PDone -> Tr c ρ2 e2 P2 -> length e2 <= length e1.
  Proof.
    intros E T1 T2.
    destruct (Compare_dec.le_lt_dec (length e2) (length e1)) as [|Hlt]; [assumption | exfalso].
    set (d := length e2 - Datatypes.S (length e1)).
    assert (Hsk : length (skipn d e2) = Datatypes.S (length e1)) by (rewrite length_skipn; unfold d; lia).
    rewrite <- (firstn_skipn d e2) in T2.
    destruct (skipn d e2) as [|x r] eqn:Es; [discriminate|]; cbn in Hsk; injection Hsk as Hsk.
    destruct (tr_drop c ρ2 _ _ _ T2) as (P' & T3).
    inversion T3 as [|r' k a κ s0 s1 s' g o T4 R4 P4 X4|r' k s P T4|r' c' P T4]; subst;
      destruct (tr_det c ρ1 ρ2 e1 r _ _ E T1 T4 (eq_sym Hsk)) as [_ E2]; discriminate.
  Qed.

  Lemma tr_done_eq c ρ1 ρ2 e1 e2 :
    (forall k, In k (cdeps c) -> ρ1 k = ρ2 k) ->
    Tr c ρ1 e1 PDone -> Tr c ρ2 e2 PDone -> e1 = e2.
  Proof.
    intros E T1 T2.
    pose proof (tr_done_len c ρ1 ρ2 e1 e2 _ E T1 T2).
    pose proof (tr_done_len c ρ2 ρ1 e2 e1 _ (fun k Hk => eq_sym (E k Hk)) T2 T1).
    exact (proj1 (tr_det c ρ1 ρ2 e1 e2 _ _ E T1 T2 ltac:(lia))).
  Qed.

  (** ** Accumulators against traces *)
  Lemma lv_In k (w : @View K) p : lookup_view K_eq_dec k w = Some p -> In (k, p) w.
  Proof.
    induction w as [|[k' p'] w IH]; cbn; [discriminate|].
    unfold keqb; destruct (K_eq_dec k k') as [->|Hne];
      [intros [= ->]; left; reflexivity | intros H; right; exact (IH H)].
  Qed.

  Definition rho (γ : State) (w : @View K) (k : K) : option S :=
    match lookup_view K_eq_dec k w with Some p => inilog γ p | None => None end.

  Inductive Corr (γ : State) (c : C) (w : @View K) : list Undo -> list Ev -> Prop :=
  | co_nil : Corr γ c w [] []
  | co_op k p t g a acc evs :
      Corr γ c w acc evs -> oplog γ t = Some a ->
      (if kmem K_eq_dec k (cdeps c) then lookup_view K_eq_dec k w = Some p
       else In (UProv Σ k p) acc) ->
      Corr γ c w (UOp Σ k p t g :: acc) (TOp k a :: evs)
  | co_prov k p s acc evs :
      Corr γ c w acc evs -> inilog γ p = Some s ->
      Corr γ c w (UProv Σ k p :: acc) (TProv k s :: evs)
  | co_spawn m c' acc evs :
      Corr γ c w acc evs -> (forall fm, fibers γ m = Some fm -> fcomp fm = c') ->
      Corr γ c w (USpawn Σ m :: acc) (TSpawn c' :: evs).

  (** A name keeps its component: fibers present below the old counter were
      present before, with the same component. *)
  Definition NamesFixed (γ γ' : State) : Prop :=
    forall m fm', fibers γ' m = Some fm' -> m < next γ ->
      exists fm, fibers γ m = Some fm /\ fcomp fm = fcomp fm'.

  Lemma corr_mono (γ γ' : State) c w acc evs :
    Corr γ c w acc evs ->
    (forall k p t g, In (UOp Σ k p t g) acc -> oplog γ' t = oplog γ t) ->
    (forall k p, In (UProv Σ k p) acc -> inilog γ' p = inilog γ p) ->
    (forall m, In (USpawn Σ m) acc -> forall fm', fibers γ' m = Some fm' ->
       exists fm, fibers γ m = Some fm /\ fcomp fm = fcomp fm') ->
    Corr γ' c w acc evs.
  Proof.
    intros H; induction H as [|k p t g a acc evs H IH Ho Hr|k p s acc evs H IH Hi|m c' acc evs H IH Hc];
      intros Eo Ei Ef.
    all: try (constructor; fail).
    all: assert (IH' : Corr γ' c w acc evs) by
           (apply IH; [intros k1 p1 t1 g1 Hin; exact (Eo k1 p1 t1 g1 (or_intror Hin))
                      | intros k1 p1 Hin; exact (Ei k1 p1 (or_intror Hin))
                      | intros m1 Hin; exact (Ef m1 (or_intror Hin))]).
    - apply co_op; [exact IH' | rewrite (Eo k p t g (or_introl eq_refl)); exact Ho | exact Hr].
    - apply co_prov; [exact IH' | rewrite (Ei k p (or_introl eq_refl)); exact Hi].
    - apply co_spawn; [exact IH'|].
      intros fm' Hm'; destruct (Ef m (or_introl eq_refl) fm' Hm') as (fm & Hm & Hc'); rewrite <- Hc'; exact (Hc fm Hm).
  Qed.

  Lemma upu_tail (u : Undo) l : UPU Σ (u :: l) -> UPU Σ l.
  Proof.
    intros H k p l1 l2 E p' Hin.
    apply (H k p (u :: l1) l2 ltac:(rewrite E; reflexivity) p'); right; exact Hin.
  Qed.

  Lemma corr_find (γ : State) c w acc evs k p :
    Corr γ c w acc evs -> UPU Σ acc -> In (UProv Σ k p) acc ->
    exists s, inilog γ p = Some s /\ find_prov evs k = Some s.
  Proof.
    intros H; induction H as [|k' p' t g a acc evs H IH Ho Hr|k' p' s acc evs H IH Hi|m c' acc evs H IH Hc];
      intros U Hin.
    - destruct Hin.
    - destruct Hin as [E|Hin]; [discriminate|].
      exact (IH (upu_tail _ _ U) Hin).
    - cbn; destruct Hin as [E|Hin].
      + injection E as -> ->; exists s; split; [exact Hi|].
        destruct (K_eq_dec k k) as [_|]; [reflexivity | contradiction].
      + destruct (K_eq_dec k k') as [->|Hne].
        * exfalso; exact (U k' p' [] acc eq_refl p Hin).
        * exact (IH (upu_tail _ _ U) Hin).
    - destruct Hin as [E|Hin]; [discriminate|].
      exact (IH (upu_tail _ _ U) Hin).
  Qed.

  Lemma corr_item (γ : State) c w acc evs k p t g :
    Corr γ c w acc evs -> In (UOp Σ k p t g) acc ->
    if kmem K_eq_dec k (cdeps c) then lookup_view K_eq_dec k w = Some p else In (UProv Σ k p) acc.
  Proof.
    intros H; induction H as [|k' p' t' g' a acc evs H IH Ho Hr|k' p' s acc evs H IH Hi|m c' acc evs H IH Hc];
      intros Hin.
    - destruct Hin.
    - destruct Hin as [E|Hin].
      + injection E as -> -> -> ->; destruct (kmem K_eq_dec k (cdeps c)); [exact Hr | right; exact Hr].
      + specialize (IH Hin); destruct (kmem K_eq_dec k (cdeps c)); [exact IH | right; exact IH].
    - destruct Hin as [E|Hin]; [discriminate|].
      specialize (IH Hin); destruct (kmem K_eq_dec k (cdeps c)); [exact IH | right; exact IH].
    - destruct Hin as [E|Hin]; [discriminate|].
      specialize (IH Hin); destruct (kmem K_eq_dec k (cdeps c)); [exact IH | right; exact IH].
  Qed.

  Lemma corr_ops (γ : State) c w acc evs k :
    Corr γ c w acc evs -> map fst (itemsF γ k (uops acc)) = evOps k evs.
  Proof.
    intros H; induction H as [|k' p t g a acc evs H IH Ho Hr|k' p s acc evs H IH Hi|m c' acc evs H IH Hc].
    - reflexivity.
    - change (uops (UOp Σ k' p t g :: acc)) with ((k', p, t, g) :: uops acc).
      unfold itemsF, evOps in *; cbn [flat_map]; rewrite map_app.
      destruct (K_eq_dec k' k); [rewrite Ho|]; cbn [map app fst]; rewrite IH; reflexivity.
    - change (uops (UProv Σ k' p :: acc)) with (uops acc); exact IH.
    - change (uops (USpawn Σ m :: acc)) with (uops acc); exact IH.
  Qed.


  (** ** Helpers for the fiber's own operations *)
  Definition onat_eq_dec : forall x y : option nat, {x = y} + {x <> y}.
  Proof. decide equality; apply Nat.eq_dec. Defined.

  Lemma upu_unique (l : list Undo) k p p' : UPU Σ l -> In (UProv Σ k p) l -> In (UProv Σ k p') l -> p = p'.
  Proof.
    intros U H1 H2; destruct (Nat.eq_dec p p') as [E|Ne]; [exact E | exfalso].
    apply in_split in H1 as (l1 & l2 & E).
    apply (U k p l1 l2 E p'); rewrite E in H2; apply in_app_iff in H2 as [H2|[H2|H2]].
    - apply in_app_iff; left; exact H2.
    - injection H2 as E2; exfalso; exact (Ne E2).
    - apply in_app_iff; right; exact H2.
  Qed.

  Lemma sorted_items_eq {A} (l1 l2 : list (A * nat)) :
    StronglySorted lt (map snd l1) -> StronglySorted lt (map snd l2) ->
    (forall x, In x l1 <-> In x l2) -> l1 = l2.
  Proof.
    revert l2; induction l1 as [|x l1 IH]; intros [|y l2] S1 S2 E.
    - reflexivity.
    - exfalso; apply (proj2 (E y)); left; reflexivity.
    - exfalso; apply (proj1 (E x)); left; reflexivity.
    - cbn in S1, S2; apply StronglySorted_inv in S1 as [S1 F1]; apply StronglySorted_inv in S2 as [S2 F2].
      rewrite Forall_forall in F1, F2.
      assert (Exy : x = y).
      { destruct (proj1 (E x) (or_introl eq_refl)) as [<-|Hx]; [reflexivity|].
        destruct (proj2 (E y) (or_introl eq_refl)) as [->|Hy]; [reflexivity|].
        exfalso; pose proof (F2 (snd x) (in_map snd _ _ Hx)); pose proof (F1 (snd y) (in_map snd _ _ Hy)); lia. }
      subst y; f_equal; apply IH; [exact S1 | exact S2|].
      intros z; split; intros Hz.
      + destruct (proj1 (E z) (or_intror Hz)) as [<-|H]; [|exact H].
        exfalso; pose proof (F1 (snd x) (in_map snd _ _ Hz)); lia.
      + destruct (proj2 (E z) (or_intror Hz)) as [<-|H]; [|exact H].
        exfalso; pose proof (F2 (snd x) (in_map snd _ _ Hz)); lia.
  Qed.

  Lemma ss_filter {A} (f : A * nat -> bool) (l : list (A * nat)) :
    StronglySorted lt (map snd l) -> StronglySorted lt (map snd (filter f l)).
  Proof.
    induction l as [|x l IH]; cbn; [constructor|]; intros H; apply StronglySorted_inv in H as [H F].
    destruct (f x); cbn; [constructor; [exact (IH H)|] | exact (IH H)].
    rewrite Forall_forall in *; intros y Hy; apply F.
    apply in_map_iff in Hy as (z & <- & Hz); apply filter_In in Hz as [Hz _]; exact (in_map snd _ _ Hz).
  Qed.

  Lemma ss_rev_nat (l : list nat) : StronglySorted gt l -> StronglySorted lt (rev l).
  Proof.
    induction l as [|x l IH]; cbn; [constructor|]; intros H; apply StronglySorted_inv in H as [H F].
    apply ss_snoc; [exact (IH H)|]; rewrite Forall_forall in F.
    intros y Hy; apply in_rev in Hy; exact (F y Hy).
  Qed.

  (** The episode invariant: a Loading or Active fiber's accumulator is an
      ideal trace of its program, under the initial states of the
      provisions its view names. *)
  Definition epl (γ : State) (c : C) (l : Life) : Prop :=
    match l with
    | Loading _ P acc w => exists evs, Tr c (rho γ w) evs P /\ Corr γ c w acc evs
    | Active _ acc w => exists evs, Tr c (rho γ w) evs PDone /\ Corr γ c w acc evs
    | _ => True
    end.

  Definition EPInv (γ : State) : Prop :=
    forall m f, fibers γ m = Some f -> epl γ (fcomp f) (life f).

  Lemma ep_keep (γ γ' : State) m f :
    SInv γ -> fibers γ m = Some f ->
    (forall p, p < next γ -> inilog γ' p = inilog γ p) ->
    (forall t, t < next γ -> oplog γ' t = oplog γ t) ->
    NamesFixed γ γ' ->
    epl γ (fcomp f) (life f) -> epl γ' (fcomp f) (life f).
  Proof.
    intros SI Hm Ei Eo NFx.
    pose proof (sinv_wf γ SI) as W.
    assert (Hrho : forall w, view_of Σ (life f) = w -> forall k, rho γ w k = rho γ' w k).
    { intros w Hw k; unfold rho; destruct (lookup_view K_eq_dec k w) as [p|] eqn:Hp; [|reflexivity].
      apply lv_In in Hp; rewrite <- Hw in Hp.
      destruct (wf_view K_eq_dec Σ prog γ W m f k p Hm Hp) as (b & Hb & <- & _).
      symmetry; apply Ei; exact (wf_pids K_eq_dec Σ prog γ W k b Hb). }
    assert (HC : forall c w evs, Corr γ c w (acc_of (life f)) evs -> Corr γ' c w (acc_of (life f)) evs).
    { intros c w evs Co; apply (corr_mono γ γ' c w _ evs Co).
      - intros k p t g Hin; apply Eo.
        exact (proj1 (proj2 (proj2 (pv_fib Σ prog γ (sinv_prov γ SI) m f Hm) k p t g Hin))).
      - intros k p Hin; destruct (wf_uprov K_eq_dec Σ prog γ W m f k p Hm Hin) as (b & Hb & <- & _).
        apply Ei; exact (wf_pids K_eq_dec Σ prog γ W k b Hb).
      - intros m' Hin fm' Hm'; apply (NFx m' fm' Hm').
        exact (wf_spawn_lt K_eq_dec Σ prog γ W m f m' Hm Hin). }
    unfold epl; destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; auto;
      intros (evs & T & Co); exists evs; split;
      [ apply (tr_ext _ (rho γ w)); [apply Hrho; reflexivity | exact T]
      | exact (HC (fcomp f) w evs Co)
      | apply (tr_ext _ (rho γ w)); [apply Hrho; reflexivity | exact T]
      | exact (HC (fcomp f) w evs Co) ].
  Qed.

  Lemma ep_relife (γ γ1 : State) n f (l : Life) :
    SInv γ -> EPInv γ -> fibers γ1 = fibers γ ->
    (forall p, p < next γ -> inilog γ1 p = inilog γ p) ->
    (forall t, t < next γ -> oplog γ1 t = oplog γ t) ->
    NamesFixed γ (set_life Σ γ1 n f l) ->
    fibers γ n = Some f -> epl (set_life Σ γ1 n f l) (fcomp f) l ->
    EPInv (set_life Σ γ1 n f l).
  Proof.
    intros SI EP E Ei Eo NFx Hn Hl m fm Hm.
    unfold set_life, set_fiber, with_fibers, fupd in Hm; cbn in Hm.
    destruct (Nat.eqb_spec m n) as [->|Hne].
    - injection Hm as <-; exact Hl.
    - rewrite E in Hm; apply (ep_keep γ _ m fm SI Hm); [exact Ei | exact Eo | exact NFx | exact (EP m fm Hm)].
  Qed.

  Lemma ep_frame (γ γ' : State) :
    SInv γ -> EPInv γ ->
    (forall p, p < next γ -> inilog γ' p = inilog γ p) ->
    (forall t, t < next γ -> oplog γ' t = oplog γ t) ->
    NamesFixed γ γ' ->
    (forall m f', fibers γ' m = Some f' -> (exists z, life f' = Inactive Σ z) \/
       exists f, fibers γ m = Some f /\ fcomp f = fcomp f' /\ life f = life f') ->
    EPInv γ'.
  Proof.
    intros SI EP Ei Eo NFx H m f' Hm.
    destruct (H m f' Hm) as [[z Hz]|(f & Hf & Hc & Hl)]; [rewrite Hz; exact Logic.I|].
    rewrite <- Hc, <- Hl; exact (ep_keep γ γ' m f SI Hf Ei Eo NFx (EP m f Hf)).
  Qed.

  (** An operation's outcome is its outcome at the provision's initial state. *)
  Lemma ep_op (γ : State) n f k a κ acc w b s' g o :
    SInv γ -> EPInv γ ->
    fibers γ n = Some f -> life f = Loading Σ (POp k a κ) acc w ->
    op_binding K_eq_dec Σ prog γ n f k w = Some b -> run a (next γ) (bst b) = Some (s', g, o) ->
    NamesFixed γ (set_life Σ (bump Σ (log_op Σ (with_binds Σ γ (bupd K_eq_dec Σ (binds γ) k
                (Some (mkBinding Σ (pid b) (owner b) s')))) (next γ) a)) n f
           (Loading Σ (κ o) (UOp Σ k (pid b) (next γ) g :: acc) w)) ->
    EPInv (set_life Σ (bump Σ (log_op Σ (with_binds Σ γ (bupd K_eq_dec Σ (binds γ) k
                (Some (mkBinding Σ (pid b) (owner b) s')))) (next γ) a)) n f
           (Loading Σ (κ o) (UOp Σ k (pid b) (next γ) g :: acc) w)).
  Proof.
    intros SI EP Hn Hl Hob Hr NFx.
    pose proof (sinv_wf γ SI) as W.
    set (γ1 := bump Σ (log_op Σ (with_binds Σ γ (bupd K_eq_dec Σ (binds γ) k
                (Some (mkBinding Σ (pid b) (owner b) s')))) (next γ) a)).
    assert (Eo : forall t, t < next γ -> oplog γ1 t = oplog γ t).
    { intros t Ht; unfold γ1; cbn; rewrite (proj2 (Nat.eqb_neq t (next γ))); [reflexivity | lia]. }
    apply (ep_relife γ γ1 n f); [exact SI | exact EP | reflexivity | intros; reflexivity | exact Eo | exact NFx | exact Hn |].
    pose proof (EP n f Hn) as Ef; rewrite Hl in Ef; destruct Ef as (evs & T & Co).
    pose proof (op_binding_spec K_eq_dec Σ prog γ n f k w b Hob) as Hb.
    destruct (s_inv _ SI k b Hb) as (s0 & L & s & Hi & PL & R & Eq).
    assert (Hres : resolveI (fcomp f) (rho γ w) evs k = Some s0 /\
                   (if kmem K_eq_dec k (cdeps (fcomp f)) then lookup_view K_eq_dec k w = Some (pid b)
                    else In (UProv Σ k (pid b)) acc)).
    { unfold op_binding in Hob; unfold resolveI, rho.
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
    (* split the pending list into this fiber's operations and the others' *)
    set (own := flab onat_eq_dec (tokOwner γ) (Some n) L).
    set (oth := fnot onat_eq_dec (tokOwner γ) (Some n) L).
    pose proof (pend_cross γ k (pid b) L SI (conj Hs HL)) as CR.
    destruct (replay_shuffle_ex (CoPair k) Hwb (HCom k) onat_eq_dec (tokOwner γ) L (own ++ oth) s0 s CR
                (flab_partition onat_eq_dec (tokOwner γ) (Some n) L) R) as (sL & R' & Es).
    apply replay_app in R' as (sO & Rown & Roth).
    pose proof (wb_respects a (next γ) (Hwb a (next γ)) (bst b) sL (transitivity Eq Es)) as Hrs; rewrite Hr in Hrs.
    destruct (run a (next γ) sL) as [[[s2 g2] o2]|] eqn:Hr2; [|destruct Hrs].
    destruct Hrs as (_ & _ & <-).
    (* the others' operations do not change the outcome *)
    assert (Hoth : forall b0 u, In (b0, u) oth -> CoPair k b0 a /\ u <> next γ).
    { intros b0 u Hin; unfold oth, fnot in Hin; apply filter_In in Hin as [Hin Hlab]; cbn in Hlab.
      destruct (onat_eq_dec (tokOwner γ u) (Some n)) as [_|Nl]; [discriminate|].
      destruct (proj1 (HL b0 u) Hin) as [(m & fm & g' & Hm & I') Hb0].
      split; [|pose proof (uacc_bound γ m fm k (pid b) u g' SI Hm I'); lia].
      rewrite (tokOwner_spec γ m fm k (pid b) u g' SI Hm I') in Nl.
      destruct (item_op γ m fm k (pid b) u g' SI Hm I') as (b1 & Hb1 & Hop1).
      rewrite Hb0 in Hb1; injection Hb1 as <-.
      apply (copair_fibers γ m fm n f k b0 a SI); [congruence | exact Hm | exact Hn | exact Hop1 | exact Hopa]. }
    destruct (outcome_after (CoPair k) (HCom k) a (next γ) oth sO sL Hoth Roth s2 g2 o Hr2) as (sO' & gO & HrO).
    (* this fiber's operations at k are its trace's operations at k, in order *)
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
    { rewrite Eown, map_rev; unfold ownIt; rewrite map_map; cbn; rewrite map_id.
      unfold uacc; rewrite Hl; cbn [acc_of]; rewrite (corr_ops γ _ _ _ _ k Co); reflexivity. }
    destruct (replay_tokens Hwb HTI own (ownIt k evs) s0 sO Ef Rown s0 (reflexivity _)) as (s1i & Ri & Ei).
    pose proof (HTI a (next γ) 0 sO) as Ht; rewrite HrO in Ht.
    destruct (run a 0 sO) as [[[s3 g3] o3]|] eqn:Hr3; [|destruct Ht].
    destruct Ht as [_ <-].
    pose proof (wb_respects a 0 (Hwb a 0) sO s1i Ei) as Hrs'; rewrite Hr3 in Hrs'.
    destruct (run a 0 s1i) as [[[s4 g4] o4]|] eqn:Hr4; [|destruct Hrs'].
    destruct Hrs' as (_ & _ & <-).
    unfold epl; exists (TOp k a :: evs); split.
    - apply (tr_ext _ (rho γ w)); [intros; reflexivity|].
      eapply tr_op; [exact T | exact Hres | exact Ri | exact Hr4].
    - apply co_op; [| cbn; rewrite Nat.eqb_refl; reflexivity | exact Hif].
      apply (corr_mono γ _ _ _ _ _ Co); [| intros; reflexivity |].
      { intros k1 p1 t1 g1 Hin; apply Eo.
        assert (Hin' : In (UOp Σ k1 p1 t1 g1) (acc_of (life f))) by (rewrite Hl; exact Hin).
        exact (proj1 (proj2 (proj2 (pv_fib Σ prog γ (sinv_prov γ SI) n f Hn) k1 p1 t1 g1 Hin'))). }
      intros m Hin fm' Hm'; apply (NFx m fm' Hm').
      assert (Hin' : In (USpawn Σ m) (acc_of (life f))) by (rewrite Hl; exact Hin).
      exact (wf_spawn_lt K_eq_dec Σ prog γ W n f m Hn Hin').
  Qed.

  Lemma ep_provide (γ : State) n f k s P' acc w :
    SInv γ -> EPInv γ -> fibers γ n = Some f -> life f = Loading Σ (PProvide k s P') acc w ->
    NamesFixed γ (set_life Σ (bump Σ (log_ini Σ (with_binds Σ γ (bupd K_eq_dec Σ (binds γ) k
                (Some (mkBinding Σ (next γ) n s)))) (next γ) s)) n f
           (Loading Σ P' (UProv Σ k (next γ) :: acc) w)) ->
    EPInv (set_life Σ (bump Σ (log_ini Σ (with_binds Σ γ (bupd K_eq_dec Σ (binds γ) k
                (Some (mkBinding Σ (next γ) n s)))) (next γ) s)) n f
           (Loading Σ P' (UProv Σ k (next γ) :: acc) w)).
  Proof.
    intros SI EP Hn Hl NFx.
    pose proof (sinv_wf γ SI) as W.
    set (γ1 := bump Σ (log_ini Σ (with_binds Σ γ (bupd K_eq_dec Σ (binds γ) k
                (Some (mkBinding Σ (next γ) n s)))) (next γ) s)).
    assert (Ei : forall p, p < next γ -> inilog γ1 p = inilog γ p).
    { intros p Hp; unfold γ1; cbn; rewrite (proj2 (Nat.eqb_neq p (next γ))); [reflexivity | lia]. }
    apply (ep_relife γ γ1 n f); [exact SI | exact EP | reflexivity | exact Ei | intros; reflexivity | exact NFx | exact Hn |].
    pose proof (EP n f Hn) as Ef; rewrite Hl in Ef; destruct Ef as (evs & T & Co).
    unfold epl; exists (TProv k s :: evs); split.
    - apply (tr_ext _ (rho γ w)); [|apply tr_prov; exact T].
      intros k1; unfold rho; destruct (lookup_view K_eq_dec k1 w) as [p|] eqn:Hp; [|reflexivity].
      apply lv_In in Hp.
      assert (Hp' : In (k1, p) (view_of Σ (life f))) by (rewrite Hl; exact Hp).
      destruct (wf_view K_eq_dec Σ prog γ W n f k1 p Hn Hp') as (b1 & Hb1 & <- & _).
      symmetry; apply Ei; exact (wf_pids K_eq_dec Σ prog γ W k1 b1 Hb1).
    - apply co_prov; [|cbn; rewrite Nat.eqb_refl; reflexivity].
      apply (corr_mono γ _ _ _ _ _ Co); [intros; reflexivity | |].
      { intros k1 p1 Hin; apply Ei.
      assert (Hin' : In (UProv Σ k1 p1) (acc_of (life f))) by (rewrite Hl; exact Hin).
      destruct (wf_uprov K_eq_dec Σ prog γ W n f k1 p1 Hn Hin') as (b1 & Hb1 & <- & _).
      exact (wf_pids K_eq_dec Σ prog γ W k1 b1 Hb1). }
      intros m Hin fm' Hm'; apply (NFx m fm' Hm').
      assert (Hin' : In (USpawn Σ m) (acc_of (life f))) by (rewrite Hl; exact Hin).
      exact (wf_spawn_lt K_eq_dec Σ prog γ W n f m Hn Hin').
  Qed.

  Record PInv (γ : State) : Prop := { p_s : SInv γ; p_e : EPInv γ }.

  Lemma pinv_init : PInv (@init K Σ C).
  Proof. split; [exact sinv_init | intros m f H; discriminate]. Qed.

  (** Every step keeps names' components. *)
  Lemma step_names (γ γ' : State) ℓ : TInv K_eq_dec Σ prog Kb γ -> step γ ℓ = Some γ' -> NamesFixed γ γ'.
  Proof.
    intros I H m fm' Hm' Hlt.
    pose proof (t_wf K_eq_dec Σ prog Kb γ I) as W.
    destruct ℓ as [c|x|x|x|x|x|x|x|x|x|x|x i|x];
      [ cbn [step] in H; destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-;
        unfold bump, with_fibers, fupd in Hm'; cbn in Hm';
        destruct (Nat.eqb_spec m (next γ)); [lia | exists fm'; auto]
      | cbn [step] in H; destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate]; injection H as <-;
        unfold set_fiber, with_fibers, fupd in Hm'; cbn in Hm';
        destruct (Nat.eqb_spec m x) as [->|]; [injection Hm' as <-; exists f; auto | exists fm'; auto]
      | cbn [step] in H; destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate];
        destruct (life f) as [[z|]| | |]; try discriminate; injection H as <-;
        unfold set_life, set_fiber, with_fibers, fupd in Hm'; cbn in Hm';
        destruct (Nat.eqb_spec m x) as [->|]; [injection Hm' as <-; exists f; auto | exists fm'; auto]
      | idtac ..
      | cbn [step] in H; destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate];
        destruct (life f) as [| |acc w|]; try discriminate;
        destruct (nth_error (reacts Σ (prog (fcomp f))) i) as [c|]; [|discriminate];
        destruct (disposed f || conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-;
        unfold set_life, set_fiber, bump, with_fibers, fupd in Hm'; cbn in Hm';
        destruct (Nat.eqb_spec m x) as [->|];
        [injection Hm' as <-; exists f; auto
        | destruct (Nat.eqb_spec m (next γ)); [lia | exists fm'; auto]]
      | idtac ].
    9: { (* ORestart *)
      cbn [step] in H; destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (disposed f); [discriminate|].
      destruct (life f) as [|P acc w|acc w|]; try discriminate; injection H as <-.
      all: unfold set_life, set_fiber, with_fibers, fupd in Hm'; cbn in Hm'.
      all: destruct (Nat.eqb_spec m x) as [->|]; [injection Hm' as <-; exists f; auto | exists fm'; auto]. }
    all: match type of H with _ ?l = Some _ =>
           assert (Hin : In l (lifecycle_labels x)) by (cbn; tauto) end.
    all: destruct (fibers γ x) as [fx|] eqn:Hx;
      [| rewrite (step_absent K_eq_dec Σ prog γ x _ Hx Hin) in H; discriminate].
    all: destruct (lstep_effects K_eq_dec Σ prog Kb rank Hrank γ γ' x _ fx I Hin H Hx) as (E1 & E2 & E3 & _).
    all: destruct (Nat.eq_dec m x) as [->|Hne];
      [ destruct (E3 fm' Hm') as [Hc _]; exists fx; split; [exact Hx | symmetry; exact Hc]
      | destruct (fibers γ m) as [fm|] eqn:Hm;
        [ destruct (E1 m fm Hne Hm) as [E|[E _]]; rewrite E in Hm'; injection Hm' as <-; exists fm; auto
        | destruct (E2 m fm' Hm Hm') as [-> _]; lia ] ].
  Qed.

  (** Spawning records the child's component. *)
  Lemma ep_spawn (γ : State) n f c' P' acc w :
    SInv γ -> EPInv γ -> fibers γ n = Some f -> life f = Loading Σ (PSpawn c' P') acc w ->
    let γ' := set_life Σ (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ)
                (Some (mkFiber Σ c' (Some n) false (Inactive Σ None)))))) n f
                (Loading Σ P' (USpawn Σ (next γ) :: acc) w) in
    NamesFixed γ γ' -> EPInv γ'.
  Proof.
    intros SI EP Hn Hl γ' NFx m fm Hm.
    pose proof (sinv_wf γ SI) as W.
    pose proof (wf_names K_eq_dec Σ prog γ W n f Hn) as Hnlt.
    assert (Hm0 := Hm).
    unfold γ', set_life, set_fiber, bump, with_fibers, fupd in Hm; cbn in Hm.
    destruct (Nat.eqb_spec m n) as [->|Hne].
    - injection Hm as <-.
      pose proof (EP n f Hn) as Ef; rewrite Hl in Ef; destruct Ef as (evs & T & Co).
      change (epl γ' (fcomp f) (Loading Σ P' (USpawn Σ (next γ) :: acc) w)).
      unfold epl; exists (TSpawn c' :: evs); split.
      + apply (tr_ext _ (rho γ w)); [intros; reflexivity | apply tr_spawn; exact T].
      + apply co_spawn.
        * apply (corr_mono γ _ _ _ _ _ Co); [intros; reflexivity | intros; reflexivity |].
          intros m' Hin fm' Hm'; apply (NFx m' fm' Hm').
          assert (Hin' : In (USpawn Σ m') (acc_of (life f))) by (rewrite Hl; exact Hin).
          exact (wf_spawn_lt K_eq_dec Σ prog γ W n f m' Hn Hin').
        * intros fm' Hm'; unfold γ', set_life, set_fiber, bump, with_fibers, fupd in Hm'; cbn in Hm'.
          rewrite (proj2 (Nat.eqb_neq (next γ) n) ltac:(lia)), Nat.eqb_refl in Hm'.
          injection Hm' as <-; reflexivity.
    - destruct (Nat.eqb_spec m (next γ)) as [->|Hne'].
      + injection Hm as <-; exact Logic.I.
      + apply (ep_keep γ γ' m fm SI Hm); [intros; reflexivity | intros; reflexivity | exact NFx | exact (EP m fm Hm)].
  Qed.

  Local Ltac relife SI EP NFx Hx :=
    apply (ep_relife _ _ _ _ _ SI EP);
      [reflexivity | intros; reflexivity | intros; reflexivity | exact NFx | exact Hx |].

  (** A reaction adds a child the startup trace does not hold, so it is
      excluded: the episode invariant is about startup. *)
  Theorem pinv_step (γ γ' : State) ℓ : (forall n i, ℓ <> OReact n i) ->
    PInv γ -> step γ ℓ = Some γ' -> PInv γ'.
  Proof.
    intros Hnr [SI EP] H; split; [exact (sinv_step γ γ' ℓ SI H)|].
    pose proof (sinv_wf γ SI) as W.
    pose proof (step_names γ γ' ℓ (c0_t K_eq_dec Σ prog Kb γ (s_c _ SI)) H) as NFx.
    destruct ℓ as [c|x|x|x|x|x|x|x|x|x|x|x i|x]; cbn [step] in H.
    - (* OInsert *)
      destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      apply (ep_frame γ); [exact SI | exact EP | intros; reflexivity | intros; reflexivity | exact NFx |].
      intros m f' Hm; unfold bump, with_fibers, fupd in Hm; cbn in Hm.
      destruct (Nat.eqb_spec m (next γ)); [injection Hm as <-; left; exists None; reflexivity|].
      right; exists f'; auto.
    - (* ODispose *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate]; injection H as <-.
      apply (ep_frame γ); [exact SI | exact EP | intros; reflexivity | intros; reflexivity | exact NFx |].
      intros m f' Hm; unfold set_fiber, with_fibers, fupd in Hm; cbn in Hm.
      destruct (Nat.eqb_spec m x) as [->|]; [injection Hm as <-; right; exists f; auto | right; exists f'; auto].
    - (* OReset *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]|P acc w|acc w|acc w z] eqn:Hl; try discriminate; injection H as <-.
      relife SI EP NFx Hx; exact Logic.I.
    - (* LBegin *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]|P acc w|acc w|acc w z] eqn:Hl;
        repeat match type of H with context [match ?e with _ => _ end] => destruct e end;
        try discriminate; injection H as <-.
      relife SI EP NFx Hx; exists []; split; constructor.
    - (* LStep *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      dif H; [injection H as <- | discriminate].
      revert NFx; destruct P as [| |k a κ|k s P'|c P'].
      + cbn [load_step]; intros NFx; relife SI EP NFx Hx.
        pose proof (ep_keep γ (set_life Σ γ x f (Active Σ acc w)) x f SI Hx
                      ltac:(intros; reflexivity) ltac:(intros; reflexivity) NFx (EP x f Hx)) as E.
        rewrite Hl in E; exact E.
      + cbn [load_step]; intros NFx; relife SI EP NFx Hx; exact Logic.I.
      + rewrite (load_step_op K_eq_dec Σ prog γ x f k a κ acc w).
        destruct (op_binding K_eq_dec Σ prog γ x f k w) as [b|] eqn:Hob.
        * destruct (run a (next γ) (bst b)) as [[[s' g] o]|] eqn:Hr; intros NFx.
          -- exact (ep_op γ x f k a κ acc w b s' g o SI EP Hx Hl Hob Hr NFx).
          -- relife SI EP NFx Hx; exact Logic.I.
        * intros NFx; relife SI EP NFx Hx; exact Logic.I.
      + cbn [load_step].
        destruct (kmem K_eq_dec k (provs Σ (prog (fcomp f)))).
        * destruct (binds γ k) as [b0|] eqn:Hb; intros NFx.
          -- relife SI EP NFx Hx; exact Logic.I.
          -- exact (ep_provide γ x f k s P' acc w SI EP Hx Hl NFx).
        * intros NFx; relife SI EP NFx Hx; exact Logic.I.
      + cbn [load_step]; destruct (conflict K_eq_dec Σ prog γ c); intros NFx.
        * relife SI EP NFx Hx; exact Logic.I.
        * exact (ep_spawn γ x f c P' acc w SI EP Hx Hl NFx).
    - (* LDivert *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      dif H; [discriminate | injection H as <-].
      relife SI EP NFx Hx; exact Logic.I.
    - (* LLeave *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      dif H; [discriminate | injection H as <-].
      relife SI EP NFx Hx; exact Logic.I.
    - (* LUndo *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      destruct u as [k p t g|k p|m]; cbn [undo_step] in H.
      + destruct (binds γ k) as [b|] eqn:Hb; [destruct (Nat.eqb (pid b) p)|];
          injection H as <-; relife SI EP NFx Hx; exact Logic.I.
      + dif H; [discriminate|].
        destruct (binds γ k) as [b|] eqn:Hb; [destruct (Nat.eqb (pid b) p)|];
          injection H as <-; relife SI EP NFx Hx; exact Logic.I.
      + destruct (fibers γ m); [discriminate | injection H as <-].
        relife SI EP NFx Hx; exact Logic.I.
    - (* LRetireChild *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|[|u acc] w z] eqn:Hl; try discriminate.
      destruct u as [k p t g|k p|m]; try discriminate.
      destruct (fibers γ m) as [g|] eqn:Hm; [|discriminate].
      dif H; [discriminate | injection H as <-].
      apply (ep_frame γ); [exact SI | exact EP | intros; reflexivity | intros; reflexivity | exact NFx |].
      intros m' f' Hm'; unfold set_fiber, with_fibers, fupd in Hm'; cbn in Hm'.
      destruct (Nat.eqb_spec m' m) as [->|]; [injection Hm' as <-; right; exists g; auto | right; exists f'; auto].
    - (* LUnloaded *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|[|u acc] w z] eqn:Hl; try discriminate; injection H as <-.
      relife SI EP NFx Hx; exact Logic.I.
    - (* LRemove *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      dif H; [injection H as <- | discriminate].
      apply (ep_frame γ); [exact SI | exact EP | intros; reflexivity | intros; reflexivity | exact NFx |].
      intros m f' Hm; unfold with_fibers, fupd in Hm; cbn in Hm.
      destruct (Nat.eqb_spec m x); [discriminate | right; exists f'; auto].
    - exfalso; exact (Hnr x i eq_refl).
    - (* ORestart *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (disposed f); [discriminate|].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate; injection H as <-;
      (relife SI EP NFx Hx; exact Logic.I).
  Qed.

  Lemma lrun_pinv (γ0 γ : State) : PInv γ0 -> LRun K_eq_dec Σ prog γ0 γ -> PInv γ.
  Proof.
    intros I R; induction R as [γ|γ ℓ γ1 γ2 Hlc Hs _ IH]; [exact I|].
    exact (IH (pinv_step γ γ1 ℓ (lifecycle_not_react ℓ Hlc) I Hs)).
  Qed.

End Episode.
