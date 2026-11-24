(** * Confluence, part 1: one execution

    Within one execution, every binding's state is, up to ≃, its initial
    state followed by the operations still pending on it, in token order
    ([INV]); every step keeps this ([sinv_step]). The ghost logs [oplog] and
    [inilog] name the operations and the initial states.

    Later parts: [Episode] (ideal traces), [StateConf] (service states,
    without spawn), [SpawnConf] (systems with spawn). *)

From Stdlib Require Import List PeanoNat Bool Lia RelationClasses Permutation Sorted Wf_nat.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering
  Recovery Progress Termination Confluence.
Import ListNotations.

Section StateInv.
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
  (** Operations two fibers may perform at one key ([Recovery.CoPair]). *)
  Local Notation CoPair := (Recovery.CoPair Σ prog).
  Local Notation CoPair_sym := (Recovery.CoPair_sym Σ prog).


  Hypothesis Hwb : forall a t, WellBehaved (Σ := Σ) a t.
  Hypothesis HUI : forall (a : Op Σ) (t : nat) (s1 s2 s1' s2' : S) (g1 g2 : S -> S) (o1 o2 : Out Σ),
    run a t s1 = Some (s1', g1, o1) -> run a t s2 = Some (s2', g2, o2) -> fun_eq (Σ := Σ) g1 g2.
  Hypothesis HTI : forall (a : Op Σ) (t t' : nat) (s : S),
    match run a t s, run a t' s with
    | None, None => True
    | Some (s1, _, o1), Some (s2, _, o2) => @st_eq Σ s1 s2 /\ o1 = o2
    | _, _ => False
    end.
  Hypothesis HRI : forall (k : K) (a b : Op Σ) (ta tb : nat) (g : S -> S), CoPair k a b -> ta <> tb ->
    yields (Σ := Σ) a ta g ->
    forall x, After (CoPair k a) a ta x -> shifted_ok (Σ := Σ) g (run b tb x) (run b tb (g x)).
  Hypothesis HCom : forall (k : K) (a b : Op Σ) (ta tb : nat), CoPair k a b -> ta <> tb ->
    Commute (Σ := Σ) a ta b tb.

  (** ** Operation items *)
  Local Notation Itm := (K * nat * nat * (S -> S))%type.

  Fixpoint uops (l : list Undo) : list Itm :=
    match l with
    | [] => []
    | UOp _ k p t g :: l' => (k, p, t, g) :: uops l'
    | _ :: l' => uops l'
    end.

  Definition itok (x : Itm) : nat := snd (fst x).

  Lemma in_uops k p t g l : In (k, p, t, g) (uops l) <-> In (UOp Σ k p t g) l.
  Proof.
    induction l as [|u l IH]; cbn; [tauto|].
    destruct u as [k' p' t' g'|k' p'|m]; cbn; rewrite IH; split; intros H;
      try tauto; try (destruct H as [H|H]; [discriminate | tauto]);
      try (right; exact H).
    - destruct H as [H|H]; [left; injection H as -> -> -> ->; reflexivity | right; exact H].
    - destruct H as [H|H]; [left; injection H as -> -> -> ->; reflexivity | right; exact H].
  Qed.

  Definition uacc (f : Fiber) : list Itm := uops (acc_of (life f)).

  (** The per-fiber invariant: items are sorted by decreasing token, and each
      was performed by an operation of the fiber's component, logged under
      its token. *)
  Definition GF (γ : State) (f : Fiber) : Prop :=
    StronglySorted gt (map itok (uacc f)) /\
    forall k p t g, In (k, p, t, g) (uacc f) ->
      exists a, oplog γ t = Some a /\ OpAt Σ k a (cbody (fcomp f)) /\
        exists s s' o, run a t s = Some (s', g, o).

  Definition Item (γ : State) (k : K) (p t : nat) : Prop :=
    exists m fm g, fibers γ m = Some fm /\ In (k, p, t, g) (uacc fm).

  Definition PendList (γ : State) (k : K) (p : nat) (L : list (Op Σ * nat)) : Prop :=
    StronglySorted lt (map snd L) /\
    forall a t, In (a, t) L <-> (Item γ k p t /\ oplog γ t = Some a).

  Definition BindInv (γ : State) (k : K) (b : Binding Σ) : Prop :=
    exists s0 L s, inilog γ (pid b) = Some s0 /\ PendList γ k (pid b) L /\
                   Replay L s0 s /\ bst b ≃ s.

  Definition INV (γ : State) : Prop :=
    forall k b, binds γ k = Some b -> BindInv γ k b.

  Record SInv (γ : State) : Prop := {
    s_c : CInv0 γ;
    s_gf : forall m f, fibers γ m = Some f -> GF γ f;
    s_inv : INV γ
  }.

  Lemma sinv_init : SInv (@init K Σ C).
  Proof.
    split; [exact (cinv_0 K_eq_dec Σ prog Kb _ (cinv_init K_eq_dec Σ prog Kb)) | intros m f H; discriminate |].
    intros k b H; discriminate.
  Qed.

  Lemma sinv_prov (γ : State) : SInv γ -> Prov Σ prog γ.
  Proof. intros SI; exact (t_prov K_eq_dec Σ prog Kb γ (c0_t K_eq_dec Σ prog Kb γ (s_c _ SI))). Qed.

  Lemma sinv_wf (γ : State) : SInv γ -> WF γ.
  Proof. intros SI; exact (t_wf K_eq_dec Σ prog Kb γ (c0_t K_eq_dec Σ prog Kb γ (s_c _ SI))). Qed.

  (** ** List facts *)
  Lemma sorted_gt_unique (l : list Itm) x y :
    StronglySorted gt (map itok l) -> In x l -> In y l -> itok x = itok y -> x = y.
  Proof.
    induction l as [|z l IH]; intros Hs Hx Hy E; [destruct Hx|].
    cbn in Hs; apply StronglySorted_inv in Hs as [Hs Hf].
    rewrite Forall_forall in Hf.
    destruct Hx as [<-|Hx], Hy as [<-|Hy]; auto.
    - exfalso; specialize (Hf (itok y) (in_map _ _ _ Hy)); lia.
    - exfalso; specialize (Hf (itok x) (in_map _ _ _ Hx)); lia.
  Qed.

  Lemma sorted_head_max (x : Itm) l y :
    StronglySorted gt (map itok (x :: l)) -> In y l -> itok y < itok x.
  Proof.
    intros Hs Hy; cbn in Hs; apply StronglySorted_inv in Hs as [_ Hf].
    rewrite Forall_forall in Hf; specialize (Hf (itok y) (in_map _ _ _ Hy)); lia.
  Qed.

  Lemma sorted_suffix (pre l : list Itm) :
    StronglySorted gt (map itok (pre ++ l)) -> StronglySorted gt (map itok l).
  Proof.
    induction pre as [|x pre IH]; cbn; [auto|].
    intros H; apply StronglySorted_inv in H as [H _]; exact (IH H).
  Qed.

  Lemma ss_lt_nodup (l : list nat) : StronglySorted lt l -> NoDup l.
  Proof.
    induction l as [|x l IH]; intros Hs; constructor.
    - apply StronglySorted_inv in Hs as [_ Hf]; rewrite Forall_forall in Hf.
      intros Hx; specialize (Hf x Hx); lia.
    - apply StronglySorted_inv in Hs as [Hs _]; exact (IH Hs).
  Qed.

  Lemma ss_snoc (l : list nat) x :
    StronglySorted lt l -> (forall y, In y l -> y < x) -> StronglySorted lt (l ++ [x]).
  Proof.
    induction l as [|y l IH]; intros Hs Hb; cbn.
    - constructor; constructor.
    - apply StronglySorted_inv in Hs as [Hs Hf]; constructor.
      + apply IH; [exact Hs | intros z Hz; apply Hb; right; exact Hz].
      + rewrite Forall_forall in *; intros z Hz; apply in_app_iff in Hz as [Hz|[<-|[]]].
        * exact (Hf z Hz).
        * apply Hb; left; reflexivity.
  Qed.

  Lemma ss_remove (l1 l2 : list nat) x :
    StronglySorted lt (l1 ++ x :: l2) -> StronglySorted lt (l1 ++ l2).
  Proof.
    induction l1 as [|y l1 IH]; cbn; intros H; apply StronglySorted_inv in H as [Hs Hf].
    - exact Hs.
    - constructor; [exact (IH Hs)|].
      rewrite Forall_forall in *; intros z Hz; apply Hf.
      apply in_app_iff in Hz as [Hz|Hz]; apply in_app_iff; [left | right; right]; exact Hz.
  Qed.

  Lemma Sub_OpIn a (P Q : Prog) : Sub Σ P Q -> OpIn Σ a P -> OpIn Σ a Q.
  Proof.
    intros HS HO; induction HS.
    - exact HO.
    - eapply op_cont; exact (IHHS HO).
    - apply op_prov; exact (IHHS HO).
    - apply op_spawn; exact (IHHS HO).
  Qed.

  (** ** Items *)
  Lemma uacc_bound (γ : State) m f k p t g :
    SInv γ -> fibers γ m = Some f -> In (k, p, t, g) (uacc f) -> p < next γ /\ t < next γ.
  Proof.
    intros SI Hm I; unfold uacc in I; apply in_uops in I.
    destruct (proj2 (pv_fib Σ prog γ (sinv_prov γ SI) m f Hm) k p t g I) as (Hp & Ht & _).
    auto.
  Qed.

  Lemma item_lt (γ : State) k p t : SInv γ -> Item γ k p t -> t < next γ.
  Proof. intros SI (m & fm & g & Hm & Hin); exact (proj2 (uacc_bound γ m fm k p t g SI Hm Hin)). Qed.

  Lemma item_pid_lt (γ : State) k p t : SInv γ -> Item γ k p t -> p < next γ.
  Proof. intros SI (m & fm & g & Hm & Hin); exact (proj1 (uacc_bound γ m fm k p t g SI Hm Hin)). Qed.

  Lemma item_op (γ : State) m fm k p t g : SInv γ -> fibers γ m = Some fm -> In (k, p, t, g) (uacc fm) ->
    exists a, oplog γ t = Some a /\ OpAt Σ k a (cbody (fcomp fm)).
  Proof.
    intros SI Hm Hin.
    destruct (proj2 (s_gf _ SI m fm Hm) k p t g Hin) as (a & Ha & Hop & _).
    exists a; split; [exact Ha | exact Hop].
  Qed.

  (** Two items with the same token are the same item, in the same fiber. *)
  Lemma item_unique (γ : State) m1 fm1 m2 fm2 k1 p1 g1 k2 p2 g2 t :
    SInv γ -> fibers γ m1 = Some fm1 -> fibers γ m2 = Some fm2 ->
    In (k1, p1, t, g1) (uacc fm1) -> In (k2, p2, t, g2) (uacc fm2) ->
    m1 = m2 /\ k1 = k2 /\ p1 = p2.
  Proof.
    intros SI H1 H2 I1 I2.
    destruct (Nat.eq_dec m1 m2) as [<-|Hne].
    - rewrite H1 in H2; injection H2 as <-.
      pose proof (sorted_gt_unique _ _ _ (proj1 (s_gf _ SI m1 fm1 H1)) I1 I2 eq_refl) as E.
      injection E; auto.
    - exfalso; unfold uacc in I1, I2; apply in_uops in I1, I2.
      exact (pv_tok Σ prog γ (sinv_prov γ SI) m1 m2 fm1 fm2 k1 p1 g1 k2 p2 g2 t Hne H1 H2 I1 I2).
  Qed.

  Lemma tok_owner (γ : State) n f k p t g k1 p1 :
    SInv γ -> fibers γ n = Some f -> In (k, p, t, g) (uacc f) -> Item γ k1 p1 t ->
    k1 = k /\ p1 = p.
  Proof.
    intros SI Hn I (m & fm & g1 & Hm & I1).
    destruct (item_unique γ m fm n f k1 p1 g1 k p g t SI Hm Hn I1 I) as (_ & -> & ->); auto.
  Qed.

  (** The fiber holding the item under a token. *)
  Definition tokOwner (γ : State) (t : nat) : option nat :=
    find (fun m => match fibers γ m with
                   | Some f => existsb (fun x => Nat.eqb (itok x) t) (uacc f)
                   | None => false
                   end) (seq 0 (next γ)).

  Lemma tokOwner_spec (γ : State) m f k p t g :
    SInv γ -> fibers γ m = Some f -> In (k, p, t, g) (uacc f) -> tokOwner γ t = Some m.
  Proof.
    intros SI Hm I.
    destruct (tokOwner γ t) as [m'|] eqn:E; unfold tokOwner in E.
    - apply find_some in E as [Hin Hp]; cbv beta in Hp.
      destruct (fibers γ m') as [f'|] eqn:Hm'; [|discriminate].
      apply existsb_exists in Hp as ([[[k' p'] t'] g'] & I' & Et); apply Nat.eqb_eq in Et; cbn in Et; subst t'.
      destruct (item_unique γ m' f' m f k' p' g' k p g t SI Hm' Hm I' I) as (-> & _); reflexivity.
    - exfalso.
      assert (Hs : In m (seq 0 (next γ))).
      { apply in_seq; pose proof (wf_names K_eq_dec Σ prog γ (sinv_wf γ SI) m f Hm); lia. }
      pose proof (find_none _ _ E m Hs) as Hn; cbv beta in Hn; rewrite Hm in Hn.
      assert (Hx : existsb (fun x => Nat.eqb (itok x) t) (uacc f) = true).
      { apply existsb_exists; exists (k, p, t, g); split; [exact I | apply Nat.eqb_refl]. }
      congruence.
  Qed.

  (** Operations of two fibers at one key may meet. *)
  Lemma copair_fibers (γ : State) m fm m' fm' k a b :
    SInv γ -> m <> m' -> fibers γ m = Some fm -> fibers γ m' = Some fm' ->
    OpAt Σ k a (cbody (fcomp fm)) -> OpAt Σ k b (cbody (fcomp fm')) -> CoPair k a b.
  Proof. intros SI; exact (copair_wf K_eq_dec Σ prog γ m fm m' fm' k a b (sinv_wf γ SI)). Qed.

  (** In a pending list, operations of different fibers may meet. *)
  Lemma pend_cross (γ : State) k p L :
    SInv γ -> PendList γ k p L -> Cross (CoPair k) (tokOwner γ) L.
  Proof.
    intros SI [Hs HL] [a t] [b u] Hx Hy Hne; cbn in Hne |- *.
    apply HL in Hx as [(m & fm & g & Hm & Ix) Ha]; apply HL in Hy as [(m' & fm' & g' & Hm' & Iy) Hb].
    rewrite (tokOwner_spec γ m fm k p t g SI Hm Ix), (tokOwner_spec γ m' fm' k p u g' SI Hm' Iy) in Hne.
    destruct (item_op γ m fm k p t g SI Hm Ix) as (a' & Ha' & Hopa).
    destruct (item_op γ m' fm' k p u g' SI Hm' Iy) as (b' & Hb' & Hopb).
    rewrite Ha in Ha'; injection Ha' as <-; rewrite Hb in Hb'; injection Hb' as <-.
    apply (copair_fibers γ m fm m' fm' k a b SI); auto; congruence.
  Qed.

  Lemma ss_mid (l1 l2 : list nat) x y : StronglySorted lt (l1 ++ x :: l2) -> In y l2 -> x < y.
  Proof.
    induction l1 as [|z l1 IH]; cbn; intros H Hy; apply StronglySorted_inv in H as [H Hf].
    - rewrite Forall_forall in Hf; exact (Hf y Hy).
    - exact (IH H Hy).
  Qed.

  Lemma item_split (γ : State) n f k p t :
    fibers γ n = Some f ->
    (Item γ k p t <-> (exists g, In (k, p, t, g) (uacc f)) \/
       exists m fm g, m <> n /\ fibers γ m = Some fm /\ In (k, p, t, g) (uacc fm)).
  Proof.
    intros Hn; split.
    - intros (m & fm & g & Hm & I); destruct (Nat.eq_dec m n) as [->|Hne].
      + rewrite Hn in Hm; injection Hm as <-; left; exists g; exact I.
      + right; exists m, fm, g; auto.
    - intros [(g & I)|(m & fm & g & _ & Hm & I)]; [exists n, f, g | exists m, fm, g]; auto.
  Qed.

  Lemma item_relife (γ γ1 : State) n f (l : Life) k p t :
    fibers γ1 = fibers γ -> fibers γ n = Some f ->
    (Item (set_life Σ γ1 n f l) k p t <-> (exists g, In (k, p, t, g) (uops (acc_of l))) \/
       exists m fm g, m <> n /\ fibers γ m = Some fm /\ In (k, p, t, g) (uacc fm)).
  Proof.
    intros E Hn; split.
    - intros (m & fm & g & Hm & I).
      unfold set_life, set_fiber, with_fibers, fupd in Hm; cbn in Hm.
      destruct (Nat.eqb_spec m n) as [->|Hne].
      + injection Hm as <-; left; exists g; exact I.
      + right; exists m, fm, g; rewrite <- E; auto.
    - intros [(g & I)|(m & fm & g & Hne & Hm & I)].
      + exists n, (mkFiber Σ (fcomp f) (parent f) (disposed f) l), g; split; [|exact I].
        unfold set_life, set_fiber, with_fibers, fupd; cbn; rewrite Nat.eqb_refl; reflexivity.
      + exists m, fm, g; split; [|exact I].
        unfold set_life, set_fiber, with_fibers, fupd; cbn.
        rewrite (proj2 (Nat.eqb_neq m n) Hne), E; exact Hm.
  Qed.

  (** ** Frames *)
  Definition FR (γ γ' : State) : Prop :=
    forall m f', fibers γ' m = Some f' -> uacc f' = [] \/
      exists f pre, fibers γ m = Some f /\ fcomp f = fcomp f' /\ uacc f = pre ++ uacc f'.

  Definition FRB (γ γ' : State) : Prop :=
    forall m f, fibers γ m = Some f -> uacc f = [] \/
      exists f', fibers γ' m = Some f' /\ uacc f' = uacc f.

  Lemma item_back (γ γ' : State) k p t : FR γ γ' -> Item γ' k p t -> Item γ k p t.
  Proof.
    intros F (m & f' & g & H & I).
    destruct (F m f' H) as [E|(f & pre & Hf & _ & E)]; [rewrite E in I; destruct I|].
    exists m, f, g; split; [exact Hf | rewrite E; apply in_or_app; right; exact I].
  Qed.

  Lemma item_fwd (γ γ' : State) k p t : FRB γ γ' -> Item γ k p t -> Item γ' k p t.
  Proof.
    intros F (m & f & g & H & I).
    destruct (F m f H) as [E|(f' & Hf & E)]; [rewrite E in I; destruct I|].
    exists m, f', g; split; [exact Hf | rewrite E; exact I].
  Qed.

  Lemma gf_one (γ γ' : State) m f f' pre :
    SInv γ -> fibers γ m = Some f -> fcomp f = fcomp f' -> uacc f = pre ++ uacc f' ->
    (forall t, t < next γ -> oplog γ' t = oplog γ t) -> GF γ' f'.
  Proof.
    intros SI Hm Hc E Ho.
    destruct (s_gf _ SI m f Hm) as [Hs Hi]; split.
    - rewrite E in Hs; exact (sorted_suffix pre _ Hs).
    - intros k p t g I.
      assert (I0 : In (k, p, t, g) (uacc f)) by (rewrite E; apply in_or_app; right; exact I).
      destruct (Hi k p t g I0) as (a & Ha & Hop & Hr).
      exists a; split; [rewrite Ho; [exact Ha | exact (proj2 (uacc_bound γ m f k p t g SI Hm I0))]|].
      rewrite <- Hc; split; [exact Hop | exact Hr].
  Qed.

  Lemma gf_nil (γ : State) f : uacc f = [] -> GF γ f.
  Proof. intros E; split; rewrite E; [constructor | intros ? ? ? ? []]. Qed.

  Lemma gf_frame (γ γ' : State) :
    SInv γ -> FR γ γ' -> (forall t, t < next γ -> oplog γ' t = oplog γ t) ->
    forall m f', fibers γ' m = Some f' -> GF γ' f'.
  Proof.
    intros SI F Ho m f' H.
    destruct (F m f' H) as [E|(f & pre & Hf & Hc & E)];
      [exact (gf_nil γ' f' E) | exact (gf_one γ γ' m f f' pre SI Hf Hc E Ho)].
  Qed.

  Lemma inv_keep (γ γ' : State) k b :
    SInv γ -> binds γ k = Some b ->
    (forall p, p < next γ -> inilog γ' p = inilog γ p) ->
    (forall t, t < next γ -> oplog γ' t = oplog γ t) ->
    (forall t, Item γ' k (pid b) t <-> Item γ k (pid b) t) ->
    BindInv γ' k b.
  Proof.
    intros SI Hb Hil Hol HI.
    destruct (s_inv _ SI k b Hb) as (s0 & L & s & Hi & [Hs HL] & R & E).
    exists s0, L, s; split.
    { rewrite Hil; [exact Hi | exact (wf_pids K_eq_dec Σ prog γ (sinv_wf γ SI) k b Hb)]. }
    split; [|split; [exact R | exact E]].
    split; [exact Hs|]; intros a t; rewrite HL, HI.
    split; intros [I O]; split; auto.
    - rewrite Hol; [exact O | exact (item_lt γ k (pid b) t SI I)].
    - rewrite Hol in O; [exact O | exact (item_lt γ k (pid b) t SI I)].
  Qed.

  Lemma inv_frame (γ γ' : State) :
    SInv γ -> (forall k b, binds γ' k = Some b -> binds γ k = Some b) ->
    (forall p, p < next γ -> inilog γ' p = inilog γ p) ->
    (forall t, t < next γ -> oplog γ' t = oplog γ t) ->
    (forall k b t, binds γ' k = Some b -> (Item γ' k (pid b) t <-> Item γ k (pid b) t)) ->
    INV γ'.
  Proof.
    intros SI HB Hil Hol HI k b Hb.
    exact (inv_keep γ γ' k b SI (HB k b Hb) Hil Hol (fun t => HI k b t Hb)).
  Qed.

  (** A step that only relabels fibers, keeping or emptying their items. *)
  Lemma sinv_frame (γ γ' : State) :
    SInv γ -> CInv0 γ' -> FR γ γ' -> FRB γ γ' ->
    (forall k b, binds γ' k = Some b -> binds γ k = Some b) ->
    inilog γ' = inilog γ -> oplog γ' = oplog γ -> SInv γ'.
  Proof.
    intros SI CI F FB HB Hil Hol; split; [exact CI | |].
    - apply (gf_frame γ γ' SI F); intros t _; rewrite Hol; reflexivity.
    - apply (inv_frame γ γ' SI HB); [intros p _; rewrite Hil; reflexivity
                                     | intros t _; rewrite Hol; reflexivity|].
      intros k b t _; split; [apply item_back; exact F | apply item_fwd; exact FB].
  Qed.

  Lemma fr_set (γ γ1 : State) n f f' :
    fibers γ1 = fibers γ -> fibers γ n = Some f -> fcomp f' = fcomp f ->
    (uacc f' = [] \/ exists pre, uacc f = pre ++ uacc f') ->
    FR γ (set_fiber Σ γ1 n f').
  Proof.
    intros E Hn Hc H m fm Hm.
    unfold set_fiber, with_fibers, fupd in Hm; cbn in Hm.
    destruct (Nat.eqb_spec m n) as [->|Hne].
    - injection Hm as <-; destruct H as [H|(pre & H)]; [left; exact H|].
      right; exists f, pre; auto.
    - right; exists fm, []; split; [rewrite <- E; exact Hm | split; reflexivity].
  Qed.

  Lemma frb_set (γ γ1 : State) n f f' :
    fibers γ1 = fibers γ -> fibers γ n = Some f ->
    (uacc f = [] \/ uacc f' = uacc f) ->
    FRB γ (set_fiber Σ γ1 n f').
  Proof.
    intros E Hn H m fm Hm.
    destruct (Nat.eq_dec m n) as [->|Hne].
    - rewrite Hn in Hm; injection Hm as <-; destruct H as [H|H]; [left; exact H|].
      right; exists f'; split; [|exact H].
      unfold set_fiber, with_fibers, fupd; cbn; rewrite Nat.eqb_refl; reflexivity.
    - right; exists fm; split; [|reflexivity].
      unfold set_fiber, with_fibers, fupd; cbn; rewrite (proj2 (Nat.eqb_neq m n) Hne), E; exact Hm.
  Qed.

  Lemma fr_upd (γ γ1 : State) m o :
    fibers γ1 = fupd Σ (fibers γ) m o ->
    (forall f', o = Some f' -> uacc f' = []) ->
    (forall f, fibers γ m = Some f -> uacc f = []) ->
    FR γ γ1 /\ FRB γ γ1.
  Proof.
    intros E Ho Hold; split.
    - intros m' f' H; rewrite E in H; unfold fupd in H.
      destruct (Nat.eqb_spec m' m) as [->|Hne]; [left; exact (Ho f' H)|].
      right; exists f', []; auto.
    - intros m' f H; destruct (Nat.eq_dec m' m) as [->|Hne]; [left; exact (Hold f H)|].
      right; exists f; split; [|reflexivity].
      rewrite E; unfold fupd; rewrite (proj2 (Nat.eqb_neq _ _) Hne); exact H.
  Qed.

  (** Re-life a fiber in a state with the same fibers, bindings and logs. *)
  Lemma sinv_relife (γ γ1 : State) n f (l : Life) :
    SInv γ -> CInv0 (set_life Σ γ1 n f l) ->
    fibers γ1 = fibers γ -> binds γ1 = binds γ -> inilog γ1 = inilog γ -> oplog γ1 = oplog γ ->
    fibers γ n = Some f ->
    (uops (acc_of l) = [] /\ uacc f = [] \/ uops (acc_of l) = uacc f) ->
    SInv (set_life Σ γ1 n f l).
  Proof.
    intros SI CI Ef Eb Ei Eo Hn H.
    apply (sinv_frame γ); [exact SI | exact CI | | | | exact Ei | exact Eo].
    - unfold set_life; apply (fr_set γ γ1 n f); [exact Ef | exact Hn | reflexivity|].
      destruct H as [[H _]|H]; [left; exact H | right; exists []; exact (eq_sym H)].
    - unfold set_life; apply (frb_set γ γ1 n f); [exact Ef | exact Hn|].
      destruct H as [[_ H]|H]; [left; exact H | right; exact H].
    - intros k b Hb; rewrite <- Eb; exact Hb.
  Qed.

  (** ** The three steps that change pending operations *)

  (** Performing an operation appends it to its binding's pending list. *)
  Lemma sinv_op (γ : State) n f k a κ acc w b s' g o :
    SInv γ ->
    fibers γ n = Some f -> life f = Loading Σ (POp k a κ) acc w ->
    binds γ k = Some b -> run a (next γ) (bst b) = Some (s', g, o) ->
    let γ' := set_life Σ (bump Σ (log_op Σ (with_binds Σ γ (bupd K_eq_dec Σ (binds γ) k
                (Some (mkBinding Σ (pid b) (owner b) s')))) (next γ) a)) n f
                (Loading Σ (κ o) (UOp Σ k (pid b) (next γ) g :: acc) w) in
    CInv0 γ' -> SInv γ'.
  Proof.
    intros SI Hn Hl Hb Hr γ' CI.
    set (γ1 := bump Σ (log_op Σ (with_binds Σ γ (bupd K_eq_dec Σ (binds γ) k
                (Some (mkBinding Σ (pid b) (owner b) s')))) (next γ) a)) in γ'.
    assert (Hu : uacc f = uops acc) by (unfold uacc; rewrite Hl; reflexivity).
    assert (Hop : forall t, oplog γ' t = if Nat.eqb t (next γ) then Some a else oplog γ t)
      by (intros t; reflexivity).
    assert (Hol : forall t, t < next γ -> oplog γ' t = oplog γ t).
    { intros t Ht; rewrite Hop, (proj2 (Nat.eqb_neq t (next γ))); [reflexivity | lia]. }
    assert (Hit : forall k1 p1 t1, Item γ' k1 p1 t1 <->
              Item γ k1 p1 t1 \/ (k1 = k /\ p1 = pid b /\ t1 = next γ)).
    { intros k1 p1 t1; unfold γ'.
      rewrite (item_relife γ γ1 n f _ k1 p1 t1 eq_refl Hn), (item_split γ n f k1 p1 t1 Hn), Hu.
      cbn [acc_of uops]; split.
      - intros [(g' & [E|I])|R].
        + injection E as E1 E2 E3 _; right; auto.
        + left; left; exists g'; exact I.
        + left; right; exact R.
      - intros [[(g' & I)|R]|(-> & -> & ->)].
        + left; exists g'; right; exact I.
        + right; exact R.
        + left; exists g; left; reflexivity. }
    assert (Hsub : Sub Σ (POp k a κ) (cbody (fcomp f)))
      by exact (proj1 (pv_fib Σ prog γ (sinv_prov γ SI) n f Hn) _ _ _ Hl).
    split; [exact CI | |].
    - (* per-fiber *)
      intros m fm Hm; unfold γ', set_life, set_fiber, with_fibers, fupd in Hm; cbn in Hm.
      destruct (Nat.eqb_spec m n) as [->|Hne].
      + injection Hm as <-.
        destruct (s_gf _ SI n f Hn) as [Hs Hi]; rewrite Hu in Hs, Hi.
        unfold GF, uacc; cbn [life acc_of uops fcomp Calculus.comp]; split.
        * cbn [map]; constructor; [exact Hs|].
          rewrite Forall_forall; intros x Hx; apply in_map_iff in Hx as ((((k1, p1), t1), g1) & <- & Hx).
          assert (Hx' : In (k1, p1, t1, g1) (uacc f)) by (rewrite Hu; exact Hx).
          unfold itok; cbn; exact (proj2 (uacc_bound γ n f k1 p1 t1 g1 SI Hn Hx')).
        * intros k1 p1 t1 g1 [E|I].
          -- injection E as <- <- <- <-; exists a; split; [rewrite Hop, Nat.eqb_refl; reflexivity|].
             split; [exact (Sub_OpAt Σ k a _ _ Hsub (at_here Σ k a κ)) | exists (bst b), s', o; exact Hr].
          -- destruct (Hi k1 p1 t1 g1 I) as (a1 & Ha1 & Hr1).
             exists a1; split; [|exact Hr1].
             assert (I' : In (k1, p1, t1, g1) (uacc f)) by (rewrite Hu; exact I).
             rewrite Hol; [exact Ha1 | exact (proj2 (uacc_bound γ n f k1 p1 t1 g1 SI Hn I'))].
      + exact (gf_one γ γ' m fm fm [] SI Hm eq_refl eq_refl Hol).
    - (* bindings *)
      intros k' b' Hb'; unfold γ', γ1 in Hb'; cbn in Hb'; unfold bupd, keqb in Hb'.
      destruct (K_eq_dec k' k) as [->|Hne].
      + injection Hb' as <-.
        destruct (s_inv _ SI k b Hb) as (s0 & L & s & Hi & [Hs HL] & R & Eq).
        pose proof (wb_respects a (next γ) (Hwb a (next γ)) (bst b) s Eq) as Hres.
        rewrite Hr in Hres.
        destruct (run a (next γ) s) as [[[s2 g2] o2]|] eqn:Hr2; [|destruct Hres].
        destruct Hres as (Es & _ & _).
        exists s0, (L ++ [(a, next γ)]), s2; cbn [pid bst Calculus.pid Calculus.bst].
        split; [exact Hi|]; split; [split|split].
        * rewrite map_app; cbn; apply ss_snoc; [exact Hs|].
          intros y Hy; apply in_map_iff in Hy as ([a' t'] & <- & Hy); apply HL in Hy as [Hy _].
          exact (item_lt γ k (pid b) t' SI Hy).
        * intros a' t'; rewrite in_app_iff, Hit, Hop; cbn [In]; split.
          -- intros [I|[E|[]]].
             ++ apply HL in I as [I O]; split; [left; exact I|].
                rewrite (proj2 (Nat.eqb_neq t' (next γ))); [exact O|].
                pose proof (item_lt γ k (pid b) t' SI I); lia.
             ++ injection E as <- <-; split; [right; auto | rewrite Nat.eqb_refl; reflexivity].
          -- intros [[I|(_ & _ & ->)] O].
             ++ left; apply HL; split; [exact I|].
                rewrite (proj2 (Nat.eqb_neq t' (next γ))) in O; [exact O|].
                pose proof (item_lt γ k (pid b) t' SI I); lia.
             ++ right; left; rewrite Nat.eqb_refl in O; injection O as ->; reflexivity.
        * apply replay_app; exists s; split; [exact R|].
          econstructor; [exact Hr2 | constructor].
        * exact Es.
      + apply (inv_keep γ γ' k' b' SI Hb'); [intros p _; reflexivity | exact Hol|].
        intros t; rewrite Hit; split; [intros [I|(E & _)]; [exact I | congruence] | intros I; left; exact I].
  Qed.

  (** Providing a key starts an empty pending list at the new pid. *)
  Lemma sinv_provide (γ : State) n f k s P' P acc w :
    SInv γ ->
    fibers γ n = Some f -> life f = Loading Σ P acc w -> binds γ k = None ->
    let γ' := set_life Σ (bump Σ (log_ini Σ (with_binds Σ γ (bupd K_eq_dec Σ (binds γ) k
                (Some (mkBinding Σ (next γ) n s)))) (next γ) s)) n f
                (Loading Σ P' (UProv Σ k (next γ) :: acc) w) in
    CInv0 γ' -> SInv γ'.
  Proof.
    intros SI Hn Hl Hb γ' CI.
    assert (Hu : uacc f = uops acc) by (unfold uacc; rewrite Hl; reflexivity).
    assert (F : FR γ γ').
    { unfold γ', set_life; apply (fr_set γ _ n f); [reflexivity | exact Hn | reflexivity|].
      right; exists []; rewrite Hu; reflexivity. }
    assert (FB : FRB γ γ').
    { unfold γ', set_life; apply (frb_set γ _ n f); [reflexivity | exact Hn|].
      right; rewrite Hu; reflexivity. }
    assert (HI : forall k1 p1 t1, Item γ' k1 p1 t1 <-> Item γ k1 p1 t1)
      by (intros; split; [apply item_back; exact F | apply item_fwd; exact FB]).
    split; [exact CI | apply (gf_frame γ γ' SI F); intros; reflexivity |].
    intros k' b' Hb'; unfold γ' in Hb'; cbn in Hb'; unfold bupd, keqb in Hb'.
    destruct (K_eq_dec k' k) as [->|Hne].
    - injection Hb' as <-; exists s, [], s; cbn [pid bst Calculus.pid Calculus.bst].
      split; [unfold γ'; cbn; rewrite Nat.eqb_refl; reflexivity|].
      split; [split; [constructor|]|split; [constructor | reflexivity]].
      intros a t; split; [intros []|]; intros [I _]; rewrite HI in I.
      pose proof (item_pid_lt γ k (next γ) t SI I); lia.
    - apply (inv_keep γ γ' k' b' SI Hb'); [|intros; reflexivity | intros; apply HI].
      intros p Hp; unfold γ'; cbn; rewrite (proj2 (Nat.eqb_neq p (next γ))); [reflexivity | lia].
  Qed.

  (** Popping an operation item. *)
  Lemma item_pop (γ γ1 : State) n f k p t g acc w z :
    SInv γ -> fibers γ1 = fibers γ -> fibers γ n = Some f ->
    life f = Unloading Σ (UOp Σ k p t g :: acc) w z ->
    forall k1 p1 t1, Item (set_life Σ γ1 n f (Unloading Σ acc w z)) k1 p1 t1 <->
                     Item γ k1 p1 t1 /\ t1 <> t.
  Proof.
    intros SI E Hn Hl k1 p1 t1.
    assert (Hu : uacc f = (k, p, t, g) :: uops acc) by (unfold uacc; rewrite Hl; reflexivity).
    pose proof (proj1 (s_gf _ SI n f Hn)) as Hs; rewrite Hu in Hs.
    rewrite (item_relife γ γ1 n f _ k1 p1 t1 E Hn), (item_split γ n f k1 p1 t1 Hn), Hu.
    cbn [acc_of]; split.
    - intros [(g' & I)|R].
      + split; [left; exists g'; right; exact I|].
        pose proof (sorted_head_max _ _ _ Hs I) as Ht; unfold itok in Ht; cbn in Ht; lia.
      + split; [right; exact R|]; intros ->.
        destruct R as (m & fm & g' & Hne & Hm & I).
        assert (Ix : In (k, p, t, g) (uacc f)) by (rewrite Hu; left; reflexivity).
        destruct (item_unique γ m fm n f k1 p1 g' k p g t SI Hm Hn I Ix) as (E1 & _); contradiction.
    - intros [[(g' & [Ex|I])|R] Hne].
      + injection Ex as _ _ E3 _; congruence.
      + left; exists g'; exact I.
      + right; exact R.
  Qed.

  Lemma gf_pop (γ γ1 : State) n f k p t g acc w z :
    SInv γ -> fibers γ1 = fibers γ -> oplog γ1 = oplog γ -> fibers γ n = Some f ->
    life f = Unloading Σ (UOp Σ k p t g :: acc) w z ->
    forall m fm, fibers (set_life Σ γ1 n f (Unloading Σ acc w z)) m = Some fm ->
      GF (set_life Σ γ1 n f (Unloading Σ acc w z)) fm.
  Proof.
    intros SI E Eo Hn Hl.
    apply (gf_frame γ _ SI); [|intros t' _; cbn; rewrite Eo; reflexivity].
    unfold set_life; apply (fr_set γ γ1 n f); [exact E | exact Hn | reflexivity|].
    right; exists [(k, p, t, g)]; unfold uacc; rewrite Hl; reflexivity.
  Qed.

  (** The popped item's binding is the one it acted on: apply its inverse. *)
  Lemma sinv_pop_hit (γ : State) n f k t g acc w z b :
    SInv γ ->
    fibers γ n = Some f -> life f = Unloading Σ (UOp Σ k (pid b) t g :: acc) w z ->
    binds γ k = Some b ->
    let γ' := set_life Σ (with_binds Σ γ (bupd K_eq_dec Σ (binds γ) k
                (Some (mkBinding Σ (pid b) (owner b) (g (bst b)))))) n f (Unloading Σ acc w z) in
    CInv0 γ' -> SInv γ'.
  Proof.
    intros SI Hn Hl Hb γ' CI.
    pose proof (item_pop γ (with_binds Σ γ (bupd K_eq_dec Σ (binds γ) k
      (Some (mkBinding Σ (pid b) (owner b) (g (bst b)))))) n f k (pid b) t g acc w z SI eq_refl Hn Hl) as Hit.
    assert (Hu : uacc f = (k, pid b, t, g) :: uops acc) by (unfold uacc; rewrite Hl; reflexivity).
    assert (Ix : In (k, pid b, t, g) (uacc f)) by (rewrite Hu; left; reflexivity).
    split; [exact CI | exact (gf_pop γ _ n f k (pid b) t g acc w z SI eq_refl eq_refl Hn Hl) |].
    intros k' b' Hb'; unfold γ' in Hb'; cbn in Hb'; unfold bupd, keqb in Hb'.
    destruct (K_eq_dec k' k) as [->|Hne].
    - injection Hb' as <-.
      destruct (s_inv _ SI k b Hb) as (s0 & L & s & Hi & [Hs HL] & R & Eq).
      destruct (proj2 (s_gf _ SI n f Hn) k (pid b) t g Ix) as (a & Ha & Hop & sx & sx' & ox & Hx).
      assert (IL : In (a, t) L) by (apply HL; split; [exists n, f, g; auto | exact Ha]).
      apply in_split in IL as (l1 & l2 & EL).
      pose proof (ss_lt_nodup _ Hs) as ND.
      pose proof (pend_cross γ k (pid b) L SI (conj Hs HL)) as CR.
      pose proof Hs as Hs'; rewrite EL, map_app in Hs'; cbn [map] in Hs'.
      rewrite EL, map_app in ND; cbn [map] in ND.
      pose proof (NoDup_remove_2 _ _ _ ND) as NT.
      pose proof (tokOwner_spec γ n f k (pid b) t g SI Hn Ix) as Htn.
      pose proof (proj1 (s_gf _ SI n f Hn)) as Hsf; rewrite Hu in Hsf.
      assert (Hl2 : forall b0 tb, In (b0, tb) l2 -> CoPair k a b0 /\ tb <> t).
      { intros b0 tb Hin.
        assert (Htb : tb <> t) by (intros ->; apply NT; apply in_or_app; right; exact (in_map snd _ _ Hin)).
        split; [|exact Htb].
        assert (InL : In (b0, tb) L) by (rewrite EL; apply in_or_app; right; right; exact Hin).
        assert (InA : In (a, t) L) by (rewrite EL; apply in_or_app; right; left; reflexivity).
        apply (CR (a, t) (b0, tb) InA InL); cbn; rewrite Htn; intros Eo.
        pose proof (ss_mid _ _ _ _ Hs' (in_map snd _ _ Hin)) as Hlt; cbn in Hlt.
        apply HL in InL as [(m & fm & g' & Hm & I') _].
        rewrite (tokOwner_spec γ m fm k (pid b) tb g' SI Hm I') in Eo; injection Eo as Emn; subst m.
        rewrite Hn in Hm; injection Hm as <-.
        rewrite Hu in I'; destruct I' as [E'|I'].
        - injection E' as E3 _; exact (Htb (eq_sym E3)).
        - pose proof (sorted_head_max _ _ _ Hsf I') as Hlt'; unfold itok in Hlt'; cbn in Hlt'; lia. }
      rewrite EL in R.
      destruct (replay_remove (CoPair k) Hwb HUI (HRI k) a t g l1 l2 s0 s
                  Hl2 (ex_intro _ sx (ex_intro _ sx' (ex_intro _ ox Hx))) R)
        as (s' & R' & Es').
      exists s0, (l1 ++ l2), s'; cbn [pid bst Calculus.pid Calculus.bst].
      split; [exact Hi|]; split; [split|split; [exact R'|]].
      + rewrite EL, map_app in Hs; cbn [map] in Hs; rewrite map_app; exact (ss_remove _ _ _ Hs).
      + intros a' t'; unfold γ'; rewrite Hit; split.
        * intros I12.
          assert (IL : In (a', t') L) by
            (rewrite EL; apply in_app_iff in I12 as [I|I]; apply in_or_app; [left | right; right]; exact I).
          apply HL in IL as [I O]; split; [split; [exact I|] | exact O].
          intros ->; apply NT; rewrite <- map_app; exact (in_map snd _ _ I12).
        * intros [[I Hne] O].
          assert (IL : In (a', t') L) by (apply HL; split; [exact I | exact O]).
          rewrite EL in IL; apply in_app_iff in IL as [IL|[E|IL]]; apply in_or_app;
            [left; exact IL | injection E as _ <-; contradiction | right; exact IL].
      + etransitivity; [exact (wb_inv a t (Hwb a t) sx sx' g ox Hx (bst b) s Eq) | exact Es'].
    - apply (inv_keep γ γ' k' b' SI Hb'); [intros; reflexivity | intros; reflexivity|].
      intros t'; unfold γ'; rewrite Hit; split; [intros [I _]; exact I|].
      intros I; split; [exact I|]; intros ->.
      destruct (tok_owner γ n f k (pid b) t g k' (pid b') SI Hn Ix I) as [E _]; contradiction.
  Qed.

  (** A stale item: its binding is gone or replaced; nothing to do. *)
  Lemma sinv_pop_miss (γ : State) n f k p t g acc w z :
    SInv γ ->
    fibers γ n = Some f -> life f = Unloading Σ (UOp Σ k p t g :: acc) w z ->
    (forall b, binds γ k = Some b -> pid b <> p) ->
    CInv0 (set_life Σ γ n f (Unloading Σ acc w z)) ->
    SInv (set_life Σ γ n f (Unloading Σ acc w z)).
  Proof.
    intros SI Hn Hl Hm CI.
    pose proof (item_pop γ γ n f k p t g acc w z SI eq_refl Hn Hl) as Hit.
    assert (Ix : In (k, p, t, g) (uacc f)) by (unfold uacc; rewrite Hl; left; reflexivity).
    split; [exact CI | exact (gf_pop γ γ n f k p t g acc w z SI eq_refl eq_refl Hn Hl) |].
    apply (inv_frame γ _ SI); [intros k' b' H; exact H | intros; reflexivity | intros; reflexivity|].
    intros k' b' t' Hb'; rewrite Hit; split; [intros [I _]; exact I|].
    intros I; split; [exact I|]; intros ->.
    destruct (tok_owner γ n f k p t g k' (pid b') SI Hn Ix I) as [-> E].
    exact (Hm b' Hb' E).
  Qed.

  Lemma fr_upd1 (γ γ1 : State) m o :
    fibers γ1 = fupd Σ (fibers γ) m o -> (forall f', o = Some f' -> uacc f' = []) -> FR γ γ1.
  Proof.
    intros E Ho m' f' H; rewrite E in H; unfold fupd in H.
    destruct (Nat.eqb_spec m' m) as [->|Hne]; [left; exact (Ho f' H)|].
    right; exists f', []; auto.
  Qed.

  Lemma frb_upd1 (γ γ1 : State) m o :
    fibers γ1 = fupd Σ (fibers γ) m o -> (forall f, fibers γ m = Some f -> uacc f = []) -> FRB γ γ1.
  Proof.
    intros E Hold m' f H; destruct (Nat.eq_dec m' m) as [->|Hne]; [left; exact (Hold f H)|].
    right; exists f; split; [|reflexivity].
    rewrite E; unfold fupd; rewrite (proj2 (Nat.eqb_neq _ _) Hne); exact H.
  Qed.

  Local Ltac dif H := match type of H with context [if ?b then _ else _] => destruct b end.

  (** ** Preservation *)
  Theorem sinv_step (γ γ' : State) ℓ : SInv γ -> step γ ℓ = Some γ' -> SInv γ'.
  Proof.
    intros SI H.
    pose proof (cinv0_step K_eq_dec Σ prog Kb HK Total γ γ' ℓ (s_c _ SI) H) as CI.
    pose proof (sinv_wf γ SI) as W.
    destruct ℓ as [c|x|x|x|x|x|x|x|x|x|x|x i|x]; cbn [step] in H.
    - (* OInsert *)
      destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      apply (sinv_frame γ); [exact SI | exact CI | | | intros k b Hb; exact Hb | reflexivity | reflexivity].
      + eapply fr_upd1; [reflexivity | intros f' [= <-]; reflexivity].
      + eapply frb_upd1; [reflexivity|].
        intros f Hf; exfalso; pose proof (wf_names K_eq_dec Σ prog γ W _ f Hf); lia.
    - (* ODispose *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate]; injection H as <-.
      apply (sinv_frame γ); [exact SI | exact CI | | | intros k b Hb; exact Hb | reflexivity | reflexivity].
      + apply (fr_set γ γ x f); [reflexivity | exact Hx | reflexivity | right; exists []; reflexivity].
      + apply (frb_set γ γ x f); [reflexivity | exact Hx | right; reflexivity].
    - (* OReset *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]|P acc w|acc w|acc w z] eqn:Hl; try discriminate; injection H as <-.
      apply (sinv_relife γ); try reflexivity; [exact SI | exact CI | exact Hx|].
      left; split; [reflexivity | unfold uacc; rewrite Hl; reflexivity].
    - (* LBegin *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]|P acc w|acc w|acc w z] eqn:Hl;
        repeat match type of H with context [match ?e with _ => _ end] => destruct e end;
        try discriminate; injection H as <-.
      apply (sinv_relife γ); try reflexivity; [exact SI | exact CI | exact Hx|].
      left; split; [reflexivity | unfold uacc; rewrite Hl; reflexivity].
    - (* LStep *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      dif H; [injection H as <- | discriminate].
      assert (Hu : uacc f = uops acc) by (unfold uacc; rewrite Hl; reflexivity).
      revert CI; destruct P as [| |k a κ|k s P'|c P'].
      + cbn [load_step]; intros CI.
        apply (sinv_relife γ); try reflexivity; [exact SI | exact CI | exact Hx | right; exact (eq_sym Hu)].
      + cbn [load_step]; intros CI.
        apply (sinv_relife γ); try reflexivity; [exact SI | exact CI | exact Hx | right; exact (eq_sym Hu)].
      + rewrite (load_step_op K_eq_dec Σ prog γ x f k a κ acc w).
        destruct (op_binding K_eq_dec Σ prog γ x f k w) as [b|] eqn:Hob.
        * destruct (run a (next γ) (bst b)) as [[[s' g] o]|] eqn:Hr; intros CI.
          -- exact (sinv_op γ x f k a κ acc w b s' g o SI Hx Hl
                      (op_binding_spec K_eq_dec Σ prog γ x f k w b Hob) Hr CI).
          -- apply (sinv_relife γ); try reflexivity;
               [exact SI | exact CI | exact Hx | right; exact (eq_sym Hu)].
        * intros CI; apply (sinv_relife γ); try reflexivity;
            [exact SI | exact CI | exact Hx | right; exact (eq_sym Hu)].
      + cbn [load_step].
        destruct (kmem K_eq_dec k (provs Σ (prog (fcomp f)))).
        * destruct (binds γ k) as [b0|] eqn:Hb; intros CI.
          -- apply (sinv_relife γ); try reflexivity;
               [exact SI | exact CI | exact Hx | right; exact (eq_sym Hu)].
          -- exact (sinv_provide γ x f k s P' _ acc w SI Hx Hl Hb CI).
        * intros CI; apply (sinv_relife γ); try reflexivity;
            [exact SI | exact CI | exact Hx | right; exact (eq_sym Hu)].
      + cbn [load_step]; destruct (conflict K_eq_dec Σ prog γ c); intros CI.
        * apply (sinv_relife γ); try reflexivity; [exact SI | exact CI | exact Hx | right; exact (eq_sym Hu)].
        * apply (sinv_frame γ); [exact SI | exact CI | | | intros k b Hb; exact Hb | reflexivity | reflexivity].
          -- intros m fm Hm; unfold set_life, set_fiber, bump, with_fibers, fupd in Hm; cbn in Hm.
             destruct (Nat.eqb_spec m x) as [->|Hne].
             ++ injection Hm as <-; right; exists f, []; split; [exact Hx|]; split; [reflexivity|].
                unfold uacc; rewrite Hl; reflexivity.
             ++ destruct (Nat.eqb_spec m (next γ)) as [->|Hne'].
                ** injection Hm as <-; left; reflexivity.
                ** right; exists fm, []; auto.
          -- intros m f0 Hm; right; destruct (Nat.eq_dec m x) as [->|Hne].
             ++ rewrite Hx in Hm; injection Hm as <-.
                exists (mkFiber Σ (fcomp f) (parent f) (disposed f) (Loading Σ P' (USpawn Σ (next γ) :: acc) w)).
                split; [unfold set_life, set_fiber, bump, with_fibers, fupd; cbn; rewrite Nat.eqb_refl; reflexivity|].
                unfold uacc; rewrite Hl; reflexivity.
             ++ exists f0; split; [|reflexivity].
                pose proof (wf_names K_eq_dec Σ prog γ W m f0 Hm) as Hlt.
                unfold set_life, set_fiber, bump, with_fibers, fupd; cbn.
                rewrite (proj2 (Nat.eqb_neq m x) Hne), (proj2 (Nat.eqb_neq m (next γ)) ltac:(lia)); exact Hm.
    - (* LDivert *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      dif H; [discriminate | injection H as <-].
      apply (sinv_relife γ); try reflexivity; [exact SI | exact CI | exact Hx|].
      right; unfold uacc; rewrite Hl; reflexivity.
    - (* LLeave *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      dif H; [discriminate | injection H as <-].
      apply (sinv_relife γ); try reflexivity; [exact SI | exact CI | exact Hx|].
      right; unfold uacc; rewrite Hl; reflexivity.
    - (* LUndo *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      destruct u as [k p t g|k p|m]; cbn [undo_step] in H.
      + destruct (binds γ k) as [b|] eqn:Hb.
        * destruct (Nat.eqb_spec (pid b) p) as [<-|Hne]; injection H as <-.
          -- exact (sinv_pop_hit γ x f k t g acc w z b SI Hx Hl Hb CI).
          -- apply (sinv_pop_miss γ x f k p t g acc w z SI Hx Hl); [|exact CI].
             intros b' Hb'; rewrite Hb in Hb'; injection Hb' as <-; exact Hne.
        * injection H as <-; apply (sinv_pop_miss γ x f k p t g acc w z SI Hx Hl); [|exact CI].
          intros b' Hb'; rewrite Hb in Hb'; discriminate.
      + dif H; [discriminate|].
        destruct (binds γ k) as [b|] eqn:Hb; [destruct (Nat.eqb_spec (pid b) p)|];
          injection H as <-.
        * apply (sinv_frame γ); [exact SI | exact CI | | | | reflexivity | reflexivity].
          -- unfold set_life; apply (fr_set γ _ x f); [reflexivity | exact Hx | reflexivity|].
             right; exists []; unfold uacc; rewrite Hl; reflexivity.
          -- unfold set_life; apply (frb_set γ _ x f); [reflexivity | exact Hx|].
             right; unfold uacc; rewrite Hl; reflexivity.
          -- intros k' b' Hb'; cbn in Hb'; unfold bupd, keqb in Hb'.
             destruct (K_eq_dec k' k); [discriminate | exact Hb'].
        * apply (sinv_relife γ); try reflexivity; [exact SI | exact CI | exact Hx|].
          right; unfold uacc; rewrite Hl; reflexivity.
        * apply (sinv_relife γ); try reflexivity; [exact SI | exact CI | exact Hx|].
          right; unfold uacc; rewrite Hl; reflexivity.
      + destruct (fibers γ m); [discriminate | injection H as <-].
        apply (sinv_relife γ); try reflexivity; [exact SI | exact CI | exact Hx|].
        right; unfold uacc; rewrite Hl; reflexivity.
    - (* LRetireChild *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|[|u acc] w z] eqn:Hl; try discriminate.
      destruct u as [k p t g|k p|m]; try discriminate.
      destruct (fibers γ m) as [g|] eqn:Hm; [|discriminate].
      dif H; [discriminate | injection H as <-].
      apply (sinv_frame γ); [exact SI | exact CI | | | intros k b Hb; exact Hb | reflexivity | reflexivity].
      + apply (fr_set γ γ m g); [reflexivity | exact Hm | reflexivity | right; exists []; reflexivity].
      + apply (frb_set γ γ m g); [reflexivity | exact Hm | right; reflexivity].
    - (* LUnloaded *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|[|u acc] w z] eqn:Hl; try discriminate; injection H as <-.
      apply (sinv_relife γ); try reflexivity; [exact SI | exact CI | exact Hx|].
      left; split; [reflexivity | unfold uacc; rewrite Hl; reflexivity].
    - (* LRemove *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      dif H; [injection H as <- | discriminate].
      apply (sinv_frame γ); [exact SI | exact CI | | | intros k b Hb; exact Hb | reflexivity | reflexivity].
      + eapply fr_upd1; [reflexivity | intros f' [=]].
      + eapply frb_upd1; [reflexivity|].
        intros f0 Hf0; rewrite Hx in Hf0; injection Hf0 as <-; unfold uacc; rewrite Hl; reflexivity.
    - (* OReact *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
      destruct (nth_error (reacts Σ (prog (fcomp f))) i) as [c|]; [|discriminate].
      destruct (disposed f || conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      apply (sinv_frame γ); [exact SI | exact CI | | | intros k b Hb; exact Hb | reflexivity | reflexivity].
      + intros m fm Hm; unfold set_life, set_fiber, bump, with_fibers, fupd in Hm; cbn in Hm.
        destruct (Nat.eqb_spec m x) as [->|Hne].
        * injection Hm as <-; right; exists f, []; split; [exact Hx|]; split; [reflexivity|].
          unfold uacc; rewrite Hl; reflexivity.
        * destruct (Nat.eqb_spec m (next γ)) as [->|Hne'].
          -- injection Hm as <-; left; reflexivity.
          -- right; exists fm, []; auto.
      + intros m f0 Hm; right; destruct (Nat.eq_dec m x) as [->|Hne].
        * rewrite Hx in Hm; injection Hm as <-.
          exists (mkFiber Σ (fcomp f) (parent f) (disposed f) (Active Σ (USpawn Σ (next γ) :: acc) w)).
          split; [unfold set_life, set_fiber, bump, with_fibers, fupd; cbn; rewrite Nat.eqb_refl; reflexivity|].
          unfold uacc; rewrite Hl; reflexivity.
        * exists f0; split; [|reflexivity].
          pose proof (wf_names K_eq_dec Σ prog γ W m f0 Hm) as Hlt.
          unfold set_life, set_fiber, bump, with_fibers, fupd; cbn.
          rewrite (proj2 (Nat.eqb_neq m x) Hne), (proj2 (Nat.eqb_neq m (next γ)) ltac:(lia)); exact Hm.
    - (* ORestart *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (disposed f); [discriminate|].
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate; injection H as <-;
      (apply (sinv_relife γ); try reflexivity; [exact SI | exact CI | exact Hx|];
       right; unfold uacc; rewrite Hl; reflexivity).
  Qed.

End StateInv.
