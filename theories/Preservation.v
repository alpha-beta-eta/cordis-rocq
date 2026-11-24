(** * Preservation (R3, first part)

    The well-formedness invariant [WF] holds at the initial state and is
    preserved by every rule. It is the counterpart of the paper's
    Definition 63 and Theorem 64, adapted to the v1 calculus. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service Calculus.
Import ListNotations.

Section Preservation.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).
  Local Notation Fiber := (@Fiber K Σ C).
  Local Notation Life := (@Life K Σ C).
  Local Notation Undo := (@Undo K Σ).
  Local Notation Binding := (@Binding Σ).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation next := (next Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation parent := (parent Σ).
  Local Notation disposed := (disposed Σ).
  Local Notation view_of := (view_of Σ).
  Local Notation acc_of := (acc_of Σ).
  Local Notation is_installed := (is_installed Σ).
  Local Notation pid := (pid Σ).
  Local Notation owner := (owner Σ).
  Local Notation step := (step K_eq_dec Σ prog).

  Definition fprovs (f : Fiber) : list K := provs Σ (prog (fcomp f)).
  Definition fdeps (f : Fiber) : list K := deps Σ (prog (fcomp f)).

  (** At most one provide undo item per key. *)
  Definition UPU (l : list Undo) : Prop :=
    forall k p l1 l2, l = l1 ++ UProv Σ k p :: l2 ->
    forall p', ~ In (UProv Σ k p') (l1 ++ l2).

  (** ** The invariant *)
  Record WF (γ : State) : Prop := {
    (** names, pids and spawned children are below the counter *)
    wf_names : forall n f, fibers γ n = Some f -> n < next γ;
    wf_pids : forall k b, binds γ k = Some b -> pid b < next γ;
    wf_spawn_lt : forall n f m,
      fibers γ n = Some f -> In (USpawn Σ m) (acc_of (life f)) -> m < next γ;
    (** a child's parent is installed and holds the undo item for it *)
    wf_parent : forall m fm q,
      fibers γ m = Some fm -> parent fm = Some q ->
      exists fq, fibers γ q = Some fq /\ is_installed (life fq) = true /\
                 In (USpawn Σ m) (acc_of (life fq));
    (** present fibers provide disjoint keys *)
    wf_disjoint : forall m n fm fn,
      m <> n -> fibers γ m = Some fm -> fibers γ n = Some fn ->
      overlaps K_eq_dec (fprovs fm) (fprovs fn) = false;
    (** every resolved dependency is bound, under the pid resolved, by
        another fiber *)
    wf_view : forall n f k p,
      fibers γ n = Some f -> In (k, p) (view_of (life f)) ->
      exists b, binds γ k = Some b /\ pid b = p /\ owner b <> n;
    wf_view_keys : forall n f,
      fibers γ n = Some f -> is_installed (life f) = true ->
      map fst (view_of (life f)) = fdeps f;
    (** every binding is owned by an installed fiber that may provide it and
        holds the undo item withdrawing it *)
    wf_bind : forall k b,
      binds γ k = Some b ->
      exists fo, fibers γ (owner b) = Some fo /\ is_installed (life fo) = true /\
                 kmem K_eq_dec k (fprovs fo) = true /\
                 In (UProv Σ k (pid b)) (acc_of (life fo));
    (** every provide undo item refers to the binding it created ... *)
    wf_uprov : forall n f k p,
      fibers γ n = Some f -> In (UProv Σ k p) (acc_of (life f)) ->
      exists b, binds γ k = Some b /\ pid b = p /\ owner b = n;
    (** ... and an accumulator holds at most one for each key *)
    wf_uprov_unique : forall n f, fibers γ n = Some f -> UPU (acc_of (life f))
  }.

  Lemma wf_init : WF (@init K Σ C).
  Proof. split; cbn; intros; discriminate. Qed.

  (** ** Lookups after updates *)
  Lemma fibers_set_life (γ : State) (n : nat) (f : Fiber) (l : Life) (m : nat) :
    fibers (set_life Σ γ n f l) m
    = if Nat.eqb m n then Some (mkFiber Σ (fcomp f) (parent f) (disposed f) l)
      else fibers γ m.
  Proof. reflexivity. Qed.

  Lemma fibers_set_life_inv (γ : State) (n : nat) (f : Fiber) (l : Life) (m : nat) (fm : Fiber) :
    fibers (set_life Σ γ n f l) m = Some fm ->
    (m = n /\ fm = mkFiber Σ (fcomp f) (parent f) (disposed f) l) \/
    (m <> n /\ fibers γ m = Some fm).
  Proof.
    rewrite fibers_set_life; destruct (Nat.eqb_spec m n) as [->|Hne].
    - intros [= <-]; left; auto.
    - intros H; right; auto.
  Qed.

  Lemma fibers_set_fiber_inv (γ : State) (n : nat) (f : Fiber) (m : nat) (fm : Fiber) :
    fibers (set_fiber Σ γ n f) m = Some fm ->
    (m = n /\ fm = f) \/ (m <> n /\ fibers γ m = Some fm).
  Proof.
    cbn; unfold fupd; destruct (Nat.eqb_spec m n) as [->|Hne].
    - intros [= <-]; left; auto.
    - intros H; right; auto.
  Qed.

  Lemma overlaps_sym (ks1 ks2 : list K) :
    overlaps K_eq_dec ks1 ks2 = overlaps K_eq_dec ks2 ks1.
  Proof.
    unfold overlaps, kmem.
    destruct (existsb _ ks1) eqn:E1, (existsb _ ks2) eqn:E2; try reflexivity.
    - apply existsb_exists in E1 as (k & Hk1 & Hk).
      apply existsb_exists in Hk as (k' & Hk2 & Hkk).
      unfold keqb in Hkk; destruct (K_eq_dec k k') as [<-|]; [|discriminate].
      exfalso; apply (proj2 (not_true_iff_false _) E2), existsb_exists.
      exists k; split; [exact Hk2|].
      apply existsb_exists; exists k; split; [exact Hk1|].
      unfold keqb; destruct (K_eq_dec k k); congruence.
    - apply existsb_exists in E2 as (k & Hk2 & Hk).
      apply existsb_exists in Hk as (k' & Hk1 & Hkk).
      unfold keqb in Hkk; destruct (K_eq_dec k k') as [<-|]; [|discriminate].
      exfalso; apply (proj2 (not_true_iff_false _) E1), existsb_exists.
      exists k; split; [exact Hk1|].
      apply existsb_exists; exists k; split; [exact Hk2|].
      unfold keqb; destruct (K_eq_dec k k); congruence.
  Qed.

  (** ** Changing one fiber without changing what the invariant reads

      The invariant reads an accumulator for three things: which children it
      waits for, which provisions it withdraws, and the uniqueness of the
      latter. [AccRel γ new old] says [new] agrees with [old] on them, where
      a child that is no longer present need not be waited for. *)
  Definition AccRel (γ : State) (new old : list Undo) : Prop :=
    (forall m, In (USpawn Σ m) new -> In (USpawn Σ m) old) /\
    (forall m, In (USpawn Σ m) old -> fibers γ m <> None -> In (USpawn Σ m) new) /\
    (forall k p, In (UProv Σ k p) new <-> In (UProv Σ k p) old) /\
    (UPU old -> UPU new).

  Lemma AccRel_refl (γ : State) (l : list Undo) : AccRel γ l l.
  Proof. repeat split; auto. Qed.

  Lemma wf_refiber (γ : State) (n : nat) (f f' : Fiber) :
    WF γ -> fibers γ n = Some f ->
    fcomp f' = fcomp f -> parent f' = parent f ->
    is_installed (life f') = is_installed (life f) ->
    view_of (life f') = view_of (life f) ->
    AccRel γ (acc_of (life f')) (acc_of (life f)) ->
    WF (set_fiber Σ γ n f').
  Proof.
    intros W Hn HC HP HI HV HA.
    assert (Hlook : forall m fm, fibers (set_fiber Σ γ n f') m = Some fm ->
              exists fm0, fibers γ m = Some fm0 /\ fcomp fm = fcomp fm0 /\
                          parent fm = parent fm0 /\
                          is_installed (life fm) = is_installed (life fm0) /\
                          view_of (life fm) = view_of (life fm0) /\
                          AccRel γ (acc_of (life fm)) (acc_of (life fm0))).
    { intros m fm H; apply fibers_set_fiber_inv in H as [[-> ->]|[_ H]].
      - exists f; auto 6.
      - exists fm; auto 7 using AccRel_refl. }
    assert (Hlook' : forall m fm0, fibers γ m = Some fm0 ->
              exists fm, fibers (set_fiber Σ γ n f') m = Some fm /\
                         fcomp fm = fcomp fm0 /\ parent fm = parent fm0 /\
                         is_installed (life fm) = is_installed (life fm0) /\
                         view_of (life fm) = view_of (life fm0) /\
                         AccRel γ (acc_of (life fm)) (acc_of (life fm0))).
    { intros m fm0 H; cbn; unfold fupd.
      destruct (Nat.eqb_spec m n) as [->|_].
      - rewrite Hn in H; injection H as <-.
        eexists; split; [reflexivity|]; auto 6.
      - exists fm0; auto 7 using AccRel_refl. }
    destruct W as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10]; split; cbn [next binds].
    - intros m fm H; destruct (Hlook m fm H) as (fm0 & H0 & _); eauto.
    - exact W2.
    - intros m fm q H Hq.
      destruct (Hlook m fm H) as (fm0 & H0 & _ & _ & _ & _ & Ha1 & _).
      eauto.
    - intros m fm q H Hp; destruct (Hlook m fm H) as (fm0 & H0 & _ & Hp0 & _).
      rewrite Hp0 in Hp; destruct (W4 m fm0 q H0 Hp) as (fq0 & Hq0 & Hiq & Hsq).
      destruct (Hlook' q fq0 Hq0) as (fq & Hq & _ & _ & Hi' & _ & _ & Ha2 & _).
      exists fq; rewrite Hi'; split; [exact Hq | split; [exact Hiq|]].
      apply Ha2; [exact Hsq | congruence].
    - intros m1 m2 f1 f2 Hne H1 H2.
      destruct (Hlook m1 f1 H1) as (g1 & G1 & Hc1 & _).
      destruct (Hlook m2 f2 H2) as (g2 & G2 & Hc2 & _).
      unfold fprovs; rewrite Hc1, Hc2; eapply W5; eauto.
    - intros m fm k p H Hin; destruct (Hlook m fm H) as (fm0 & H0 & _ & _ & _ & Hv0 & _).
      rewrite Hv0 in Hin; eauto.
    - intros m fm H Hinst; destruct (Hlook m fm H) as (fm0 & H0 & Hc & _ & Hi0 & Hv0 & _).
      unfold fdeps; rewrite Hc, Hv0; rewrite Hi0 in Hinst.
      exact (W7 m fm0 H0 Hinst).
    - intros k b Hb; destruct (W8 k b Hb) as (fo0 & Ho0 & Hio & Hko & Huo).
      destruct (Hlook' _ fo0 Ho0) as (fo & Ho & Hc & _ & Hi' & _ & _ & _ & Ha3 & _).
      exists fo; unfold fprovs; rewrite Hc, Hi'; repeat split; auto.
      apply Ha3; exact Huo.
    - intros m fm k p H Hin.
      destruct (Hlook m fm H) as (fm0 & H0 & _ & _ & _ & _ & _ & _ & Ha3 & _).
      apply Ha3 in Hin; eauto.
    - intros m fm H.
      destruct (Hlook m fm H) as (fm0 & H0 & _ & _ & _ & _ & _ & _ & _ & Ha4).
      apply Ha4; eauto.
  Qed.

  Lemma wf_relife (γ : State) (n : nat) (f : Fiber) (l : Life) :
    WF γ -> fibers γ n = Some f ->
    is_installed l = is_installed (life f) ->
    view_of l = view_of (life f) ->
    acc_of l = acc_of (life f) ->
    WF (set_life Σ γ n f l).
  Proof.
    intros W Hn Hi Hv Ha; eapply wf_refiber; eauto.
    cbn; rewrite Ha; apply AccRel_refl.
  Qed.

  Lemma wf_relife_acc (γ : State) (n : nat) (f : Fiber) (l : Life) :
    WF γ -> fibers γ n = Some f ->
    is_installed l = is_installed (life f) ->
    view_of l = view_of (life f) ->
    AccRel γ (acc_of l) (acc_of (life f)) ->
    WF (set_life Σ γ n f l).
  Proof. intros W Hn Hi Hv Ha; eapply wf_refiber; eauto. Qed.

  Lemma wf_set_disposed (γ : State) (n : nat) (f : Fiber) (b : bool) :
    WF γ -> fibers γ n = Some f ->
    WF (set_fiber Σ γ n (mkFiber Σ (fcomp f) (parent f) b (life f))).
  Proof. intros W Hn; eapply wf_refiber; eauto using AccRel_refl. Qed.

  (** Raising the counter keeps the invariant. *)
  Lemma wf_bump (γ : State) : WF γ -> WF (bump Σ γ).
  Proof.
    intros [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10]; split; cbn [next fibers binds bump];
      eauto; intros; [eapply Nat.lt_lt_succ_r; eauto ..].
  Qed.

  (** The ghost logs are not read by the invariant. *)
  Lemma wf_log_op (γ : State) t a : WF γ -> WF (log_op Σ γ t a).
  Proof. intros [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10]; split; cbn [next fibers binds log_op]; auto. Qed.

  Lemma wf_log_ini (γ : State) p s : WF γ -> WF (log_ini Σ γ p s).
  Proof. intros [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10]; split; cbn [next fibers binds log_ini]; auto. Qed.

  (** ** Simple rules *)
  Ltac step_inv H :=
    cbn [step] in H;
    repeat match type of H with
    | (match ?x with _ => _ end) = Some _ => destruct x eqn:?; try discriminate
    | (if ?x then _ else _) = Some _ => destruct x eqn:?; try discriminate
    | Some _ = Some _ => injection H as <-
    end.

  Lemma wf_ODispose (γ γ' : State) n :
    WF γ -> step γ (ODispose n) = Some γ' -> WF γ'.
  Proof. intros W H; step_inv H; apply wf_set_disposed; assumption. Qed.

  Lemma wf_OReset (γ γ' : State) n :
    WF γ -> step γ (OReset n) = Some γ' -> WF γ'.
  Proof.
    intros W H; step_inv H.
    apply wf_relife; auto; match goal with E : life _ = _ |- _ => rewrite E end; reflexivity.
  Qed.

  Lemma wf_LDivert (γ γ' : State) n :
    WF γ -> step γ (LDivert n) = Some γ' -> WF γ'.
  Proof.
    intros W H; step_inv H.
    apply wf_relife; auto; match goal with E : life _ = _ |- _ => rewrite E end; reflexivity.
  Qed.

  Lemma wf_LLeave (γ γ' : State) n :
    WF γ -> step γ (LLeave n) = Some γ' -> WF γ'.
  Proof.
    intros W H; step_inv H.
    apply wf_relife; auto; match goal with E : life _ = _ |- _ => rewrite E end; reflexivity.
  Qed.

  Lemma wf_LRetireChild (γ γ' : State) n :
    WF γ -> step γ (LRetireChild n) = Some γ' -> WF γ'.
  Proof. intros W H; step_inv H; apply wf_set_disposed; assumption. Qed.
  (** ** Accumulator lemmas *)
  Lemma upu_nil : UPU [].
  Proof. intros k p l1 l2 E; destruct l1; discriminate. Qed.

  Lemma upu_tail (u : Undo) (l : list Undo) : UPU (u :: l) -> UPU l.
  Proof.
    intros H k p l1 l2 E p' Hin.
    exact (H k p (u :: l1) l2 ltac:(rewrite E; reflexivity) p' (or_intror Hin)).
  Qed.

  Lemma upu_cons_nonprov (u : Undo) (l : list Undo) :
    (forall k p, u <> UProv Σ k p) -> UPU l -> UPU (u :: l).
  Proof.
    intros Hu H k p l1 l2 E p' Hin.
    destruct l1 as [|x l1]; cbn in E.
    - injection E as E _; exact (Hu k p E).
    - injection E as -> E; cbn in Hin; destruct Hin as [Hx|Hin].
      + exact (Hu k p' Hx).
      + exact (H k p l1 l2 E p' Hin).
  Qed.

  Lemma upu_cons_fresh (k : K) (p : nat) (l : list Undo) :
    UPU l -> (forall p', ~ In (UProv Σ k p') l) -> UPU (UProv Σ k p :: l).
  Proof.
    intros H Hf k0 p0 l1 l2 E p' Hin.
    destruct l1 as [|x l1]; cbn in E.
    - injection E as -> -> ->; exact (Hf p' Hin).
    - injection E as Ex E; subst x; cbn in Hin; destruct Hin as [Hx|Hin].
      + injection Hx as Hk _; subst k0.
        apply (Hf p0); rewrite E; apply in_or_app; right; left; reflexivity.
      + exact (H k0 p0 l1 l2 E p' Hin).
  Qed.

  Lemma AccRel_push_uop (γ : State) k p t g (l : list Undo) :
    AccRel γ (UOp Σ k p t g :: l) l.
  Proof.
    repeat split.
    - intros m [H|H]; [discriminate | exact H].
    - intros m H _; right; exact H.
    - intros [H|H]; [discriminate | exact H].
    - intros H; right; exact H.
    - apply upu_cons_nonprov; intros; discriminate.
  Qed.

  Lemma AccRel_pop_uop (γ : State) k p t g (l : list Undo) :
    AccRel γ l (UOp Σ k p t g :: l).
  Proof.
    repeat split.
    - intros m H; right; exact H.
    - intros m [H|H] _; [discriminate | exact H].
    - intros H; right; exact H.
    - intros [H|H]; [discriminate | exact H].
    - apply upu_tail.
  Qed.

  Lemma AccRel_pop_spawn (γ : State) m (l : list Undo) :
    fibers γ m = None -> AccRel γ l (USpawn Σ m :: l).
  Proof.
    intros Hm; repeat split.
    - intros m' H; right; exact H.
    - intros m' [H|H] Hp; [injection H as ->; contradiction | exact H].
    - intros H; right; exact H.
    - intros [H|H]; [discriminate | exact H].
    - apply upu_tail.
  Qed.

  (** ** Specifications of the derived notions *)
  Lemma fresh_none (γ : State) : WF γ -> fibers γ (next γ) = None.
  Proof.
    intros W; destruct (fibers γ (next γ)) as [f|] eqn:E; [|reflexivity].
    apply (wf_names _ W) in E; lia.
  Qed.

  Lemma in_names (γ : State) m fm : WF γ -> fibers γ m = Some fm -> In m (names Σ γ).
  Proof.
    intros W H; unfold names; apply in_seq; split; [lia|].
    cbn; eapply wf_names; eauto.
  Qed.

  Lemma conflict_false (γ : State) c m fm :
    WF γ -> conflict K_eq_dec Σ prog γ c = false -> fibers γ m = Some fm ->
    overlaps K_eq_dec (provs Σ (prog c)) (fprovs fm) = false.
  Proof.
    intros W Hc Hm; destruct (overlaps _ _ _) eqn:E; [|reflexivity].
    exfalso; apply (proj2 (not_true_iff_false _) Hc), existsb_exists.
    exists m; split; [eapply in_names; eauto|].
    rewrite Hm; exact E.
  Qed.

  Lemma relied_false (γ : State) n p m fm k :
    WF γ -> relied Σ γ n p = false -> fibers γ m = Some fm -> m <> n ->
    is_installed (life fm) = true -> In (k, p) (view_of (life fm)) -> False.
  Proof.
    intros W Hr Hm Hne Hi Hin.
    apply (proj2 (not_true_iff_false _) Hr), existsb_exists.
    exists m; split; [eapply in_names; eauto|].
    apply andb_true_iff; split.
    - apply negb_true_iff, Nat.eqb_neq; exact Hne.
    - unfold resolves; rewrite Hm, Hi; cbn.
      apply existsb_exists; exists (k, p); split; [exact Hin | apply Nat.eqb_refl].
  Qed.

  Lemma visible_spec (γ : State) k p :
    visible Σ γ k = Some p ->
    exists b fo, binds γ k = Some b /\ pid b = p /\
                 fibers γ (owner b) = Some fo /\ is_active Σ (life fo) = true.
  Proof.
    unfold visible; destruct (binds γ k) as [b|]; [|discriminate].
    destruct (fibers γ (owner b)) as [fo|] eqn:Ho; [|discriminate].
    destruct (is_active Σ (life fo)) eqn:Ha; [|discriminate].
    intros [= <-]; exists b, fo; auto.
  Qed.

  Lemma resolve_spec (γ : State) (ks : list K) w :
    resolve Σ γ ks = Some w ->
    map fst w = ks /\ forall k p, In (k, p) w -> visible Σ γ k = Some p.
  Proof.
    revert w; induction ks as [|k ks IH]; cbn; intros w H.
    - injection H as <-; split; [reflexivity | intros _ _ []].
    - destruct (visible Σ γ k) as [p|] eqn:Ev; [|discriminate].
      destruct (resolve Σ γ ks) as [w'|]; [|discriminate].
      injection H as <-; destruct (IH w' eq_refl) as [IH1 IH2].
      split; [cbn; f_equal; exact IH1|].
      intros k' p' [Heq|Hin]; [injection Heq as <- <-; exact Ev | exact (IH2 _ _ Hin)].
  Qed.

  Lemma target_spec (γ : State) n f w :
    fibers γ n = Some f -> target Σ prog γ n = Some w ->
    resolve Σ γ (fdeps f) = Some w.
  Proof.
    intros Hn; unfold target; rewrite Hn.
    destruct (disposed f); [discriminate | auto].
  Qed.

  Lemma active_installed (l : Life) : is_active Σ l = true -> is_installed l = true.
  Proof. destruct l; cbn; congruence. Qed.

  (** ** Updating the state of a binding *)
  Lemma wf_bind_state (γ : State) k b s' :
    WF γ -> binds γ k = Some b ->
    WF (with_binds Σ γ (bupd K_eq_dec Σ (binds γ) k
                          (Some (mkBinding Σ (pid b) (owner b) s')))).
  Proof.
    intros W Hb; destruct W as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
    split; cbn [with_binds binds fibers next]; unfold bupd, keqb; auto.
    - intros k' b'; destruct (K_eq_dec k' k) as [->|_]; [|apply W2].
      intros [= <-]; cbn; eapply W2; eauto.
    - intros n f k' p Hn Hin; destruct (W6 n f k' p Hn Hin) as (b0 & Hb0 & Hp0 & Ho0).
      destruct (K_eq_dec k' k) as [->|_]; [|eauto].
      rewrite Hb in Hb0; injection Hb0 as <-.
      eexists; split; [reflexivity|]; cbn; auto.
    - intros k' b'; destruct (K_eq_dec k' k) as [->|_]; [|apply W8].
      intros [= <-]; cbn; exact (W8 k b Hb).
    - intros n f k' p Hn Hin; destruct (W9 n f k' p Hn Hin) as (b0 & Hb0 & Hp0 & Ho0).
      destruct (K_eq_dec k' k) as [->|_]; [|eauto].
      rewrite Hb in Hb0; injection Hb0 as <-.
      eexists; split; [reflexivity|]; cbn; auto.
  Qed.

  (** ** Inserting a fiber *)
  Lemma wf_OInsert (γ γ' : State) c :
    WF γ -> step γ (OInsert c) = Some γ' -> WF γ'.
  Proof.
    intros W H; cbn [step] in H.
    destruct (conflict K_eq_dec Σ prog γ c) eqn:Hc; [discriminate|].
    injection H as <-.
    pose proof (fun m fm => conflict_false γ c m fm W Hc) as Hdis.
    destruct W as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
    set (N := next γ) in *.
    split; cbn [bump with_fibers next fibers binds]; unfold fupd.
    - intros m fm; destruct (Nat.eqb_spec m N) as [->|Hne]; [lia|].
      intros Hm; apply W1 in Hm; lia.
    - intros k b Hb; apply W2 in Hb; lia.
    - intros m fm m'; destruct (Nat.eqb_spec m N) as [->|Hne].
      + intros [= <-] [].
      + intros Hm Hin; pose proof (W3 m fm m' Hm Hin); lia.
    - intros m fm q; destruct (Nat.eqb_spec m N) as [->|Hne].
      + intros [= <-]; discriminate.
      + intros Hm Hp; destruct (W4 m fm q Hm Hp) as (fq & Hq & Hiq & Hsq).
        exists fq; destruct (Nat.eqb_spec q N) as [->|_]; [apply W1 in Hq; lia | auto].
    - intros m1 m2 f1 f2 Hne.
      destruct (Nat.eqb_spec m1 N) as [->|Hne1], (Nat.eqb_spec m2 N) as [->|Hne2].
      + contradiction.
      + intros [= <-] H2; exact (Hdis _ _ H2).
      + intros H1 [= <-]; rewrite overlaps_sym; exact (Hdis _ _ H1).
      + intros H1 H2; exact (W5 m1 m2 f1 f2 Hne H1 H2).
    - intros m fm k p; destruct (Nat.eqb_spec m N) as [->|Hne].
      + intros [= <-] [].
      + intros Hm Hin; eapply W6; eauto.
    - intros m fm; destruct (Nat.eqb_spec m N) as [->|Hne].
      + intros [= <-]; discriminate.
      + apply W7.
    - intros k b Hb; destruct (W8 k b Hb) as (fo & Ho & Hio & Hko & Huo).
      exists fo; destruct (Nat.eqb_spec (owner b) N) as [Heq|_];
        [apply W1 in Ho; lia | auto].
    - intros m fm k p; destruct (Nat.eqb_spec m N) as [->|Hne].
      + intros [= <-] [].
      + apply W9.
    - intros m fm; destruct (Nat.eqb_spec m N) as [->|Hne].
      + intros [= <-]; apply upu_nil.
      + apply W10.
  Qed.

  (** ** Installing and uninstalling a fiber *)
  Lemma wf_install (γ : State) n f (l : Life) w :
    WF γ -> fibers γ n = Some f -> is_installed (life f) = false ->
    is_installed l = true -> view_of l = w -> acc_of l = [] ->
    map fst w = fdeps f ->
    (forall k p, In (k, p) w ->
       exists b, binds γ k = Some b /\ pid b = p /\ owner b <> n) ->
    WF (set_life Σ γ n f l).
  Proof.
    intros W Hn Hni Hli Hlv Hla Hkeys Hview.
    pose proof W as W'; destruct W' as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
    assert (Hpar : forall m fm q, fibers γ m = Some fm -> parent fm = Some q -> q <> n).
    { intros m fm q Hm Hp ->; destruct (W4 m fm n Hm Hp) as (fq & Hq & Hiq & _).
      rewrite Hn in Hq; injection Hq as <-; congruence. }
    split; cbn [next binds].
    - intros m fm H; apply fibers_set_life_inv in H as [[-> _]|[_ H]]; eauto.
    - exact W2.
    - intros m fm m' H Hin; apply fibers_set_life_inv in H as [[-> ->]|[_ H]].
      + cbn in Hin; rewrite Hla in Hin; destruct Hin.
      + eauto.
    - intros m fm q H Hp.
      assert (H0 : exists fm0, fibers γ m = Some fm0 /\ parent fm0 = Some q).
      { apply fibers_set_life_inv in H as [[-> ->]|[_ H]]; eauto. }
      destruct H0 as (fm0 & H0 & Hp0).
      pose proof (Hpar m fm0 q H0 Hp0) as Hqn.
      destruct (W4 m fm0 q H0 Hp0) as (fq & Hq & Hiq & Hsq).
      exists fq; rewrite fibers_set_life; destruct (Nat.eqb_spec q n); [contradiction | auto].
    - intros m1 m2 f1 f2 Hne H1 H2.
      assert (L : forall m fm, fibers (set_life Σ γ n f l) m = Some fm ->
                  exists fm0, fibers γ m = Some fm0 /\ fprovs fm = fprovs fm0).
      { intros m fm H; apply fibers_set_life_inv in H as [[-> ->]|[_ H]]; eauto. }
      destruct (L _ _ H1) as (g1 & G1 & E1), (L _ _ H2) as (g2 & G2 & E2).
      rewrite E1, E2; exact (W5 m1 m2 g1 g2 Hne G1 G2).
    - intros m fm k p H Hin; apply fibers_set_life_inv in H as [[-> ->]|[_ H]].
      + cbn in Hin; rewrite Hlv in Hin; exact (Hview k p Hin).
      + exact (W6 m fm k p H Hin).
    - intros m fm H Hi; apply fibers_set_life_inv in H as [[-> ->]|[_ H]].
      + cbn; rewrite Hlv; exact Hkeys.
      + eauto.
    - intros k b Hb; destruct (W8 k b Hb) as (fo & Ho & Hio & Hko & Huo).
      exists fo; rewrite fibers_set_life; destruct (Nat.eqb_spec (owner b) n) as [Heq|_].
      + rewrite Heq, Hn in Ho; injection Ho as <-; congruence.
      + auto.
    - intros m fm k p H Hin; apply fibers_set_life_inv in H as [[-> ->]|[_ H]].
      + cbn in Hin; rewrite Hla in Hin; destruct Hin.
      + exact (W9 m fm k p H Hin).
    - intros m fm H; apply fibers_set_life_inv in H as [[-> ->]|[_ H]].
      + cbn; rewrite Hla; apply upu_nil.
      + eauto.
  Qed.

  Lemma wf_uninstall (γ : State) n f (l : Life) :
    WF γ -> fibers γ n = Some f -> acc_of (life f) = [] ->
    is_installed l = false -> view_of l = [] -> acc_of l = [] ->
    WF (set_life Σ γ n f l).
  Proof.
    intros W Hn Hfa Hli Hlv Hla.
    pose proof W as W'; destruct W' as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
    split; cbn [next binds].
    - intros m fm H; apply fibers_set_life_inv in H as [[-> _]|[_ H]]; eauto.
    - exact W2.
    - intros m fm m' H Hin; apply fibers_set_life_inv in H as [[-> ->]|[_ H]].
      + cbn in Hin; rewrite Hla in Hin; destruct Hin.
      + eauto.
    - intros m fm q H Hp.
      assert (H0 : exists fm0, fibers γ m = Some fm0 /\ parent fm0 = Some q).
      { apply fibers_set_life_inv in H as [[-> ->]|[_ H]]; eauto. }
      destruct H0 as (fm0 & H0 & Hp0).
      destruct (W4 m fm0 q H0 Hp0) as (fq & Hq & Hiq & Hsq).
      exists fq; rewrite fibers_set_life; destruct (Nat.eqb_spec q n) as [->|_]; [|auto].
      rewrite Hn in Hq; injection Hq as <-; rewrite Hfa in Hsq; destruct Hsq.
    - intros m1 m2 f1 f2 Hne H1 H2.
      assert (L : forall m fm, fibers (set_life Σ γ n f l) m = Some fm ->
                  exists fm0, fibers γ m = Some fm0 /\ fprovs fm = fprovs fm0).
      { intros m fm H; apply fibers_set_life_inv in H as [[-> ->]|[_ H]]; eauto. }
      destruct (L _ _ H1) as (g1 & G1 & E1), (L _ _ H2) as (g2 & G2 & E2).
      rewrite E1, E2; exact (W5 m1 m2 g1 g2 Hne G1 G2).
    - intros m fm k p H Hin; apply fibers_set_life_inv in H as [[-> ->]|[_ H]].
      + cbn in Hin; rewrite Hlv in Hin; destruct Hin.
      + exact (W6 m fm k p H Hin).
    - intros m fm H Hi; apply fibers_set_life_inv in H as [[-> ->]|[_ H]].
      + cbn in Hi; congruence.
      + eauto.
    - intros k b Hb; destruct (W8 k b Hb) as (fo & Ho & Hio & Hko & Huo).
      exists fo; rewrite fibers_set_life; destruct (Nat.eqb_spec (owner b) n) as [Heq|_].
      + rewrite Heq, Hn in Ho; injection Ho as <-; rewrite Hfa in Huo; destruct Huo.
      + auto.
    - intros m fm k p H Hin; apply fibers_set_life_inv in H as [[-> ->]|[_ H]].
      + cbn in Hin; rewrite Hla in Hin; destruct Hin.
      + exact (W9 m fm k p H Hin).
    - intros m fm H; apply fibers_set_life_inv in H as [[-> ->]|[_ H]].
      + cbn; rewrite Hla; apply upu_nil.
      + eauto.
  Qed.

  (** ** Removing an Inactive fiber *)
  Lemma wf_remove (γ : State) n f :
    WF γ -> fibers γ n = Some f -> is_installed (life f) = false ->
    WF (with_fibers Σ γ (fupd Σ (fibers γ) n None)).
  Proof.
    intros W Hn Hni.
    pose proof W as W'; destruct W' as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
    split; cbn [with_fibers next binds fibers]; unfold fupd.
    - intros m fm; destruct (Nat.eqb_spec m n); [discriminate | eauto].
    - exact W2.
    - intros m fm m'; destruct (Nat.eqb_spec m n); [discriminate | eauto].
    - intros m fm q; destruct (Nat.eqb_spec m n); [discriminate|].
      intros Hm Hp; destruct (W4 m fm q Hm Hp) as (fq & Hq & Hiq & Hsq).
      exists fq; destruct (Nat.eqb_spec q n) as [->|_]; [|auto].
      rewrite Hn in Hq; injection Hq as <-; congruence.
    - intros m1 m2 f1 f2 Hne.
      destruct (Nat.eqb_spec m1 n), (Nat.eqb_spec m2 n); try discriminate; eauto.
    - intros m fm k p; destruct (Nat.eqb_spec m n); [discriminate | eauto].
    - intros m fm; destruct (Nat.eqb_spec m n); [discriminate | eauto].
    - intros k b Hb; destruct (W8 k b Hb) as (fo & Ho & Hio & Hko & Huo).
      exists fo; destruct (Nat.eqb_spec (owner b) n) as [Heq|_]; [|auto].
      rewrite Heq, Hn in Ho; injection Ho as <-; congruence.
    - intros m fm k p; destruct (Nat.eqb_spec m n); [discriminate | eauto].
    - intros m fm; destruct (Nat.eqb_spec m n); [discriminate | eauto].
  Qed.

  (** ** Providing a key *)
  Lemma wf_provide (γ : State) n f k s P0 P' acc w :
    WF γ -> fibers γ n = Some f -> life f = Loading Σ P0 acc w ->
    kmem K_eq_dec k (fprovs f) = true -> binds γ k = None ->
    WF (set_life Σ (bump Σ (log_ini Σ (with_binds Σ γ (bupd K_eq_dec Σ (binds γ) k
           (Some (mkBinding Σ (next γ) n s)))) (next γ) s)) n f
           (Loading Σ P' (UProv Σ k (next γ) :: acc) w)).
  Proof.
    intros W Hn Hl Hk Hbk.
    pose proof W as W'; destruct W' as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
    set (N := next γ) in *.
    assert (Hacc : acc_of (life f) = acc) by (rewrite Hl; reflexivity).
    assert (Hview : view_of (life f) = w) by (rewrite Hl; reflexivity).
    assert (Hfresh : forall p', ~ In (UProv Σ k p') acc).
    { intros p' Hin; rewrite <- Hacc in Hin.
      destruct (W9 n f k p' Hn Hin) as (b0 & Hb0 & _); congruence. }
    split; cbn [set_life set_fiber with_fibers with_binds bump log_op log_ini next fibers binds];
      unfold fupd, bupd, keqb.
    - intros m fm; destruct (Nat.eqb_spec m n) as [->|Hne].
      + intros _; pose proof (W1 n f Hn); lia.
      + intros H; apply W1 in H; lia.
    - intros k' b'; destruct (K_eq_dec k' k) as [->|Hne].
      + intros [= <-]; cbn; lia.
      + intros H; apply W2 in H; lia.
    - intros m fm m'; destruct (Nat.eqb_spec m n) as [->|Hne].
      + intros [= <-] Hin; cbn in Hin; destruct Hin as [Hin|Hin]; [discriminate|].
        rewrite <- Hacc in Hin; pose proof (W3 n f m' Hn Hin); lia.
      + intros H Hin; pose proof (W3 m fm m' H Hin); lia.
    - intros m fm q Hm Hp.
      assert (H0 : exists fm0, fibers γ m = Some fm0 /\ parent fm0 = Some q).
      { revert Hm; destruct (Nat.eqb_spec m n) as [->|_]; intros Hm.
        - injection Hm as <-; exists f; auto.
        - exists fm; auto. }
      destruct H0 as (fm0 & H0 & Hp0).
      destruct (W4 m fm0 q H0 Hp0) as (fq & Hq & Hiq & Hsq).
      destruct (Nat.eqb_spec q n) as [->|_].
      + rewrite Hn in Hq; injection Hq as <-.
        eexists; split; [reflexivity|]; cbn; split; [reflexivity|].
        right; rewrite <- Hacc; exact Hsq.
      + exists fq; auto.
    - intros m1 m2 f1 f2 Hne.
      assert (L : forall m fm,
                (if m =? n then Some (mkFiber Σ (fcomp f) (parent f) (disposed f)
                                       (Loading Σ P' (UProv Σ k N :: acc) w))
                 else fibers γ m) = Some fm ->
                exists fm0, fibers γ m = Some fm0 /\ fprovs fm = fprovs fm0).
      { intros m fm; destruct (Nat.eqb_spec m n) as [->|_]; intros H.
        - injection H as <-; exists f; auto.
        - exists fm; auto. }
      intros H1 H2; destruct (L _ _ H1) as (g1 & G1 & E1), (L _ _ H2) as (g2 & G2 & E2).
      rewrite E1, E2; exact (W5 m1 m2 g1 g2 Hne G1 G2).
    - intros m fm k' p Hm Hin.
      assert (H0 : exists fm0, fibers γ m = Some fm0 /\ In (k', p) (view_of (life fm0))).
      { revert Hm; destruct (Nat.eqb_spec m n) as [->|_]; intros Hm.
        - injection Hm as <-; exists f; split; [exact Hn | rewrite Hview; exact Hin].
        - exists fm; auto. }
      destruct H0 as (fm0 & H0 & Hin0).
      destruct (W6 m fm0 k' p H0 Hin0) as (b0 & Hb0 & Hp0 & Ho0).
      destruct (K_eq_dec k' k) as [->|_]; [congruence|].
      exists b0; auto.
    - intros m fm; destruct (Nat.eqb_spec m n) as [->|Hne].
      + intros [= <-] _; cbn; rewrite <- Hview.
        apply (W7 n f Hn); rewrite Hl; reflexivity.
      + apply W7.
    - intros k' b'; destruct (K_eq_dec k' k) as [->|Hne].
      + intros [= <-]; cbn; rewrite Nat.eqb_refl.
        eexists; split; [reflexivity|]; cbn.
        split; [reflexivity | split; [exact Hk | left; reflexivity]].
      + intros Hb'; destruct (W8 k' b' Hb') as (fo & Ho & Hio & Hko & Huo).
        destruct (Nat.eqb_spec (owner b') n) as [Heq|_].
        * rewrite Heq, Hn in Ho; injection Ho as <-.
          eexists; split; [reflexivity|]; cbn.
          split; [reflexivity | split; [exact Hko | right; rewrite <- Hacc; exact Huo]].
        * exists fo; auto.
    - intros m fm k' p Hm Hin.
      revert Hm; destruct (Nat.eqb_spec m n) as [->|Hne]; intros Hm.
      + injection Hm as <-; cbn in Hin; destruct Hin as [Hx|Hin].
        * injection Hx as <- <-.
          destruct (K_eq_dec k k) as [_|]; [|contradiction].
          eexists; split; [reflexivity|]; cbn; auto.
        * rewrite <- Hacc in Hin.
          destruct (W9 n f k' p Hn Hin) as (b0 & Hb0 & Hp0 & Ho0).
          destruct (K_eq_dec k' k) as [->|_]; [congruence|].
          exists b0; auto.
      + destruct (W9 m fm k' p Hm Hin) as (b0 & Hb0 & Hp0 & Ho0).
        destruct (K_eq_dec k' k) as [->|_]; [congruence|].
        exists b0; auto.
    - intros m fm; destruct (Nat.eqb_spec m n) as [->|Hne].
      + intros [= <-]; cbn; apply upu_cons_fresh; [|exact Hfresh].
        rewrite <- Hacc; exact (W10 n f Hn).
      + apply W10.
  Qed.

  (** ** Spawning a child *)
  Lemma wf_spawn (γ : State) n f c P0 P' acc w :
    WF γ -> fibers γ n = Some f -> life f = Loading Σ P0 acc w ->
    conflict K_eq_dec Σ prog γ c = false ->
    WF (set_life Σ (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ)
           (Some (mkFiber Σ c (Some n) false (Inactive Σ None)))))) n f
           (Loading Σ P' (USpawn Σ (next γ) :: acc) w)).
  Proof.
    intros W Hn Hl Hc.
    pose proof (fun m fm => conflict_false γ c m fm W Hc) as Hdis.
    pose proof W as W'; destruct W' as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
    set (N := next γ) in *.
    pose proof (W1 n f Hn) as HnN.
    assert (Hacc : acc_of (life f) = acc) by (rewrite Hl; reflexivity).
    assert (Hview : view_of (life f) = w) by (rewrite Hl; reflexivity).
    set (f' := mkFiber Σ (fcomp f) (parent f) (disposed f)
                 (Loading Σ P' (USpawn Σ N :: acc) w)).
    set (child := mkFiber Σ c (Some n) false (Inactive Σ None)).
    (* Lookups in the new state, in three cases. *)
    assert (Lk : forall m fm,
              (if m =? n then Some f' else if m =? N then Some child else fibers γ m)
                = Some fm ->
              (m = n /\ fm = f') \/ (m = N /\ fm = child) \/
              (m <> n /\ m <> N /\ fibers γ m = Some fm)).
    { intros m fm; destruct (Nat.eqb_spec m n) as [->|Hn'];
        [intros [= <-]; left; auto|].
      destruct (Nat.eqb_spec m N) as [->|HN]; [intros [= <-]; right; left; auto|].
      intros H; right; right; auto. }
    assert (Lk' : forall q fq, fibers γ q = Some fq -> q <> n ->
              (if q =? n then Some f' else if q =? N then Some child else fibers γ q)
                = Some fq).
    { intros q fq Hq Hqn; destruct (Nat.eqb_spec q n) as [->|_]; [contradiction|].
      destruct (Nat.eqb_spec q N) as [->|_]; [apply W1 in Hq; lia | exact Hq]. }
    split; cbn [set_life set_fiber with_fibers with_binds bump log_op log_ini next fibers binds];
      unfold fupd.
    - intros m fm H; apply Lk in H as [[-> _]|[[-> _]|(_ & _ & H)]]; [lia | lia|].
      apply W1 in H; lia.
    - intros k b Hb; apply W2 in Hb; lia.
    - intros m fm m' H Hin; apply Lk in H as [[-> ->]|[[-> ->]|(_ & _ & H)]].
      + cbn in Hin; destruct Hin as [Hx|Hin]; [injection Hx as <-; lia|].
        rewrite <- Hacc in Hin; pose proof (W3 n f m' Hn Hin); lia.
      + destruct Hin.
      + pose proof (W3 m fm m' H Hin); lia.
    - intros m fm q H Hp; apply Lk in H as [[-> ->]|[[-> ->]|(Hmn & HmN & H)]].
      + destruct (W4 n f q Hn Hp) as (fq & Hq & Hiq & Hsq).
        destruct (Nat.eqb_spec q n) as [->|Hqn].
        * rewrite Hn in Hq; injection Hq as <-.
          exists f'; split; [reflexivity|]; cbn.
          split; [reflexivity | right; rewrite <- Hacc; exact Hsq].
        * exists fq; split; [|auto].
          destruct (Nat.eqb_spec q N) as [->|_]; [apply W1 in Hq; lia | exact Hq].
      + injection Hp as <-.
        exists f'; rewrite Nat.eqb_refl; split; [reflexivity|]; cbn.
        split; [reflexivity | left; reflexivity].
      + destruct (W4 m fm q H Hp) as (fq & Hq & Hiq & Hsq).
        destruct (Nat.eqb_spec q n) as [->|Hqn].
        * rewrite Hn in Hq; injection Hq as <-.
          exists f'; split; [reflexivity|]; cbn.
          split; [reflexivity | right; rewrite <- Hacc; exact Hsq].
        * exists fq; split; [|auto].
          destruct (Nat.eqb_spec q N) as [->|_]; [apply W1 in Hq; lia | exact Hq].
    - intros m1 m2 f1 f2 Hne H1 H2.
      apply Lk in H1 as [[-> ->]|[[-> ->]|(Hn1 & HN1 & H1)]];
        apply Lk in H2 as [[-> ->]|[[-> ->]|(Hn2 & HN2 & H2)]];
        try contradiction.
      + rewrite overlaps_sym; exact (Hdis n f Hn).
      + exact (W5 n m2 f f2 Hne Hn H2).
      + exact (Hdis n f Hn).
      + exact (Hdis m2 f2 H2).
      + exact (W5 m1 n f1 f Hne H1 Hn).
      + rewrite overlaps_sym; exact (Hdis m1 f1 H1).
      + exact (W5 m1 m2 f1 f2 Hne H1 H2).
    - intros m fm k p H Hin; apply Lk in H as [[-> ->]|[[-> ->]|(_ & _ & H)]].
      + cbn in Hin; rewrite <- Hview in Hin; exact (W6 n f k p Hn Hin).
      + destruct Hin.
      + exact (W6 m fm k p H Hin).
    - intros m fm H Hi; apply Lk in H as [[-> ->]|[[-> ->]|(_ & _ & H)]].
      + cbn; rewrite <- Hview; apply (W7 n f Hn); rewrite Hl; reflexivity.
      + discriminate.
      + exact (W7 m fm H Hi).
    - intros k b Hb; destruct (W8 k b Hb) as (fo & Ho & Hio & Hko & Huo).
      destruct (Nat.eqb_spec (owner b) n) as [Heq|Hon].
      + rewrite Heq, Hn in Ho; injection Ho as <-.
        exists f'; split; [reflexivity|]; cbn.
        split; [reflexivity | split; [exact Hko | right; rewrite <- Hacc; exact Huo]].
      + exists fo; split; [|auto].
        destruct (Nat.eqb_spec (owner b) N) as [Heq|_]; [apply W1 in Ho; lia | exact Ho].
    - intros m fm k p H Hin; apply Lk in H as [[-> ->]|[[-> ->]|(_ & _ & H)]].
      + cbn in Hin; destruct Hin as [Hx|Hin]; [discriminate|].
        rewrite <- Hacc in Hin; exact (W9 n f k p Hn Hin).
      + destruct Hin.
      + exact (W9 m fm k p H Hin).
    - intros m fm H; apply Lk in H as [[-> ->]|[[-> ->]|(_ & _ & H)]].
      + cbn; apply upu_cons_nonprov; [intros; discriminate|].
        rewrite <- Hacc; exact (W10 n f Hn).
      + apply upu_nil.
      + exact (W10 m fm H).
  Qed.

  (** Spawning a child from any installed life, keeping the view. *)
  Lemma wf_spawn_at (γ : State) n f c (l : Life) :
    WF γ -> fibers γ n = Some f -> is_installed (life f) = true ->
    acc_of l = USpawn Σ (next γ) :: acc_of (life f) -> view_of l = view_of (life f) ->
    is_installed l = true ->
    conflict K_eq_dec Σ prog γ c = false ->
    WF (set_life Σ (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ)
           (Some (mkFiber Σ c (Some n) false (Inactive Σ None)))))) n f l).
  Proof.
    intros W Hn Hinst Hal Hvl Hil Hc.
    set (acc := acc_of (life f)) in *.
    set (w := view_of (life f)) in *.
    pose proof (fun m fm => conflict_false γ c m fm W Hc) as Hdis.
    pose proof W as W'; destruct W' as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
    set (N := next γ) in *.
    pose proof (W1 n f Hn) as HnN.
    assert (Hacc : acc_of (life f) = acc) by reflexivity.
    assert (Hview : view_of (life f) = w) by reflexivity.
    set (f' := mkFiber Σ (fcomp f) (parent f) (disposed f) l).
    set (child := mkFiber Σ c (Some n) false (Inactive Σ None)).
    (* Lookups in the new state, in three cases. *)
    assert (Lk : forall m fm,
              (if m =? n then Some f' else if m =? N then Some child else fibers γ m)
                = Some fm ->
              (m = n /\ fm = f') \/ (m = N /\ fm = child) \/
              (m <> n /\ m <> N /\ fibers γ m = Some fm)).
    { intros m fm; destruct (Nat.eqb_spec m n) as [->|Hn'];
        [intros [= <-]; left; auto|].
      destruct (Nat.eqb_spec m N) as [->|HN]; [intros [= <-]; right; left; auto|].
      intros H; right; right; auto. }
    assert (Lk' : forall q fq, fibers γ q = Some fq -> q <> n ->
              (if q =? n then Some f' else if q =? N then Some child else fibers γ q)
                = Some fq).
    { intros q fq Hq Hqn; destruct (Nat.eqb_spec q n) as [->|_]; [contradiction|].
      destruct (Nat.eqb_spec q N) as [->|_]; [apply W1 in Hq; lia | exact Hq]. }
    split; cbn [set_life set_fiber with_fibers with_binds bump log_op log_ini next fibers binds];
      unfold fupd.
    - intros m fm H; apply Lk in H as [[-> _]|[[-> _]|(_ & _ & H)]]; [lia | lia|].
      apply W1 in H; lia.
    - intros k b Hb; apply W2 in Hb; lia.
    - intros m fm m' H Hin; apply Lk in H as [[-> ->]|[[-> ->]|(_ & _ & H)]].
      + cbn in Hin; rewrite Hal in Hin; destruct Hin as [Hx|Hin]; [injection Hx as <-; lia|].
        pose proof (W3 n f m' Hn Hin); lia.
      + destruct Hin.
      + pose proof (W3 m fm m' H Hin); lia.
    - intros m fm q H Hp; apply Lk in H as [[-> ->]|[[-> ->]|(Hmn & HmN & H)]].
      + destruct (W4 n f q Hn Hp) as (fq & Hq & Hiq & Hsq).
        destruct (Nat.eqb_spec q n) as [->|Hqn].
        * rewrite Hn in Hq; injection Hq as <-.
          exists f'; split; [reflexivity|]; cbn.
          split; [exact Hil | rewrite Hal; right; exact Hsq].
        * exists fq; split; [|auto].
          destruct (Nat.eqb_spec q N) as [->|_]; [apply W1 in Hq; lia | exact Hq].
      + injection Hp as <-.
        exists f'; rewrite Nat.eqb_refl; split; [reflexivity|]; cbn.
        split; [exact Hil | rewrite Hal; left; reflexivity].
      + destruct (W4 m fm q H Hp) as (fq & Hq & Hiq & Hsq).
        destruct (Nat.eqb_spec q n) as [->|Hqn].
        * rewrite Hn in Hq; injection Hq as <-.
          exists f'; split; [reflexivity|]; cbn.
          split; [exact Hil | rewrite Hal; right; exact Hsq].
        * exists fq; split; [|auto].
          destruct (Nat.eqb_spec q N) as [->|_]; [apply W1 in Hq; lia | exact Hq].
    - intros m1 m2 f1 f2 Hne H1 H2.
      apply Lk in H1 as [[-> ->]|[[-> ->]|(Hn1 & HN1 & H1)]];
        apply Lk in H2 as [[-> ->]|[[-> ->]|(Hn2 & HN2 & H2)]];
        try contradiction.
      + rewrite overlaps_sym; exact (Hdis n f Hn).
      + exact (W5 n m2 f f2 Hne Hn H2).
      + exact (Hdis n f Hn).
      + exact (Hdis m2 f2 H2).
      + exact (W5 m1 n f1 f Hne H1 Hn).
      + rewrite overlaps_sym; exact (Hdis m1 f1 H1).
      + exact (W5 m1 m2 f1 f2 Hne H1 H2).
    - intros m fm k p H Hin; apply Lk in H as [[-> ->]|[[-> ->]|(_ & _ & H)]].
      + cbn in Hin; rewrite Hvl in Hin; exact (W6 n f k p Hn Hin).
      + destruct Hin.
      + exact (W6 m fm k p H Hin).
    - intros m fm H Hi; apply Lk in H as [[-> ->]|[[-> ->]|(_ & _ & H)]].
      + cbn; rewrite Hvl; exact (W7 n f Hn Hinst).
      + discriminate.
      + exact (W7 m fm H Hi).
    - intros k b Hb; destruct (W8 k b Hb) as (fo & Ho & Hio & Hko & Huo).
      destruct (Nat.eqb_spec (owner b) n) as [Heq|Hon].
      + rewrite Heq, Hn in Ho; injection Ho as <-.
        exists f'; split; [reflexivity|]; cbn.
        split; [exact Hil | split; [exact Hko | rewrite Hal; right; exact Huo]].
      + exists fo; split; [|auto].
        destruct (Nat.eqb_spec (owner b) N) as [Heq|_]; [apply W1 in Ho; lia | exact Ho].
    - intros m fm k p H Hin; apply Lk in H as [[-> ->]|[[-> ->]|(_ & _ & H)]].
      + cbn in Hin; rewrite Hal in Hin; destruct Hin as [Hx|Hin]; [discriminate|].
        exact (W9 n f k p Hn Hin).
      + destruct Hin.
      + exact (W9 m fm k p H Hin).
    - intros m fm H; apply Lk in H as [[-> ->]|[[-> ->]|(_ & _ & H)]].
      + cbn; rewrite Hal; apply upu_cons_nonprov; [intros; discriminate | exact (W10 n f Hn)].
      + apply upu_nil.
      + exact (W10 m fm H).
  Qed.

  Lemma view_installed (l : Life) k p : In (k, p) (view_of l) -> is_installed l = true.
  Proof. destruct l; cbn; auto; intros []. Qed.

  (** ** Withdrawing a provision *)
  Lemma wf_unprovide (γ : State) n f k p acc w z b :
    WF γ -> fibers γ n = Some f -> life f = Unloading Σ (UProv Σ k p :: acc) w z ->
    relied Σ γ n p = false -> binds γ k = Some b -> pid b = p ->
    WF (set_life Σ (with_binds Σ γ (bupd K_eq_dec Σ (binds γ) k None)) n f
           (Unloading Σ acc w z)).
  Proof.
    intros W Hn Hl Hr Hb Hpb.
    pose proof W as W'; destruct W' as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10].
    assert (Hacc : acc_of (life f) = UProv Σ k p :: acc) by (rewrite Hl; reflexivity).
    assert (Hview : view_of (life f) = w) by (rewrite Hl; reflexivity).
    assert (Hown : owner b = n).
    { assert (Hin : In (UProv Σ k p) (acc_of (life f))) by (rewrite Hacc; left; reflexivity).
      destruct (W9 n f k p Hn Hin) as (b0 & Hb0 & _ & Ho0); congruence. }
    assert (Huniq : forall p', ~ In (UProv Σ k p') acc).
    { intros p'; apply (W10 n f Hn k p [] acc); exact Hacc. }
    split; cbn [set_life set_fiber with_fibers with_binds next fibers binds];
      unfold fupd, bupd, keqb.
    - intros m fm; destruct (Nat.eqb_spec m n) as [->|_]; [intros _; eauto | apply W1].
    - intros k' b'; destruct (K_eq_dec k' k) as [->|_]; [discriminate | apply W2].
    - intros m fm m'; destruct (Nat.eqb_spec m n) as [->|_].
      + intros [= <-] Hin; apply (W3 n f m' Hn); rewrite Hacc; right; exact Hin.
      + apply W3.
    - intros m fm q Hm Hp.
      assert (H0 : exists fm0, fibers γ m = Some fm0 /\ parent fm0 = Some q).
      { revert Hm; destruct (Nat.eqb_spec m n) as [->|_]; intros Hm.
        - injection Hm as <-; exists f; auto.
        - exists fm; auto. }
      destruct H0 as (fm0 & H0 & Hp0).
      destruct (W4 m fm0 q H0 Hp0) as (fq & Hq & Hiq & Hsq).
      destruct (Nat.eqb_spec q n) as [->|_].
      + rewrite Hn in Hq; injection Hq as <-.
        eexists; split; [reflexivity|]; cbn; split; [reflexivity|].
        rewrite Hacc in Hsq; destruct Hsq as [Hx|Hsq]; [discriminate | exact Hsq].
      + exists fq; auto.
    - intros m1 m2 f1 f2 Hne.
      assert (L : forall m fm,
                (if m =? n then Some (mkFiber Σ (fcomp f) (parent f) (disposed f)
                                       (Unloading Σ acc w z))
                 else fibers γ m) = Some fm ->
                exists fm0, fibers γ m = Some fm0 /\ fprovs fm = fprovs fm0).
      { intros m fm; destruct (Nat.eqb_spec m n) as [->|_]; intros H.
        - injection H as <-; exists f; auto.
        - exists fm; auto. }
      intros H1 H2; destruct (L _ _ H1) as (g1 & G1 & E1), (L _ _ H2) as (g2 & G2 & E2).
      rewrite E1, E2; exact (W5 m1 m2 g1 g2 Hne G1 G2).
    - intros m fm k' p' Hm Hin.
      assert (H0 : exists fm0, fibers γ m = Some fm0 /\ In (k', p') (view_of (life fm0))).
      { revert Hm; destruct (Nat.eqb_spec m n) as [->|_]; intros Hm.
        - injection Hm as <-; exists f; split; [exact Hn | rewrite Hview; exact Hin].
        - exists fm; auto. }
      destruct H0 as (fm0 & H0 & Hin0).
      destruct (W6 m fm0 k' p' H0 Hin0) as (b0 & Hb0 & Hp0 & Ho0).
      destruct (K_eq_dec k' k) as [->|_]; [|exists b0; auto].
      exfalso; rewrite Hb in Hb0; injection Hb0 as <-.
      destruct (Nat.eqb_spec m n) as [->|Hmn]; [congruence|].
      apply (relied_false γ n p m fm0 k W Hr H0 Hmn).
      + exact (view_installed _ _ _ Hin0).
      + rewrite <- Hpb, Hp0; exact Hin0.
    - intros m fm; destruct (Nat.eqb_spec m n) as [->|_].
      + intros [= <-] _; cbn; rewrite <- Hview.
        apply (W7 n f Hn); rewrite Hl; reflexivity.
      + apply W7.
    - intros k' b'; destruct (K_eq_dec k' k) as [->|Hkk]; [discriminate|].
      intros Hb'; destruct (W8 k' b' Hb') as (fo & Ho & Hio & Hko & Huo).
      destruct (Nat.eqb_spec (owner b') n) as [Heq|_].
      + rewrite Heq, Hn in Ho; injection Ho as <-.
        eexists; split; [reflexivity|]; cbn.
        split; [reflexivity | split; [exact Hko|]].
        rewrite Hacc in Huo; destruct Huo as [Hx|Huo]; [injection Hx as Hx; congruence | exact Huo].
      + exists fo; auto.
    - intros m fm k' p' Hm Hin.
      revert Hm; destruct (Nat.eqb_spec m n) as [->|Hmn]; intros Hm.
      + injection Hm as <-; cbn in Hin.
        assert (Hin' : In (UProv Σ k' p') (acc_of (life f))) by (rewrite Hacc; right; exact Hin).
        destruct (W9 n f k' p' Hn Hin') as (b0 & Hb0 & Hp0 & Ho0).
        destruct (K_eq_dec k' k) as [->|_]; [exfalso; exact (Huniq p' Hin)|].
        exists b0; auto.
      + destruct (W9 m fm k' p' Hm Hin) as (b0 & Hb0 & Hp0 & Ho0).
        destruct (K_eq_dec k' k) as [->|_]; [|exists b0; auto].
        exfalso; rewrite Hb in Hb0; injection Hb0 as <-; congruence.
    - intros m fm; destruct (Nat.eqb_spec m n) as [->|_].
      + intros [= <-]; cbn; apply (upu_tail (UProv Σ k p)).
        rewrite <- Hacc; exact (W10 n f Hn).
      + apply W10.
  Qed.

  (** ** One step of a Loading fiber *)
  Lemma wf_load_step (γ : State) n f P acc w :
    WF γ -> fibers γ n = Some f -> life f = Loading Σ P acc w ->
    WF (load_step K_eq_dec Σ prog γ n f P acc w).
  Proof.
    intros W Hn Hl.
    assert (Hfail : forall γ0 z, WF γ0 -> fibers γ0 n = Some f ->
                    WF (set_life Σ γ0 n f (Unloading Σ acc w z))).
    { intros γ0 z W0 H0; apply wf_relife; auto; rewrite Hl; reflexivity. }
    destruct P as [| |k a κ|k s P'|c P']; cbn [load_step].
    - apply wf_relife; auto; rewrite Hl; reflexivity.
    - apply Hfail; auto.
    - match goal with |- WF (match ?x with _ => _ end) => destruct x as [p|] end;
        [|apply Hfail; auto].
      destruct (binds γ k) as [b|] eqn:Hb; [|apply Hfail; auto].
      destruct (Nat.eqb (pid b) p); [|apply Hfail; auto].
      destruct (run a (next γ) (bst Σ b)) as [[[s' g] o]|].
      + apply wf_relife_acc.
        * apply wf_bump, wf_log_op, wf_bind_state; auto.
        * exact Hn.
        * rewrite Hl; reflexivity.
        * rewrite Hl; reflexivity.
        * rewrite Hl; apply AccRel_push_uop.
      + apply Hfail; [apply wf_bump; auto | exact Hn].
    - destruct (kmem K_eq_dec k (provs Σ (prog (fcomp f)))) eqn:Hk; [|apply Hfail; auto].
      destruct (binds γ k) eqn:Hb; [apply Hfail; auto|].
      eapply wf_provide; eauto.
    - destruct (conflict K_eq_dec Σ prog γ c) eqn:Hc; [apply Hfail; auto|].
      eapply wf_spawn; eauto.
  Qed.

  (** ** One undo item of an Unloading fiber *)
  Lemma wf_undo (γ γ' : State) n f u acc w z :
    WF γ -> fibers γ n = Some f -> life f = Unloading Σ (u :: acc) w z ->
    undo_step K_eq_dec Σ γ n f u acc w z = Some γ' -> WF γ'.
  Proof.
    intros W Hn Hl.
    destruct u as [k p t g|k p|m]; cbn [undo_step]; intros H.
    - destruct (binds γ k) as [b|] eqn:Hb; [destruct (Nat.eqb (pid b) p)|];
        injection H as <-.
      + apply wf_relife_acc.
        * apply wf_bind_state; auto.
        * exact Hn.
        * rewrite Hl; reflexivity.
        * rewrite Hl; reflexivity.
        * rewrite Hl; apply AccRel_pop_uop.
      + apply wf_relife_acc; auto; rewrite Hl; [reflexivity | reflexivity | apply AccRel_pop_uop].
      + apply wf_relife_acc; auto; rewrite Hl; [reflexivity | reflexivity | apply AccRel_pop_uop].
    - destruct (relied Σ γ n p) eqn:Hr; [discriminate|].
      assert (Hin : In (UProv Σ k p) (acc_of (life f))) by (rewrite Hl; left; reflexivity).
      destruct (wf_uprov _ W n f k p Hn Hin) as (b0 & Hb0 & Hp0 & _).
      rewrite Hb0 in H; rewrite (proj2 (Nat.eqb_eq (pid b0) p) Hp0) in H.
      injection H as <-; eapply wf_unprovide; eauto.
    - destruct (fibers γ m) eqn:Hm; [discriminate|].
      injection H as <-.
      apply wf_relife_acc; auto; rewrite Hl; [reflexivity | reflexivity |].
      apply AccRel_pop_spawn; exact Hm.
  Qed.

  (** ** Preservation *)
  Theorem preservation (γ γ' : State) (ℓ : Label) :
    WF γ -> step γ ℓ = Some γ' -> WF γ'.
  Proof.
    intros W H; destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n n0|n].
    - eapply wf_OInsert; eauto.
    - eapply wf_ODispose; eauto.
    - eapply wf_OReset; eauto.
    - (* LBegin *)
      cbn [step] in H.
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (target Σ prog γ n) as [w|] eqn:Ht; [|discriminate].
      injection H as <-.
      pose proof (resolve_spec γ _ w (target_spec γ n f w Hn Ht)) as [Hkeys Hvis].
      apply (wf_install γ n f _ w W Hn); auto; [rewrite Hl; reflexivity|].
      intros k p Hin.
      destruct (visible_spec γ k p (Hvis k p Hin)) as (b & fo & Hb & Hp & Ho & Ha).
      exists b; split; [exact Hb | split; [exact Hp|]].
      intros Heq; rewrite Heq, Hn in Ho; injection Ho as <-.
      rewrite Hl in Ha; discriminate.
    - (* LStep *)
      cbn [step] in H.
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [|discriminate].
      injection H as <-; apply wf_load_step; auto.
    - eapply wf_LDivert; eauto.
    - eapply wf_LLeave; eauto.
    - (* LUndo *)
      cbn [step] in H.
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      eapply wf_undo; eauto.
    - eapply wf_LRetireChild; eauto.
    - (* LUnloaded *)
      cbn [step] in H.
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      injection H as <-; apply wf_uninstall; auto; rewrite Hl; reflexivity.
    - (* LRemove *)
      cbn [step] in H.
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [z| | |] eqn:Hl; try discriminate.
      destruct (disposed f && negb (has_child Σ γ n)); [|discriminate].
      injection H as <-; eapply wf_remove; eauto; rewrite Hl; reflexivity.
    - (* OReact *)
      cbn [step] in H.
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (nth_error (reacts Σ (prog (fcomp f))) n0) as [c|]; [|discriminate].
      destruct (disposed f || conflict K_eq_dec Σ prog γ c) eqn:Hdc; [discriminate|].
      apply orb_false_iff in Hdc as [_ Hc]; injection H as <-.
      apply (wf_spawn_at γ n f c); auto; rewrite Hl; reflexivity.
    - (* ORestart *)
      apply restart_shape in H as (f & acc & w & Hn & _ & [P Hl] & ->).
      apply wf_relife; auto; destruct Hl as [Hl|Hl]; rewrite Hl; reflexivity.
  Qed.

  (** Every state reached from the initial state is well formed. *)
  Corollary wf_reachable (γ : State) (ls : list Label) :
    run_labels K_eq_dec Σ prog (@init K Σ C) ls = Some γ -> WF γ.
  Proof.
    assert (G : forall γ0 ls γ, WF γ0 -> run_labels K_eq_dec Σ prog γ0 ls = Some γ -> WF γ).
    { intros γ0 ls0; revert γ0; induction ls0 as [|ℓ ls0 IH]; cbn; intros γ0 γ1 W0 H.
      - injection H as <-; exact W0.
      - destruct (step γ0 ℓ) as [γ0'|] eqn:Hs; [|discriminate].
        exact (IH γ0' γ1 (preservation γ0 γ0' ℓ W0 Hs) H). }
    intros H; exact (G _ ls γ wf_init H).
  Qed.
End Preservation.
