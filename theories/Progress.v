(** * Progress (R3, fourth part): no deadlock

    Counterpart of the first half of the paper's Theorem 73.

    A state is settled when every fiber has reached where its target puts
    it: a failed fiber rests Inactive, a fiber that ought not to run rests
    Inactive, a fiber that ought to run is Active against its target, and
    no fiber is Loading or Unloading. The theorem: a state at which no
    lifecycle rule applies is settled, so a state that is not settled always
    has a lifecycle rule to take.

    The only place a fiber can wait is while Unloading: for the dependents
    of its provisions to leave (before it undoes anything), or for a child
    to be removed. Waiting cannot
    go round in a circle provided the relation "provides a key the other
    declares, or may spawn it" between components has no infinite ascending
    chain, the counterpart of the paper's assumption that ≺ is acyclic and
    registration bounded. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Recovery.
Import ListNotations.

Section Progress.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).
  Local Notation Fiber := (@Fiber K Σ C).
  Local Notation Life := (@Life K Σ C).
  Local Notation Undo := (@Undo K Σ).
  Local Notation Prog := (@Prog K Σ C).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation next := (next Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation disposed := (Calculus.disposed Σ).
  Local Notation view_of := (view_of Σ).
  Local Notation acc_of := (acc_of Σ).
  Local Notation is_installed := (is_installed Σ).
  Local Notation pid := (pid Σ).
  Local Notation owner := (owner Σ).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation WF := (WF K_eq_dec Σ prog).
  Local Notation Prov := (Prov Σ prog).
  Local Notation Sub := (Sub Σ).
  Local Notation target := (target Σ prog).
  Local Notation cbody c := (body Σ (prog c)).

  (** ** Components a program may spawn *)
  Inductive SpawnIn (c : C) : Prog -> Prop :=
  | spi_here P : SpawnIn c (PSpawn c P)
  | spi_op k a κ o : SpawnIn c (κ o) -> SpawnIn c (POp k a κ)
  | spi_prov k s P : SpawnIn c P -> SpawnIn c (PProvide k s P)
  | spi_spawn c' P : SpawnIn c P -> SpawnIn c (PSpawn c' P).

  Lemma SpawnIn_Sub c P Q : Sub P Q -> SpawnIn c P -> SpawnIn c Q.
  Proof.
    intros HS; induction HS; intros H.
    - exact H.
    - eapply spi_op; eauto.
    - apply spi_prov; auto.
    - apply spi_spawn; auto.
  Qed.

  (** ** Two more invariants *)

  (** Distinct bindings carry distinct pids. *)
  Definition PidUnique (γ : State) : Prop :=
    forall k1 k2 b1 b2, binds γ k1 = Some b1 -> binds γ k2 = Some b2 ->
                        pid b1 = pid b2 -> k1 = k2.

  (** [c] may create a child of component [c']: its program spawns [c'],
      or [c'] is one of its handlers. *)
  Definition Spawns (c c' : C) : Prop := SpawnIn c' (cbody c) \/ In c' (reacts Σ (prog c)).

  (** A child's component is one its parent may create. *)
  Definition SpawnProv (γ : State) : Prop :=
    forall x f m fm, fibers γ x = Some f -> In (USpawn Σ m) (acc_of (life f)) ->
                     fibers γ m = Some fm -> Spawns (fcomp f) (fcomp fm).

  Record Inv2 (γ : State) : Prop := {
    i2_pid : PidUnique γ;
    i2_spawn : SpawnProv γ
  }.

  Lemma inv2_init : Inv2 (@init K Σ C).
  Proof. split; cbn; intros; discriminate. Qed.

  Lemma pu_same (γ γ' : State) :
    (forall k, binds γ' k = binds γ k) -> PidUnique γ -> PidUnique γ'.
  Proof. intros E P k1 k2 b1 b2; rewrite !E; apply P. Qed.

  Lemma pu_update (γ γ' : State) k b s' :
    binds γ k = Some b ->
    (forall k', binds γ' k' =
       if keqb K_eq_dec k' k then Some (mkBinding Σ (pid b) (owner b) s') else binds γ k') ->
    PidUnique γ -> PidUnique γ'.
  Proof.
    intros Hb E P k1 k2 b1 b2; rewrite !E; unfold keqb.
    destruct (K_eq_dec k1 k) as [->|N1], (K_eq_dec k2 k) as [->|N2].
    - intros; reflexivity.
    - intros [= <-] H2 Hp; cbn in Hp; exact (P k k2 b b2 Hb H2 Hp).
    - intros H1 [= <-] Hp; cbn in Hp; exact (P k1 k b1 b H1 Hb Hp).
    - apply P.
  Qed.

  Lemma pu_create (γ γ' : State) k o s :
    WF γ -> binds γ k = None ->
    (forall k', binds γ' k' =
       if keqb K_eq_dec k' k then Some (mkBinding Σ (next γ) o s) else binds γ k') ->
    PidUnique γ -> PidUnique γ'.
  Proof.
    intros W Hb E P k1 k2 b1 b2; rewrite !E; unfold keqb.
    destruct (K_eq_dec k1 k) as [->|N1], (K_eq_dec k2 k) as [->|N2].
    - intros; reflexivity.
    - intros [= <-] H2 Hp; cbn in Hp.
      pose proof (wf_pids K_eq_dec Σ prog γ W k2 b2 H2); lia.
    - intros H1 [= <-] Hp; cbn in Hp.
      pose proof (wf_pids K_eq_dec Σ prog γ W k1 b1 H1); lia.
    - apply P.
  Qed.

  Lemma pu_remove (γ γ' : State) k :
    (forall k', binds γ' k' = if keqb K_eq_dec k' k then None else binds γ k') ->
    PidUnique γ -> PidUnique γ'.
  Proof.
    intros E P k1 k2 b1 b2; rewrite !E; unfold keqb.
    destruct (K_eq_dec k1 k), (K_eq_dec k2 k);
      try (intros H; discriminate H); try (intros _ H; discriminate H); apply P.
  Qed.

  Lemma sp_set_fiber (γ γ1 : State) x f f' :
    SpawnProv γ -> fibers γ x = Some f -> fibers γ1 = fibers γ -> fcomp f' = fcomp f ->
    (forall m, In (USpawn Σ m) (acc_of (life f')) -> In (USpawn Σ m) (acc_of (life f))) ->
    SpawnProv (set_fiber Σ γ1 x f').
  Proof.
    intros SP Hx E Hc Hi y fy m fm Hy Hin Hm.
    assert (L : forall z fz, fibers (set_fiber Σ γ1 x f') z = Some fz ->
              exists fz0, fibers γ z = Some fz0 /\ fcomp fz = fcomp fz0 /\
                (forall m, In (USpawn Σ m) (acc_of (life fz)) ->
                           In (USpawn Σ m) (acc_of (life fz0)))).
    { intros z fz H; cbn in H; unfold fupd in H; destruct (Nat.eqb_spec z x) as [->|_].
      - injection H as <-; exists f; auto.
      - rewrite E in H; exists fz; auto. }
    destruct (L y fy Hy) as (fy0 & Hy0 & Hcy & Hiy).
    destruct (L m fm Hm) as (fm0 & Hm0 & Hcm & _).
    rewrite Hcy, Hcm; exact (SP y fy0 m fm0 Hy0 (Hiy m Hin) Hm0).
  Qed.

  Lemma sp_set_life (γ γ1 : State) x f (l : Life) :
    SpawnProv γ -> fibers γ x = Some f -> fibers γ1 = fibers γ ->
    (forall m, In (USpawn Σ m) (acc_of l) -> In (USpawn Σ m) (acc_of (life f))) ->
    SpawnProv (set_life Σ γ1 x f l).
  Proof. intros SP Hx E Hi; unfold set_life; eapply sp_set_fiber; eauto. Qed.

  Lemma sp_add (γ : State) fnew :
    WF γ -> SpawnProv γ -> acc_of (life fnew) = [] ->
    SpawnProv (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ) (Some fnew)))).
  Proof.
    intros W SP Ha y fy m fm; cbn; unfold fupd.
    destruct (Nat.eqb_spec y (next γ)) as [->|Hy].
    - intros [= <-] Hin; rewrite Ha in Hin; destruct Hin.
    - intros Hfy Hin.
      pose proof (wf_spawn_lt K_eq_dec Σ prog γ W y fy m Hfy Hin) as Hm.
      destruct (Nat.eqb_spec m (next γ)) as [->|_]; [lia|].
      apply (SP y fy m fm Hfy Hin).
  Qed.

  Lemma sp_spawn (γ : State) x f c (l : Life) acc :
    WF γ -> SpawnProv γ -> fibers γ x = Some f -> acc_of (life f) = acc ->
    acc_of l = USpawn Σ (next γ) :: acc -> Spawns (fcomp f) c ->
    SpawnProv (set_life Σ (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ)
        (Some (mkFiber Σ c (Some x) false (Inactive Σ None)))))) x f l).
  Proof.
    intros W SP Hx Ha Hal Hc.
    pose proof (wf_names K_eq_dec Σ prog γ W x f Hx) as HxN.
    set (N := next γ) in *.
    assert (Old : forall z fz, z <> N ->
              fibers (set_life Σ (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) N
                 (Some (mkFiber Σ c (Some x) false (Inactive Σ None)))))) x f l) z = Some fz ->
              exists fz0, fibers γ z = Some fz0 /\ fcomp fz = fcomp fz0 /\
                (z <> x -> fz = fz0)).
    { intros z fz HzN H; cbn in H; unfold fupd in H.
      destruct (Nat.eqb_spec z x) as [->|Hzx].
      - injection H as <-; exists f; split; [exact Hx | split; [reflexivity | congruence]].
      - destruct (Nat.eqb_spec z N) as [->|_]; [contradiction|].
        exists fz; auto. }
    intros y fy m fm Hy Hin Hm.
    destruct (Nat.eqb_spec y N) as [Hye|HyN].
    - (* the new child holds nothing *)
      rewrite Hye in Hy; cbn in Hy; unfold fupd in Hy.
      destruct (Nat.eqb_spec N x) as [E|_]; [lia|].
      rewrite Nat.eqb_refl in Hy; injection Hy as <-; destruct Hin.
    - destruct (Old y fy HyN Hy) as (fy0 & Hy0 & Hcy & Ey).
      destruct (Nat.eqb_spec y x) as [->|Hyx].
      + (* the spawning fiber *)
        cbn in Hy; unfold fupd in Hy; rewrite Nat.eqb_refl in Hy; injection Hy as <-.
        cbn in Hin; rewrite Hal in Hin; destruct Hin as [Hx'|Hin].
        * injection Hx' as Hme; rewrite <- Hme in Hm.
          cbn in Hm; unfold fupd in Hm.
          destruct (Nat.eqb_spec N x) as [E|_]; [lia|].
          rewrite Nat.eqb_refl in Hm; injection Hm as <-; exact Hc.
        * rewrite <- Ha in Hin.
          pose proof (wf_spawn_lt K_eq_dec Σ prog γ W x f m Hx Hin) as HmN.
          destruct (Old m fm ltac:(lia) Hm) as (fm0 & Hm0 & Hcm & _).
          rewrite Hcm; exact (SP x f m fm0 Hx Hin Hm0).
      + rewrite (Ey Hyx) in Hin.
        pose proof (wf_spawn_lt K_eq_dec Σ prog γ W y fy0 m Hy0 Hin) as HmN.
        destruct (Old m fm ltac:(lia) Hm) as (fm0 & Hm0 & Hcm & _).
        rewrite Hcy, Hcm; exact (SP y fy0 m fm0 Hy0 Hin Hm0).
  Qed.

  Lemma sp_remove (γ : State) x :
    SpawnProv γ -> SpawnProv (with_fibers Σ γ (fupd Σ (fibers γ) x None)).
  Proof.
    intros SP y fy m fm; cbn; unfold fupd.
    destruct (Nat.eqb_spec y x); [discriminate|].
    destruct (Nat.eqb_spec m x); [intros _ _ H; discriminate H|].
    apply SP.
  Qed.

  Theorem inv2_step (γ γ' : State) ℓ :
    WF γ -> Prov γ -> Inv2 γ -> step γ ℓ = Some γ' -> Inv2 γ'.
  Proof.
    intros W PV [PU SP] H.
    assert (Same : forall γ1 x f (l : Life),
              fibers γ x = Some f -> fibers γ1 = fibers γ ->
              (forall k, binds γ1 k = binds γ k) ->
              (forall m, In (USpawn Σ m) (acc_of l) -> In (USpawn Σ m) (acc_of (life f))) ->
              Inv2 (set_life Σ γ1 x f l)).
    { intros γ1 x f l Hx Ef Eb Ei; split.
      - apply (pu_same γ); [exact Eb | exact PU].
      - eapply sp_set_life; eauto. }
    destruct ℓ as [c|x|x|x|x|x|x|x|x|x|x|x i|x]; cbn [step] in H.
    - destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      split; [apply (pu_same γ); [intros; reflexivity | exact PU]|].
      apply sp_add; auto.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate]; injection H as <-.
      split; [apply (pu_same γ); [intros; reflexivity | exact PU]|].
      eapply sp_set_fiber; eauto.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate; injection H as <-.
      apply Same; auto; intros m [].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (target γ x); [|discriminate]; injection H as <-.
      apply Same; auto; intros m [].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (may_step K_eq_dec Σ prog γ x P w); [|discriminate]; injection H as <-.
      assert (Ha : acc_of (life f) = acc) by (rewrite Hl; reflexivity).
      pose proof (proj1 (pv_fib Σ prog γ PV x f Hx) P acc w Hl) as Hsub.
      destruct P as [| |k a κ|k s P'|c P'].
      + cbn [load_step]; apply Same; auto; intros m Hm; rewrite Ha; exact Hm.
      + cbn [load_step]; apply Same; auto; intros m Hm; rewrite Ha; exact Hm.
      + rewrite (load_step_op K_eq_dec Σ prog γ x f k a κ acc w).
        destruct (op_binding K_eq_dec Σ prog γ x f k w) as [b|] eqn:Hob.
        2: { apply Same; auto; intros m Hm; rewrite Ha; exact Hm. }
        pose proof (op_binding_spec K_eq_dec Σ prog γ x f k w b Hob) as Hb.
        destruct (run a (next γ) (bst Σ b)) as [[[s' g] o]|].
        * split.
          -- apply (pu_update γ _ k b s' Hb); [intros; reflexivity | exact PU].
          -- apply sp_set_life with (γ := γ); auto.
             intros m [E|Hm]; [discriminate | rewrite Ha; exact Hm].
        * apply Same; auto; intros m Hm; rewrite Ha; exact Hm.
      + cbn [load_step].
        destruct (kmem K_eq_dec k (provs Σ (prog (fcomp f)))).
        2: { apply Same; auto; intros m Hm; rewrite Ha; exact Hm. }
        destruct (binds γ k) as [b|] eqn:Hb.
        { apply Same; auto; intros m Hm; rewrite Ha; exact Hm. }
        split.
        * apply (pu_create γ _ k x s W Hb); [intros; reflexivity | exact PU].
        * apply sp_set_life with (γ := γ); auto.
          intros m [E|Hm]; [discriminate | rewrite Ha; exact Hm].
      + cbn [load_step].
        destruct (conflict K_eq_dec Σ prog γ c).
        { apply Same; auto; intros m Hm; rewrite Ha; exact Hm. }
        split; [apply (pu_same γ); [intros; reflexivity | exact PU]|].
        eapply (sp_spawn γ x f c _ acc W SP Hx Ha); [reflexivity|].
        left; apply (SpawnIn_Sub c (PSpawn c P')); [exact Hsub | apply spi_here].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [discriminate|]; injection H as <-.
      apply Same; auto; intros m Hm; rewrite Hl; exact Hm.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [discriminate|]; injection H as <-.
      apply Same; auto; intros m Hm; rewrite Hl; exact Hm.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      assert (Ht : forall m, In (USpawn Σ m) acc -> In (USpawn Σ m) (acc_of (life f)))
        by (intros m Hm; rewrite Hl; right; exact Hm).
      destruct u as [k p t g|k p|m]; cbn [undo_step] in H.
      + destruct (binds γ k) as [b|] eqn:Hb.
        * destruct (Nat.eqb (pid b) p); injection H as <-.
          -- split.
             ++ apply (pu_update γ _ k b (g (bst Σ b)) Hb); [intros; reflexivity | exact PU].
             ++ apply sp_set_life with (γ := γ); auto.
          -- apply Same; auto.
        * injection H as <-; apply Same; auto.
      + destruct (relied Σ γ x p); [discriminate|].
        destruct (binds γ k) as [b|] eqn:Hb.
        * destruct (Nat.eqb (pid b) p); injection H as <-.
          -- split.
             ++ apply (pu_remove γ _ k); [intros; reflexivity | exact PU].
             ++ apply sp_set_life with (γ := γ); auto.
          -- apply Same; auto.
        * injection H as <-; apply Same; auto.
      + destruct (fibers γ m); [discriminate|]; injection H as <-; apply Same; auto.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|[k p t g|k p|m0] acc] w z]; try discriminate.
      destruct (fibers γ m0) as [g|] eqn:Hg; [|discriminate].
      unheld H; destruct (disposed g); [discriminate|]; injection H as <-.
      split; [apply (pu_same γ); [intros; reflexivity | exact PU]|].
      eapply sp_set_fiber; eauto.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      injection H as <-; apply Same; auto; intros m [].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z| | |]; try discriminate.
      destruct (disposed f && negb (has_child Σ γ x)); [|discriminate]; injection H as <-.
      split; [apply (pu_same γ); [intros; reflexivity | exact PU]|].
      apply sp_remove; exact SP.
    - (* OReact *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (nth_error (reacts Σ (prog (fcomp f))) i) as [c|] eqn:Hc; [|discriminate].
      destruct (disposed f || conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      split; [apply (pu_same γ); [intros; reflexivity | exact PU]|].
      eapply (sp_spawn γ x f c _ acc W SP Hx ltac:(rewrite Hl; reflexivity)); [reflexivity|].
      right; exact (nth_error_In _ _ Hc).
    - (* ORestart *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (disposed f); [discriminate|].
      destruct (life f) as [|P acc w|acc w|] eqn:Hl; try discriminate; injection H as <-;
      (apply Same; auto; intros m Hm; rewrite Hl; exact Hm).
  Qed.

  (** ** Settled states *)
  Definition settled_fiber (γ : State) n (f : Fiber) : Prop :=
    match life f with
    | Inactive _ (Some _) => disposed f = false
    | Inactive _ None => disposed f = false /\ target γ n = None
    | Active _ _ w => target γ n = Some w
    | _ => False
    end.

  Definition settled (γ : State) : Prop :=
    forall n f, fibers γ n = Some f -> settled_fiber γ n f.

  (** [c'] is above [c] when [c] provides a key [c'] declares, or [c]
      may spawn [c'] ([Spawns]: in its program, or as a handler). *)
  Definition Above (c c' : C) : Prop :=
    (exists k, In k (provs Σ (prog c)) /\ In k (deps Σ (prog c'))) \/
    Spawns c c'.

  (** No infinite ascending chain of components. *)
  Hypothesis Hwf : well_founded (fun c' c => Above c c').

  (** ** Helpers *)
  Lemma kmem_In k ks : kmem K_eq_dec k ks = true -> In k ks.
  Proof.
    unfold kmem; intros H; apply existsb_exists in H as (k' & Hin & E).
    unfold keqb in E; destruct (K_eq_dec k k') as [->|]; [exact Hin | discriminate].
  Qed.

  Lemma has_child_inactive (γ : State) m fm :
    WF γ -> fibers γ m = Some fm -> is_installed (life fm) = false ->
    has_child Σ γ m = false.
  Proof.
    intros W Hm Hi; unfold has_child.
    destruct (existsb _ _) eqn:E; [|reflexivity].
    exfalso; apply existsb_exists in E as (x & _ & Ex).
    destruct (fibers γ x) as [fx|] eqn:Hx; [|discriminate].
    destruct (Calculus.parent Σ fx) as [q|] eqn:Hp; [|discriminate].
    apply Nat.eqb_eq in Ex; subst q.
    destruct (wf_parent K_eq_dec Σ prog γ W x fx m Hx Hp) as (fq & Hq & Hiq & _).
    rewrite Hm in Hq; injection Hq as <-; congruence.
  Qed.

  Lemma resolve_none (γ : State) k ks :
    In k ks -> visible Σ γ k = None -> resolve Σ γ ks = None.
  Proof.
    intros Hin Hv; induction ks as [|k0 ks IH]; [destruct Hin|]; cbn.
    destruct Hin as [<-|Hin].
    - rewrite Hv; reflexivity.
    - rewrite (IH Hin); destruct (visible Σ γ k0); reflexivity.
  Qed.

  Lemma target_none (γ : State) m fm k :
    fibers γ m = Some fm -> In k (deps Σ (prog (fcomp fm))) -> visible Σ γ k = None ->
    target γ m = None.
  Proof.
    intros Hm Hin Hv; unfold target; rewrite Hm.
    destruct (disposed fm); [reflexivity|].
    exact (resolve_none γ k _ Hin Hv).
  Qed.

  Lemma step_absent (γ : State) n ℓ :
    fibers γ n = None -> In ℓ (lifecycle_labels n) -> step γ ℓ = None.
  Proof.
    intros Hn Hin; cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [step]; rewrite Hn; reflexivity|]).
    destruct Hin.
  Qed.

  (** ** Stuck states are settled *)
  Theorem quiet_settled (γ : State) :
    WF γ -> Inv2 γ -> quiet K_eq_dec Σ prog γ -> settled γ.
  Proof.
    intros W [PU SP] Q.
    assert (QU : forall n ℓ, In ℓ (lifecycle_labels n) -> step γ ℓ = None) by exact Q.
    (* A Loading fiber can always step or divert; an Active fiber whose
       target has changed can always leave. *)
    assert (NoLoad : forall m fm P acc w, fibers γ m = Some fm ->
              life fm = Loading Σ P acc w -> False).
    { intros m fm P acc w Hm Hl.
      pose proof (QU m (LStep m) ltac:(cbn; tauto)) as E1.
      pose proof (QU m (LDivert m) ltac:(cbn; tauto)) as E2.
      cbn [step] in E1, E2; rewrite Hm, Hl in E1, E2.
      destruct P; cbn [may_step] in E1; try discriminate;
        destruct (target_is K_eq_dec Σ prog γ m w); discriminate. }
    assert (NoLeave : forall m fm acc w, fibers γ m = Some fm ->
              life fm = Active Σ acc w -> target γ m <> Some w -> False).
    { intros m fm acc w Hm Hl Ht.
      pose proof (QU m (LLeave m) ltac:(cbn; tauto)) as E.
      cbn [step] in E; rewrite Hm, Hl in E.
      destruct (target_is K_eq_dec Σ prog γ m w) eqn:Et; [|discriminate].
      apply (target_is_spec K_eq_dec Σ prog) in Et; contradiction. }
    (* No fiber is Unloading, by induction along [Above]. *)
    assert (NoU : forall c n f, fibers γ n = Some f -> fcomp f = c ->
              forall acc w z, life f <> Unloading Σ acc w z).
    { intros c; induction (Hwf c) as [c _ IH].
      intros n f Hn Hc acc w z Hl.
      destruct acc as [|u acc].
      { pose proof (QU n (LUnloaded n) ltac:(cbn; tauto)) as E.
        cbn [step] in E; rewrite Hn, Hl in E; discriminate. }
      pose proof (QU n (LUndo n) ltac:(cbn; tauto)) as E.
      cbn [step] in E; rewrite Hn, Hl in E.
      (* The fiber blocking [n] is installed, above [n], and cannot be
         Loading or Active, hence Unloading: contradiction by induction. *)
      assert (Blocked : forall m fm, fibers γ m = Some fm -> Above c (fcomp fm) ->
                target γ m = None -> is_installed (life fm) = true -> False).
      { intros m fm Hm HA Ht Hi.
        destruct (life fm) as [z'|P acc' w'|acc' w'|acc' w' z'] eqn:Hlm.
        - discriminate.
        - exact (NoLoad m fm P acc' w' Hm Hlm).
        - apply (NoLeave m fm acc' w' Hm Hlm); rewrite Ht; discriminate.
        - exact (IH (fcomp fm) HA m fm Hm eq_refl acc' w' z' Hlm). }
      (* No provision still pending in [n]'s accumulator is relied on: the
         fiber resolving it would be blocking [n]. *)
      assert (NoRelied : forall k p, In (UProv Σ k p) (u :: acc) ->
                relied Σ γ n p = true -> False).
      { intros k p Hu0 Hr.
        unfold relied in Hr; apply existsb_exists in Hr as (m & _ & Hm).
        apply andb_true_iff in Hm as [Hmn Hres].
        apply negb_true_iff, Nat.eqb_neq in Hmn.
        unfold resolves in Hres.
        destruct (fibers γ m) as [fm|] eqn:Hfm; [|discriminate].
        apply andb_true_iff in Hres as [Hinst Hex].
        apply existsb_exists in Hex as ([k' p'] & Hin' & Hp'); cbn in Hp'.
        apply Nat.eqb_eq in Hp'; subst p'.
        assert (Hu : In (UProv Σ k p) (acc_of (life f))) by (rewrite Hl; exact Hu0).
        destruct (wf_uprov K_eq_dec Σ prog γ W n f k p Hn Hu) as (b0 & Hb0 & Hpb0 & Hob0).
        destruct (wf_view K_eq_dec Σ prog γ W m fm k' p Hfm Hin') as (b1 & Hb1 & Hpb1 & _).
        assert (Hkk : k' = k) by (apply (PU k' k b1 b0 Hb1 Hb0); congruence).
        subst k'.
        assert (Hkd : In k (deps Σ (prog (fcomp fm)))).
        { pose proof (wf_view_keys K_eq_dec Σ prog γ W m fm Hfm Hinst) as Hk.
          unfold fdeps in Hk; rewrite <- Hk; apply in_map_iff; exists (k, p); auto. }
        apply (Blocked m fm Hfm); [| |exact Hinst].
        + left; exists k; split; [|exact Hkd].
          destruct (wf_bind K_eq_dec Σ prog γ W k b0 Hb0) as (fo & Ho & _ & Hko & _).
          rewrite Hob0, Hn in Ho; injection Ho as <-.
          rewrite <- Hc; apply kmem_In; exact Hko.
        + apply (target_none γ m fm k Hfm Hkd).
          unfold visible; rewrite Hb0, Hob0, Hn, Hl; reflexivity. }
      assert (Hh : held Σ γ n (u :: acc) = false).
      { destruct (held Σ γ n (u :: acc)) eqn:Hh; [|reflexivity].
        exfalso; unfold held in Hh; apply existsb_exists in Hh as (u' & Hin & Hu').
        destruct u' as [k p t g|k p|m]; try discriminate.
        exact (NoRelied k p Hin Hu'). }
      rewrite Hh in E.
      destruct u as [k p t g|k p|m]; cbn [undo_step] in E.
      - destruct (binds γ k) as [b|]; [destruct (Nat.eqb (pid b) p)|]; discriminate.
      - destruct (relied Σ γ n p) eqn:Hr.
        + exact (NoRelied k p (or_introl eq_refl) Hr).
        + destruct (binds γ k) as [b|]; [destruct (Nat.eqb (pid b) p)|]; discriminate.
      - destruct (fibers γ m) as [fm|] eqn:Hfm; [|discriminate].
        pose proof (QU n (LRetireChild n) ltac:(cbn; tauto)) as E4.
        cbn [step] in E4; rewrite Hn, Hl, Hfm, Hh in E4; cbn [orb] in E4.
        destruct (disposed fm) eqn:Hd; [|discriminate].
        assert (HA : Above c (fcomp fm)).
        { right; rewrite <- Hc.
          apply (SP n f m fm Hn); [rewrite Hl; left; reflexivity | exact Hfm]. }
        destruct (is_installed (life fm)) eqn:Hi.
        + apply (Blocked m fm Hfm HA); [|exact Hi].
          unfold target; rewrite Hfm, Hd; reflexivity.
        + destruct (life fm) as [z'| | |] eqn:Hlm; try discriminate.
          pose proof (QU m (LRemove m) ltac:(cbn; tauto)) as E5.
          cbn [step] in E5; rewrite Hfm, Hlm, Hd in E5.
          rewrite (has_child_inactive γ m fm W Hfm) in E5 by (rewrite Hlm; reflexivity).
          discriminate. }
    intros n f Hn; unfold settled_fiber.
    destruct (life f) as [[e|]|P acc w|acc w|acc w z] eqn:Hl.
    - destruct (disposed f) eqn:Hd; [|reflexivity].
      pose proof (QU n (LRemove n) ltac:(cbn; tauto)) as E.
      cbn [step] in E; rewrite Hn, Hl, Hd in E.
      rewrite (has_child_inactive γ n f W Hn) in E by (rewrite Hl; reflexivity).
      discriminate.
    - assert (Hd : disposed f = false).
      { destruct (disposed f) eqn:Hd; [|reflexivity].
        pose proof (QU n (LRemove n) ltac:(cbn; tauto)) as E.
        cbn [step] in E; rewrite Hn, Hl, Hd in E.
        rewrite (has_child_inactive γ n f W Hn) in E by (rewrite Hl; reflexivity).
        discriminate. }
      split; [exact Hd|].
      destruct (target γ n) as [w|] eqn:Ht; [|reflexivity].
      pose proof (QU n (LBegin n) ltac:(cbn; tauto)) as E.
      cbn [step] in E; rewrite Hn, Hl, Ht in E; discriminate.
    - exact (NoLoad n f P acc w Hn Hl).
    - destruct (target γ n) as [w'|] eqn:Ht.
      + destruct (view_eq_dec K_eq_dec w w') as [->|Hne]; [reflexivity|].
        exfalso; apply (NoLeave n f acc w Hn Hl); rewrite Ht; congruence.
      + exfalso; apply (NoLeave n f acc w Hn Hl); rewrite Ht; discriminate.
    - exact (NoU (fcomp f) n f Hn eq_refl acc w z Hl).
  Qed.

  (** ** Progress *)
  Definition enabled (γ : State) : bool :=
    existsb (fun n => existsb (fun ℓ => match step γ ℓ with Some _ => true | None => false end)
                              (lifecycle_labels n)) (names Σ γ).

  (** A state is settled, or some lifecycle rule applies. *)
  Theorem progress (γ : State) :
    WF γ -> Inv2 γ ->
    settled γ \/ exists n ℓ γ', In ℓ (lifecycle_labels n) /\ step γ ℓ = Some γ'.
  Proof.
    intros W I.
    destruct (enabled γ) eqn:E.
    - right; apply existsb_exists in E as (n & _ & E).
      apply existsb_exists in E as (ℓ & Hin & E).
      destruct (step γ ℓ) as [γ'|] eqn:Hs; [|discriminate].
      exists n, ℓ, γ'; auto.
    - left; apply quiet_settled; auto.
      intros n ℓ Hin.
      destruct (fibers γ n) as [f|] eqn:Hn; [|exact (step_absent γ n ℓ Hn Hin)].
      destruct (step γ ℓ) as [γ'|] eqn:Hs; [|reflexivity].
      exfalso; apply (proj2 (not_true_iff_false _) E), existsb_exists.
      exists n; split; [exact (in_names K_eq_dec Σ prog γ n f W Hn)|].
      apply existsb_exists; exists ℓ; split; [exact Hin | rewrite Hs; reflexivity].
  Qed.

  (** Every reachable state is settled or can take a lifecycle step. *)
  Corollary progress_reachable ls (γ : State) :
    run_labels K_eq_dec Σ prog (@init K Σ C) ls = Some γ ->
    settled γ \/ exists n ℓ γ', In ℓ (lifecycle_labels n) /\ step γ ℓ = Some γ'.
  Proof.
    assert (G : forall γ0 ls γ, WF γ0 -> Prov γ0 -> Inv2 γ0 ->
                run_labels K_eq_dec Σ prog γ0 ls = Some γ -> WF γ /\ Inv2 γ).
    { intros γ0 ls0; revert γ0; induction ls0 as [|ℓ ls0 IH]; cbn; intros γ0 γ1 W0 P0 I0 H.
      - injection H as <-; auto.
      - destruct (step γ0 ℓ) as [γ0'|] eqn:Hs; [|discriminate].
        exact (IH γ0' γ1 (preservation K_eq_dec Σ prog γ0 γ0' ℓ W0 Hs)
                  (prov_step K_eq_dec Σ prog γ0 γ0' ℓ W0 P0 Hs)
                  (inv2_step γ0 γ0' ℓ W0 P0 I0 Hs) H). }
    intros H.
    destruct (G _ ls γ (wf_init K_eq_dec Σ prog) (prov_init Σ prog) inv2_init H) as [W I].
    apply progress; auto.
  Qed.
End Progress.
