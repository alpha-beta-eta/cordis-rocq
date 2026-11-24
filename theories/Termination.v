(** * Progress (R3, fourth part, continued): termination

    Counterpart of the second half of the paper's Theorem 73: lifecycle
    steps alone cannot go on for ever.

    Hypotheses:
    - a rank on components, increasing along [Above] (a component that
      provides a key another declares, or may spawn it, has a lower rank),
      with ranks bounded by [R];
    - every component's program performs at most [K] steps on any path
      (the paper's len(e) ≤ K).

    The proof gives every fiber a measure μ: an upper bound on the steps it
    can still take while its target stays as it is. The measure of a state
    is the vector whose r-th entry is the sum of μ over the fibers of rank
    r. A step of a fiber [n] leaves the fibers of rank at most that of [n]
    alone, apart from [n] itself, whose μ drops; so the vector drops
    lexicographically. Fibers of higher rank may change arbitrarily. *)

From Stdlib Require Import List PeanoNat Bool Lia Wf_nat Compare_dec.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Recovery Progress.
Import ListNotations.

Section Termination.
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
  Local Notation parent := (Calculus.parent Σ).
  Local Notation disposed := (Calculus.disposed Σ).
  Local Notation view_of := (view_of Σ).
  Local Notation acc_of := (acc_of Σ).
  Local Notation is_installed := (is_installed Σ).
  Local Notation pid := (pid Σ).
  Local Notation owner := (owner Σ).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation WF := (WF K_eq_dec Σ prog).
  Local Notation Prov := (Prov Σ prog).
  Local Notation Inv2 := (Inv2 Σ prog).
  Local Notation Above := (Above Σ prog).
  Local Notation SpawnIn := (SpawnIn Σ).
  Local Notation target := (target Σ prog).
  Local Notation cbody c := (body Σ (prog c)).

  (** ** Bounded programs *)
  Inductive Bounded : nat -> Prog -> Prop :=
  | bd_done j : Bounded j PDone
  | bd_fail j : Bounded j PFail
  | bd_op j k a κ : (forall o, Bounded j (κ o)) -> Bounded (S j) (POp k a κ)
  | bd_prov j k s P : Bounded j P -> Bounded (S j) (PProvide k s P)
  | bd_spawn j c P : Bounded j P -> Bounded (S j) (PSpawn c P).

  Variable Kb : nat.
  Hypothesis HK : forall c, Bounded Kb (cbody c).

  Variable rank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', Above c c' -> rank c < rank c'.
  Hypothesis Hbnd : forall c, rank c <= Rb.

  (** ** Two more invariants *)

  (** A Loading fiber has at most [Kb] items, and what remains of its
      program fits in the rest of the budget. *)
  Definition LoadBound (γ : State) : Prop :=
    forall n f P acc w, fibers γ n = Some f -> life f = Loading Σ P acc w ->
      length acc <= Kb /\ Bounded (Kb - length acc) P.

  (** A spawn undo item names a child of the fiber holding it. *)
  Definition SpawnOwn (γ : State) : Prop :=
    forall x f m fm, fibers γ x = Some f -> In (USpawn Σ m) (acc_of (life f)) ->
      fibers γ m = Some fm -> parent fm = Some x.

  Record TInv (γ : State) : Prop := {
    t_wf : WF γ;
    t_prov : Prov γ;
    t_inv2 : Inv2 γ;
    t_lb : LoadBound γ;
    t_so : SpawnOwn γ
  }.

  Lemma tinv_init : TInv (@init K Σ C).
  Proof.
    split.
    - exact (wf_init K_eq_dec Σ prog).
    - exact (prov_init Σ prog).
    - exact (inv2_init Σ prog).
    - intros n f P acc w H; discriminate.
    - intros x f m fm H; discriminate.
  Qed.

  (** *** Preservation *)
  Lemma lb_relife (γ γ1 : State) n f (l : Life) :
    LoadBound γ ->
    (forall m fm, fibers γ1 m = Some fm ->
       fibers γ m = Some fm \/ exists z, life fm = Inactive Σ z) ->
    (forall P acc w, l = Loading Σ P acc w -> length acc <= Kb /\ Bounded (Kb - length acc) P) ->
    LoadBound (set_life Σ γ1 n f l).
  Proof.
    intros LB Hlk Hl m fm P acc w H Hfl.
    apply fibers_set_life_inv in H as [[-> ->]|[_ H]].
    - exact (Hl P acc w Hfl).
    - destruct (Hlk m fm H) as [H0|[z Hz]]; [exact (LB m fm P acc w H0 Hfl) | congruence].
  Qed.

  Lemma so_relife (γ γ1 : State) n f (l : Life) :
    SpawnOwn γ -> fibers γ n = Some f -> fibers γ1 = fibers γ ->
    (forall m, In (USpawn Σ m) (acc_of l) -> In (USpawn Σ m) (acc_of (life f))) ->
    SpawnOwn (set_life Σ γ1 n f l).
  Proof.
    intros SO Hn E Hi x fx m fm Hx Hin Hm.
    assert (L : forall z fz, fibers (set_life Σ γ1 n f l) z = Some fz ->
              exists fz0, fibers γ z = Some fz0 /\ parent fz = parent fz0 /\
                (forall m, In (USpawn Σ m) (acc_of (life fz)) ->
                           In (USpawn Σ m) (acc_of (life fz0)))).
    { intros z fz H; apply fibers_set_life_inv in H as [[-> ->]|[_ H]].
      - exists f; auto.
      - rewrite E in H; exists fz; auto. }
    destruct (L x fx Hx) as (fx0 & Hx0 & _ & Hix).
    destruct (L m fm Hm) as (fm0 & Hm0 & Hpm & _).
    rewrite Hpm; exact (SO x fx0 m fm0 Hx0 (Hix m Hin) Hm0).
  Qed.

  Lemma so_set_disposed (γ : State) n f b :
    SpawnOwn γ -> fibers γ n = Some f ->
    SpawnOwn (set_fiber Σ γ n (mkFiber Σ (fcomp f) (parent f) b (life f))).
  Proof.
    intros SO Hn x fx m fm Hx Hin Hm.
    apply fibers_set_fiber_inv in Hx as [[-> ->]|[_ Hx]];
      apply fibers_set_fiber_inv in Hm as [[-> ->]|[_ Hm]]; cbn in *.
    - exact (SO n f n f Hn Hin Hn).
    - exact (SO n f m fm Hn Hin Hm).
    - exact (SO x fx n f Hx Hin Hn).
    - exact (SO x fx m fm Hx Hin Hm).
  Qed.

  Theorem tinv_step (γ γ' : State) ℓ : TInv γ -> step γ ℓ = Some γ' -> TInv γ'.
  Proof.
    intros [W PV I2 LB SO] H.
    pose proof (preservation K_eq_dec Σ prog γ γ' ℓ W H) as W'.
    pose proof (prov_step K_eq_dec Σ prog γ γ' ℓ W PV H) as PV'.
    pose proof (inv2_step K_eq_dec Σ prog γ γ' ℓ W PV I2 H) as I2'.
    split; [exact W' | exact PV' | exact I2' | |].
    all: destruct ℓ as [c|x|x|x|x|x|x|x|x|x|x|x i|x]; cbn [step] in H.
    (* LoadBound *)
    - destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      intros m fm P acc w; cbn; unfold fupd.
      destruct (Nat.eqb_spec m (next γ)); [intros [= <-]; discriminate | apply LB].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate]; injection H as <-.
      intros m fm P acc w Hm Hl; apply fibers_set_fiber_inv in Hm as [[-> ->]|[_ Hm]];
        cbn in Hl; [exact (LB x f P acc w Hx Hl) | exact (LB m fm P acc w Hm Hl)].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]| | |]; try discriminate; injection H as <-.
      apply (lb_relife γ γ); [exact LB | intros; left; assumption | intros ? ? ? E; discriminate E].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]| | |]; try discriminate.
      destruct (target γ x); [|discriminate]; injection H as <-.
      apply (lb_relife γ γ); [exact LB | intros; left; assumption |].
      intros P acc w [= <- <- _]; cbn; split; [lia | rewrite Nat.sub_0_r; apply HK].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [|discriminate]; injection H as <-.
      destruct (LB x f P acc w Hx Hl) as [Hlen Hb].
      assert (Keep : forall γ1 (l : Life), fibers γ1 = fibers γ ->
                (forall P0 acc0 w0, l = Loading Σ P0 acc0 w0 -> False) ->
                LoadBound (set_life Σ γ1 x f l)).
      { intros γ1 l E Hl'; apply (lb_relife γ γ1); [exact LB | |].
        - intros m fm; rewrite E; left; auto.
        - intros P0 acc0 w0 E'; destruct (Hl' P0 acc0 w0 E'). }
      destruct P as [| |k a κ|k s P'|c P'].
      + apply Keep; [reflexivity | intros ? ? ? E; discriminate E].
      + apply Keep; [reflexivity | intros ? ? ? E; discriminate E].
      + rewrite (load_step_op K_eq_dec Σ prog γ x f k a κ acc w).
        destruct (op_binding K_eq_dec Σ prog γ x f k w) as [b|].
        2: { apply Keep; [reflexivity | intros ? ? ? E; discriminate E]. }
        destruct (run a (next γ) (bst Σ b)) as [[[s' g] o]|].
        2: { apply Keep; [reflexivity | intros ? ? ? E; discriminate E]. }
        apply (lb_relife γ); [exact LB | intros m fm Hm; left; exact Hm |].
        intros P0 acc0 w0 [= <- <- _]; cbn.
        inversion Hb as [| |j k0 a0 κ0 Hκ Hj| |]; subst.
        split; [lia|].
        replace (Kb - S (length acc)) with j by lia; apply Hκ.
      + cbn [load_step].
        destruct (kmem K_eq_dec k (provs Σ (prog (fcomp f)))).
        2: { apply Keep; [reflexivity | intros ? ? ? E; discriminate E]. }
        destruct (binds γ k).
        { apply Keep; [reflexivity | intros ? ? ? E; discriminate E]. }
        apply (lb_relife γ); [exact LB | intros m fm Hm; left; exact Hm |].
        intros P0 acc0 w0 [= <- <- _]; cbn.
        inversion Hb as [| | |j k0 s0 P0 HP Hj|]; subst.
        split; [lia|]; replace (Kb - S (length acc)) with j by lia; exact HP.
      + cbn [load_step].
        destruct (conflict K_eq_dec Σ prog γ c).
        { apply Keep; [reflexivity | intros ? ? ? E; discriminate E]. }
        apply (lb_relife γ); [exact LB | |].
        * intros m fm; cbn; unfold fupd.
          destruct (Nat.eqb_spec m (next γ)) as [->|_];
            [intros [= <-]; right; eexists; reflexivity | intros Hm; left; exact Hm].
        * intros P0 acc0 w0 [= <- <- _]; cbn.
          inversion Hb as [| | | |j c0 P0 HP Hj]; subst.
          split; [lia|]; replace (Kb - S (length acc)) with j by lia; exact HP.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [|P acc w| |]; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [discriminate|]; injection H as <-.
      apply (lb_relife γ γ); [exact LB | intros; left; assumption | intros ? ? ? E; discriminate E].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| |acc w|]; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [discriminate|]; injection H as <-.
      apply (lb_relife γ γ); [exact LB | intros; left; assumption | intros ? ? ? E; discriminate E].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z]; try discriminate.
      unheld H.
      destruct (undo_step_shape K_eq_dec Σ γ γ' x f u acc w z H) as (γ1 & -> & E).
      apply (lb_relife γ γ1);
        [exact LB | intros m fm; rewrite E; left; auto | intros ? ? ? E'; discriminate E'].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|[k p t g|k p|m0] acc] w z]; try discriminate.
      destruct (fibers γ m0) as [g|] eqn:Hg; [|discriminate].
      unheld H; destruct (disposed g); [discriminate|]; injection H as <-.
      intros m fm P acc' w' Hm Hl; apply fibers_set_fiber_inv in Hm as [[-> ->]|[_ Hm]];
        cbn in Hl; [exact (LB m0 g P acc' w' Hg Hl) | exact (LB m fm P acc' w' Hm Hl)].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z]; try discriminate.
      injection H as <-.
      apply (lb_relife γ γ); [exact LB | intros; left; assumption | intros ? ? ? E; discriminate E].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z| | |]; try discriminate.
      destruct (disposed f && negb (has_child Σ γ x)); [|discriminate]; injection H as <-.
      intros m fm P acc w; cbn; unfold fupd.
      destruct (Nat.eqb_spec m x); [discriminate | apply LB].
    - (* OReact *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (nth_error (reacts Σ (prog (fcomp f))) i) as [c|]; [|discriminate].
      destruct (disposed f || conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      apply (lb_relife γ); [exact LB | | intros ? ? ? E; discriminate E].
      intros m fm; cbn; unfold fupd; destruct (Nat.eqb_spec m (next γ)) as [->|_];
        [intros [= <-]; right; eexists; reflexivity | intros Hm; left; exact Hm].
    - (* ORestart *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (disposed f); [discriminate|].
      destruct (life f) as [|P acc w|acc w|]; try discriminate; injection H as <-;
      (apply (lb_relife γ γ); [exact LB | intros; left; assumption | intros ? ? ? E; discriminate E]).
    (* SpawnOwn *)
    - destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      intros y fy m fm; cbn; unfold fupd.
      destruct (Nat.eqb_spec y (next γ)) as [->|Hy]; [intros [= <-] []|].
      intros Hfy Hin.
      pose proof (wf_spawn_lt K_eq_dec Σ prog γ W y fy m Hfy Hin) as Hm.
      destruct (Nat.eqb_spec m (next γ)) as [->|_]; [lia|].
      apply (SO y fy m fm Hfy Hin).
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate]; injection H as <-.
      apply so_set_disposed; auto.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate; injection H as <-.
      apply (so_relife γ); auto; intros m [].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (target γ x); [|discriminate]; injection H as <-.
      apply (so_relife γ); auto; intros m [].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [|discriminate]; injection H as <-.
      assert (Ha : acc_of (life f) = acc) by (rewrite Hl; reflexivity).
      assert (Keep : forall γ1 (l : Life), fibers γ1 = fibers γ ->
                (forall m, In (USpawn Σ m) (acc_of l) -> In (USpawn Σ m) acc) ->
                SpawnOwn (set_life Σ γ1 x f l)).
      { intros γ1 l E Hi; apply (so_relife γ); auto; rewrite Ha; exact Hi. }
      destruct P as [| |k a κ|k s P'|c P'].
      + apply Keep; [reflexivity | auto].
      + apply Keep; [reflexivity | auto].
      + rewrite (load_step_op K_eq_dec Σ prog γ x f k a κ acc w).
        destruct (op_binding K_eq_dec Σ prog γ x f k w) as [b|]; [|apply Keep; auto].
        destruct (run a (next γ) (bst Σ b)) as [[[s' g] o]|]; [|apply Keep; auto].
        apply Keep; [reflexivity|]; intros m [E|Hm]; [discriminate | exact Hm].
      + cbn [load_step].
        destruct (kmem K_eq_dec k (provs Σ (prog (fcomp f)))); [|apply Keep; auto].
        destruct (binds γ k); [apply Keep; auto|].
        apply Keep; [reflexivity|]; intros m [E|Hm]; [discriminate | exact Hm].
      + cbn [load_step].
        destruct (conflict K_eq_dec Σ prog γ c); [apply Keep; auto|].
        pose proof (wf_names K_eq_dec Σ prog γ W x f Hx) as HxN.
        intros y fy m fm Hy Hin Hm.
        cbn in Hy, Hm; unfold fupd in Hy, Hm.
        destruct (Nat.eqb_spec y x) as [->|Hyx].
        * injection Hy as <-; cbn in Hin; destruct Hin as [Hx'|Hin].
          -- injection Hx' as Hme; subst m.
             destruct (Nat.eqb_spec (next γ) x) as [E|_]; [lia|].
             rewrite Nat.eqb_refl in Hm; injection Hm as <-; reflexivity.
          -- rewrite <- Ha in Hin.
             pose proof (wf_spawn_lt K_eq_dec Σ prog γ W x f m Hx Hin) as Hml.
             destruct (Nat.eqb_spec m x) as [->|_].
             ++ injection Hm as <-; cbn; exact (SO x f x f Hx Hin Hx).
             ++ destruct (Nat.eqb_spec m (next γ)) as [->|_]; [lia|].
                exact (SO x f m fm Hx Hin Hm).
        * destruct (Nat.eqb_spec y (next γ)) as [->|Hyn]; [injection Hy as <-; destruct Hin|].
          pose proof (wf_spawn_lt K_eq_dec Σ prog γ W y fy m Hy Hin) as Hml.
          destruct (Nat.eqb_spec m x) as [->|_].
          -- injection Hm as <-; cbn; exact (SO y fy x f Hy Hin Hx).
          -- destruct (Nat.eqb_spec m (next γ)) as [->|_]; [lia|].
             exact (SO y fy m fm Hy Hin Hm).
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [discriminate|]; injection H as <-.
      apply (so_relife γ); auto; intros m Hm; rewrite Hl; exact Hm.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [discriminate|]; injection H as <-.
      apply (so_relife γ); auto; intros m Hm; rewrite Hl; exact Hm.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      destruct (undo_step_shape K_eq_dec Σ γ γ' x f u acc w z H) as (γ1 & -> & E).
      apply (so_relife γ); auto; intros m Hm; rewrite Hl; right; exact Hm.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|[k p t g|k p|m0] acc] w z]; try discriminate.
      destruct (fibers γ m0) as [g|] eqn:Hg; [|discriminate].
      unheld H; destruct (disposed g); [discriminate|]; injection H as <-.
      apply so_set_disposed; auto.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      injection H as <-; apply (so_relife γ); auto; intros m [].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z| | |]; try discriminate.
      destruct (disposed f && negb (has_child Σ γ x)); [|discriminate]; injection H as <-.
      intros y fy m fm; cbn; unfold fupd.
      destruct (Nat.eqb_spec y x); [discriminate|].
      destruct (Nat.eqb_spec m x); [intros _ _ E; discriminate E | apply SO].
    - (* OReact *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (nth_error (reacts Σ (prog (fcomp f))) i) as [c|]; [|discriminate].
      destruct (disposed f || conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      assert (Ha : acc_of (life f) = acc) by (rewrite Hl; reflexivity).
      pose proof (wf_names K_eq_dec Σ prog γ W x f Hx) as HxN.
      intros y fy m fm Hy Hin Hm.
      cbn in Hy, Hm; unfold fupd in Hy, Hm.
      destruct (Nat.eqb_spec y x) as [->|Hyx].
      * injection Hy as <-; cbn in Hin; destruct Hin as [Hx'|Hin].
        -- injection Hx' as Hme; subst m.
           destruct (Nat.eqb_spec (next γ) x) as [E|_]; [lia|].
           rewrite Nat.eqb_refl in Hm; injection Hm as <-; reflexivity.
        -- rewrite <- Ha in Hin.
           pose proof (wf_spawn_lt K_eq_dec Σ prog γ W x f m Hx Hin) as Hml.
           destruct (Nat.eqb_spec m x) as [->|_].
           ++ injection Hm as <-; cbn; exact (SO x f x f Hx Hin Hx).
           ++ destruct (Nat.eqb_spec m (next γ)) as [->|_]; [lia|].
              exact (SO x f m fm Hx Hin Hm).
      * destruct (Nat.eqb_spec y (next γ)) as [->|Hyn]; [injection Hy as <-; destruct Hin|].
        pose proof (wf_spawn_lt K_eq_dec Σ prog γ W y fy m Hy Hin) as Hml.
        destruct (Nat.eqb_spec m x) as [->|_].
        -- injection Hm as <-; cbn; exact (SO y fy x f Hy Hin Hx).
        -- destruct (Nat.eqb_spec m (next γ)) as [->|_]; [lia|].
           exact (SO y fy m fm Hy Hin Hm).
    - (* ORestart *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (disposed f); [discriminate|].
      destruct (life f) as [|P acc w|acc w|] eqn:Hl; try discriminate; injection H as <-;
      (apply (so_relife γ); auto; intros m Hm; rewrite Hl; exact Hm).
  Qed.

  (** ** What a lifecycle step of [n] does to the rest of the state *)
  Local Notation frank f := (rank (fcomp f)).

  (** The binding at [k] is unchanged, or keeps its pid and owner, or [k] is
      a key [n] may provide. *)
  Definition BindsOK (γ γ' : State) (fn : Fiber) : Prop :=
    forall k, binds γ' k = binds γ k \/
      (exists b b', binds γ k = Some b /\ binds γ' k = Some b' /\
                    pid b' = pid b /\ owner b' = owner b) \/
      kmem K_eq_dec k (fprovs Σ prog fn) = true.

  Definition Effects (γ γ' : State) n (fn : Fiber) : Prop :=
    (forall x fx, x <> n -> fibers γ x = Some fx ->
       fibers γ' x = Some fx \/
       (fibers γ' x = Some (mkFiber Σ (fcomp fx) (parent fx) true (life fx)) /\
        In (USpawn Σ x) (acc_of (life fn)))) /\
    (forall x fx', fibers γ x = None -> fibers γ' x = Some fx' ->
       x = next γ /\ SpawnIn (fcomp fx') (cbody (fcomp fn))) /\
    (forall fn', fibers γ' n = Some fn' -> fcomp fn' = fcomp fn /\ disposed fn' = disposed fn) /\
    (fibers γ' n = None -> disposed fn = true) /\
    BindsOK γ γ' fn.

  Lemma effects_relife (γ γ1 : State) n fn (l : Life) :
    fibers γ n = Some fn -> fibers γ1 = fibers γ -> BindsOK γ γ1 fn ->
    Effects γ (set_life Σ γ1 n fn l) n fn.
  Proof.
    intros Hn E HB; split; [|split; [|split; [|split]]].
    - intros x fx Hxn Hx; left; rewrite fibers_set_life.
      destruct (Nat.eqb_spec x n); [contradiction | rewrite E; exact Hx].
    - intros x fx' Hx Hx'; rewrite fibers_set_life in Hx'.
      destruct (Nat.eqb_spec x n) as [->|_]; [congruence | rewrite E in Hx'; congruence].
    - intros fn' H; rewrite fibers_set_life, Nat.eqb_refl in H; injection H as <-; auto.
    - rewrite fibers_set_life, Nat.eqb_refl; discriminate.
    - exact HB.
  Qed.

  Lemma bok_same (γ γ1 : State) fn : (forall k, binds γ1 k = binds γ k) -> BindsOK γ γ1 fn.
  Proof. intros E k; left; apply E. Qed.

  Lemma bok_update (γ γ1 : State) fn k0 b s :
    binds γ k0 = Some b ->
    (forall k, binds γ1 k = if keqb K_eq_dec k k0
                            then Some (mkBinding Σ (pid b) (owner b) s) else binds γ k) ->
    BindsOK γ γ1 fn.
  Proof.
    intros Hb E k; rewrite E; unfold keqb.
    destruct (K_eq_dec k k0) as [->|_]; [|left; reflexivity].
    right; left; exists b, (mkBinding Σ (pid b) (owner b) s); auto.
  Qed.

  Lemma bok_own (γ γ1 : State) fn k0 o :
    kmem K_eq_dec k0 (fprovs Σ prog fn) = true ->
    (forall k, binds γ1 k = if keqb K_eq_dec k k0 then o else binds γ k) ->
    BindsOK γ γ1 fn.
  Proof.
    intros Hk E k; rewrite E; unfold keqb.
    destruct (K_eq_dec k k0) as [->|_]; [right; right; exact Hk | left; reflexivity].
  Qed.

  Lemma lstep_effects (γ γ' : State) (n : nat) (ℓ : @Label C) (fn : Fiber) :
    TInv γ -> In ℓ (lifecycle_labels n) -> step γ ℓ = Some γ' -> fibers γ n = Some fn ->
    Effects γ γ' n fn.
  Proof.
    intros [W PV I2 LB SO] Hin H Hn.
    cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [step] in H; rewrite Hn in H|]); [| | | | | | | |destruct Hin].
    - (* LBegin *)
      destruct (life fn) as [[z|]| | |]; try discriminate.
      destruct (target γ n); [|discriminate]; injection H as <-.
      apply effects_relife; auto; apply bok_same; reflexivity.
    - (* LStep *)
      destruct (life fn) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [|discriminate]; injection H as <-.
      pose proof (proj1 (pv_fib Σ prog γ PV n fn Hn) P acc w Hl) as Hsub.
      destruct P as [| |k a κ|k s P'|c P'].
      + apply effects_relife; auto; apply bok_same; reflexivity.
      + apply effects_relife; auto; apply bok_same; reflexivity.
      + rewrite (load_step_op K_eq_dec Σ prog γ n fn k a κ acc w).
        destruct (op_binding K_eq_dec Σ prog γ n fn k w) as [b|] eqn:Hob.
        2: { apply effects_relife; auto; apply bok_same; reflexivity. }
        pose proof (op_binding_spec K_eq_dec Σ prog γ n fn k w b Hob) as Hb.
        destruct (run a (next γ) (bst Σ b)) as [[[s' g] o]|].
        * apply effects_relife; auto.
          apply (bok_update γ _ fn k b s' Hb); intros; reflexivity.
        * apply effects_relife; auto; apply bok_same; reflexivity.
      + cbn [load_step].
        destruct (kmem K_eq_dec k (provs Σ (prog (fcomp fn)))) eqn:Hk.
        2: { apply effects_relife; auto; apply bok_same; reflexivity. }
        destruct (binds γ k).
        { apply effects_relife; auto; apply bok_same; reflexivity. }
        apply effects_relife; auto.
        apply (bok_own γ _ fn k (Some (mkBinding Σ (next γ) n s)) Hk); intros; reflexivity.
      + cbn [load_step].
        destruct (conflict K_eq_dec Σ prog γ c).
        { apply effects_relife; auto; apply bok_same; reflexivity. }
        pose proof (wf_names K_eq_dec Σ prog γ W n fn Hn) as HnN.
        split; [|split; [|split; [|split]]].
        * intros x fx Hxn Hx; left; rewrite fibers_set_life.
          destruct (Nat.eqb_spec x n); [contradiction|]; cbn; unfold fupd.
          destruct (Nat.eqb_spec x (next γ)) as [->|_];
            [apply (wf_names K_eq_dec Σ prog γ W) in Hx; lia | exact Hx].
        * intros x fx' Hx Hx'; rewrite fibers_set_life in Hx'.
          destruct (Nat.eqb_spec x n) as [->|_]; [congruence|]; cbn in Hx'; unfold fupd in Hx'.
          destruct (Nat.eqb_spec x (next γ)) as [->|_]; [|congruence].
          injection Hx' as <-; cbn; split; [reflexivity|].
          apply (SpawnIn_Sub Σ c (PSpawn c P')); [exact Hsub | apply spi_here].
        * intros fn' H; rewrite fibers_set_life, Nat.eqb_refl in H; injection H as <-; auto.
        * rewrite fibers_set_life, Nat.eqb_refl; discriminate.
        * apply bok_same; reflexivity.
    - (* LDivert *)
      destruct (life fn) as [|P acc w| |]; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [discriminate|]; injection H as <-.
      apply effects_relife; auto; apply bok_same; reflexivity.
    - (* LLeave *)
      destruct (life fn) as [| |acc w|]; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [discriminate|]; injection H as <-.
      apply effects_relife; auto; apply bok_same; reflexivity.
    - (* LUndo *)
      destruct (life fn) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      destruct u as [k p t g|k p|m]; cbn [undo_step] in H.
      + destruct (binds γ k) as [b|] eqn:Hb.
        * destruct (Nat.eqb (pid b) p); injection H as <-; apply effects_relife; auto.
          -- apply (bok_update γ _ fn k b (g (bst Σ b)) Hb); intros; reflexivity.
          -- apply bok_same; reflexivity.
        * injection H as <-; apply effects_relife; auto; apply bok_same; reflexivity.
      + destruct (relied Σ γ n p); [discriminate|].
        assert (Hu : In (UProv Σ k p) (acc_of (life fn))) by (rewrite Hl; left; reflexivity).
        destruct (wf_uprov K_eq_dec Σ prog γ W n fn k p Hn Hu) as (b0 & Hb0 & _ & Ho0).
        destruct (wf_bind K_eq_dec Σ prog γ W k b0 Hb0) as (fo & Ho & _ & Hko & _).
        rewrite Ho0, Hn in Ho; injection Ho as <-.
        destruct (binds γ k) as [b|] eqn:Hb.
        * destruct (Nat.eqb (pid b) p); injection H as <-; apply effects_relife; auto.
          -- apply (bok_own γ _ fn k None Hko); intros; reflexivity.
          -- apply bok_same; reflexivity.
        * injection H as <-; apply effects_relife; auto; apply bok_same; reflexivity.
      + destruct (fibers γ m); [discriminate|]; injection H as <-.
        apply effects_relife; auto; apply bok_same; reflexivity.
    - (* LRetireChild *)
      destruct (life fn) as [| | |[|[k p t g|k p|mm] acc] w z] eqn:Hl; try discriminate.
      destruct (fibers γ mm) as [g|] eqn:Hg; [|discriminate].
      unheld H; destruct (disposed g) eqn:Hd; [discriminate|]; injection H as <-.
      assert (Hin : In (USpawn Σ mm) (acc_of (life fn))) by (rewrite Hl; left; reflexivity).
      assert (Hmn : mm <> n).
      { intros ->; rewrite Hn in Hg; injection Hg as <-.
        pose proof (i2_spawn Σ prog γ I2 n fn n fn Hn Hin Hn) as HS.
        pose proof (Hrank (fcomp fn) (fcomp fn) (or_intror HS)); lia. }
      split; [|split; [|split; [|split]]].
      + intros x fx Hxn Hx; cbn; unfold fupd.
        destruct (Nat.eqb_spec x mm) as [->|_]; [|left; exact Hx].
        right; rewrite Hg in Hx; injection Hx as <-; split; [reflexivity | exact Hin].
      + intros x fx' Hx Hx'; apply fibers_set_fiber_inv in Hx' as [[-> _]|[_ Hx']]; congruence.
      + intros fn' Hn'; apply fibers_set_fiber_inv in Hn' as [[E _]|[_ Hn']]; [congruence|].
        rewrite Hn in Hn'; injection Hn' as <-; auto.
      + cbn; unfold fupd; destruct (Nat.eqb_spec n mm) as [E|_]; [congruence|].
        rewrite Hn; discriminate.
      + apply bok_same; reflexivity.
    - (* LUnloaded *)
      destruct (life fn) as [| | |[|u acc] w z]; try discriminate; injection H as <-.
      apply effects_relife; auto; apply bok_same; reflexivity.
    - (* LRemove *)
      destruct (life fn) as [z| | |]; try discriminate.
      destruct (disposed fn) eqn:Hd; [|discriminate]; cbn in H.
      destruct (negb (has_child Σ γ n)); [|discriminate]; injection H as <-.
      split; [|split; [|split; [|split]]].
      + intros x fx Hxn Hx; left; cbn; unfold fupd.
        destruct (Nat.eqb_spec x n); [contradiction | exact Hx].
      + intros x fx' Hx; cbn; unfold fupd.
        destruct (Nat.eqb_spec x n); [discriminate | congruence].
      + intros fn'; cbn; unfold fupd; rewrite Nat.eqb_refl; discriminate.
      + intros _; exact Hd.
      + apply bok_same; reflexivity.
  Qed.

  (** ** Ranks along providers and children *)
  Lemma prov_rank (fo fm : Fiber) (k : K) :
    kmem K_eq_dec k (fprovs Σ prog fo) = true -> In k (deps Σ (prog (fcomp fm))) ->
    frank fo < frank fm.
  Proof.
    intros Hk Hd; apply Hrank; left; exists k; split; [exact (kmem_In K_eq_dec k _ Hk) | exact Hd].
  Qed.

  Lemma child_rank (γ : State) (n : nat) (fn : Fiber) (x : nat) (fx : Fiber) :
    TInv γ -> fibers γ n = Some fn -> In (USpawn Σ x) (acc_of (life fn)) ->
    fibers γ x = Some fx -> frank fn < frank fx.
  Proof.
    intros I Hn Hin Hx; apply Hrank; right.
    exact (i2_spawn Σ prog γ (t_inv2 _ I) n fn x fx Hn Hin Hx).
  Qed.

  (** Fibers of rank at most that of [n], other than [n], are untouched. *)
  Lemma lower_same (γ γ' : State) (n : nat) (fn : Fiber) (x : nat) (fx : Fiber) :
    TInv γ -> Effects γ γ' n fn -> fibers γ n = Some fn ->
    x <> n -> fibers γ x = Some fx -> frank fx <= frank fn -> fibers γ' x = Some fx.
  Proof.
    intros I [E1 _] Hn Hxn Hx Hr.
    destruct (E1 x fx Hxn Hx) as [H|[_ Hin]]; [exact H|].
    pose proof (child_rank γ n fn x fx I Hn Hin Hx); lia.
  Qed.

  (** ** Targets of fibers of rank at most that of [n] do not move *)
  Lemma visible_stable (γ γ' : State) (n : nat) (fn fm : Fiber) (k : K) :
    TInv γ -> Effects γ γ' n fn -> fibers γ n = Some fn ->
    In k (deps Σ (prog (fcomp fm))) -> frank fm <= frank fn ->
    visible Σ γ' k = visible Σ γ k.
  Proof.
    intros I EF Hn Hk Hr.
    pose proof EF as (_ & _ & _ & _ & EB).
    pose proof (t_wf _ I) as W.
    assert (Owner : forall b, binds γ k = Some b ->
              fibers γ' (owner b) = fibers γ (owner b)).
    { intros b Hb.
      destruct (wf_bind K_eq_dec Σ prog γ W k b Hb) as (fo & Ho & _ & Hko & _).
      assert (Hon : owner b <> n).
      { intros Heq; rewrite Heq, Hn in Ho; injection Ho as <-.
        pose proof (prov_rank fn fm k Hko Hk); lia. }
      pose proof (prov_rank fo fm k Hko Hk).
      rewrite Ho; exact (lower_same γ γ' n fn (owner b) fo I EF Hn Hon Ho ltac:(lia)). }
    destruct (EB k) as [Eq|[(b & b' & Hb & Hb' & Hp & Ho)|Hkm]].
    - unfold visible; rewrite Eq.
      destruct (binds γ k) as [b|] eqn:Hb; [|reflexivity].
      rewrite (Owner b eq_refl); reflexivity.
    - unfold visible; rewrite Hb, Hb', Ho, Hp, (Owner b Hb); reflexivity.
    - pose proof (prov_rank fn fm k Hkm Hk); lia.
  Qed.

  Lemma resolve_stable (γ γ' : State) (ks : list K) :
    (forall k, In k ks -> visible Σ γ' k = visible Σ γ k) ->
    resolve Σ γ' ks = resolve Σ γ ks.
  Proof.
    induction ks as [|k ks IH]; intros H; cbn; [reflexivity|].
    rewrite (H k (or_introl eq_refl)), IH; [reflexivity|].
    intros k' Hk'; apply H; right; exact Hk'.
  Qed.

  Lemma target_stable (γ γ' : State) (n : nat) (fn : Fiber) (m : nat) (fm fm' : Fiber) :
    TInv γ -> Effects γ γ' n fn -> fibers γ n = Some fn ->
    fibers γ m = Some fm -> fibers γ' m = Some fm' ->
    fcomp fm' = fcomp fm -> disposed fm' = disposed fm -> frank fm <= frank fn ->
    target γ' m = target γ m.
  Proof.
    intros I EF Hn Hm Hm' Hc Hd Hr; unfold target; rewrite Hm, Hm', Hd, Hc.
    destruct (disposed fm); [reflexivity|].
    apply resolve_stable; intros k Hk; exact (visible_stable γ γ' n fn fm k I EF Hn Hk Hr).
  Qed.

  Lemma target_is_stable (γ γ' : State) m w :
    target γ' m = target γ m ->
    target_is K_eq_dec Σ prog γ' m w = target_is K_eq_dec Σ prog γ m w.
  Proof. intros E; unfold target_is; rewrite E; reflexivity. Qed.

  (** ** The measure of a fiber *)
  Definition Bm : nat := 3 * Kb + 11.

  Definition childflag (γ : State) (m : nat) : nat :=
    match fibers γ m with
    | Some fm => if disposed fm then 0 else 1
    | None => 0
    end.

  Definition wt (γ : State) (u : Undo) : nat :=
    match u with USpawn _ m => 1 + childflag γ m | _ => 1 end.

  Fixpoint Wt (γ : State) (l : list Undo) : nat :=
    match l with [] => 0 | u :: l' => wt γ u + Wt γ l' end.

  Definition dflag (f : Fiber) : nat := if disposed f then 1 else 0.

  (** What remains of an unload: the items, the final step, and then either
      a new load (when the target asks for one) or a removal. *)
  Definition muU (γ : State) (f : Fiber) (acc : list Undo) (z : option Err)
      (t : option (@View K)) : nat :=
    Wt γ acc + 1 + match z, t with None, Some _ => Bm | _, _ => dflag f end.

  Definition mu (γ : State) (n : nat) (f : Fiber) : nat :=
    match life f with
    | Inactive _ (Some _) => dflag f
    | Inactive _ None => match target γ n with Some _ => Bm | None => dflag f end
    | Loading _ _ acc w =>
        if target_is K_eq_dec Σ prog γ n w then 3 * Kb + 10 - length acc
        else muU γ f acc None (target γ n) + 1
    | Active _ acc w =>
        if target_is K_eq_dec Σ prog γ n w then 0
        else muU γ f acc None (target γ n) + 1
    | Unloading _ acc _ z => muU γ f acc z (target γ n)
    end.

  Lemma Wt_le (γ : State) l : Wt γ l <= 2 * length l.
  Proof.
    induction l as [|u l IH]; cbn; [lia|].
    assert (wt γ u <= 2) by (destruct u; cbn; unfold childflag;
      [lia | lia | destruct (fibers γ _) as [fm|]; [destruct (disposed fm)|]; lia]).
    lia.
  Qed.

  Lemma Wt_ext (γ γ' : State) l :
    (forall x, In (USpawn Σ x) l -> childflag γ' x = childflag γ x) -> Wt γ' l = Wt γ l.
  Proof.
    induction l as [|u l IH]; intros H; cbn; [reflexivity|].
    rewrite IH by (intros x Hx; apply H; right; exact Hx).
    destruct u; cbn; [reflexivity | reflexivity | rewrite (H _ (or_introl eq_refl)); reflexivity].
  Qed.

  Lemma Wt_mono (γ γ' : State) l :
    (forall x, In (USpawn Σ x) l -> childflag γ' x <= childflag γ x) -> Wt γ' l <= Wt γ l.
  Proof.
    induction l as [|u l IH]; intros H; cbn; [lia|].
    specialize (IH (fun x Hx => H x (or_intror Hx))).
    destruct u; cbn; [lia | lia | specialize (H _ (or_introl eq_refl)); lia].
  Qed.

  (** A fiber is not its own child. *)
  Lemma own_item_ne (γ : State) (n : nat) (fn : Fiber) (x : nat) :
    TInv γ -> fibers γ n = Some fn -> In (USpawn Σ x) (acc_of (life fn)) -> x <> n.
  Proof.
    intros I Hn Hin ->; pose proof (child_rank γ n fn n fn I Hn Hin Hn); lia.
  Qed.

  Lemma childflag_relife (γ γ1 : State) n f (l : Life) x :
    fibers γ1 = fibers γ -> x <> n ->
    childflag (set_life Σ γ1 n f l) x = childflag γ x.
  Proof.
    intros E Hxn; unfold childflag; rewrite fibers_set_life.
    destruct (Nat.eqb_spec x n); [contradiction | rewrite E; reflexivity].
  Qed.

  (** ** The measure of [n] drops at a step of [n] *)
  Lemma mu_drop (γ γ' : State) (n : nat) (ℓ : @Label C) (fn : Fiber) :
    TInv γ -> In ℓ (lifecycle_labels n) -> step γ ℓ = Some γ' -> fibers γ n = Some fn ->
    match fibers γ' n with Some fn' => mu γ' n fn' | None => 0 end < mu γ n fn.
  Proof.
    intros I Hin H Hn.
    pose proof (lstep_effects γ γ' n ℓ fn I Hin H Hn) as EF.
    pose proof EF as (_ & _ & E3 & _ & _).
    assert (Ht : forall fn', fibers γ' n = Some fn' -> target γ' n = target γ n).
    { intros fn' Hn'; destruct (E3 fn' Hn') as [Hc Hd].
      exact (target_stable γ γ' n fn n fn fn' I EF Hn Hn Hn' Hc Hd (le_n _)). }
    assert (Hrl : forall γ1 (l : Life), fibers (set_life Σ γ1 n fn l) n =
                    Some (mkFiber Σ (fcomp fn) (parent fn) (disposed fn) l))
      by (intros; rewrite fibers_set_life, Nat.eqb_refl; reflexivity).
    pose proof (t_lb _ I) as LB.
    cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [step] in H; rewrite Hn in H|]); [| | | | | | | |destruct Hin].
    - (* LBegin *)
      destruct (life fn) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (target γ n) as [w|] eqn:Htg; [|discriminate]; injection H as <-.
      rewrite Hrl; specialize (Ht _ (Hrl _ _)).
      unfold mu; cbn [life]; rewrite Hl, Htg.
      rewrite (proj2 (target_is_spec K_eq_dec Σ prog _ n w) Ht); cbn; unfold Bm; lia.
    - (* LStep *)
      destruct (life fn) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w) eqn:Hti; [|discriminate]; injection H as <-.
      destruct (LB n fn P acc w Hn Hl) as [Hlen _].
      assert (Hmu : mu γ n fn = 3 * Kb + 10 - length acc) by (unfold mu; rewrite Hl, Hti; reflexivity).
      rewrite Hmu.
      assert (Goal : forall γ1 (l : Life),
                target (set_life Σ γ1 n fn l) n = target γ n ->
                (match l with
                 | Active _ acc' w' => acc' = acc /\ w' = w
                 | Unloading _ acc' _ (Some _) => acc' = acc
                 | Loading _ _ acc' w' => length acc' = S (length acc) /\ w' = w
                 | _ => False
                 end) ->
                mu (set_life Σ γ1 n fn l) n (mkFiber Σ (fcomp fn) (parent fn) (disposed fn) l)
                < 3 * Kb + 10 - length acc).
      { intros γ1 l Ht' Hshape.
        unfold mu; cbn [life].
        destruct l as [z'|P' acc' w'|acc' w'|acc' w' [e|]]; try contradiction.
        - destruct Hshape as [Hla ->].
          rewrite (target_is_stable γ _ n w Ht'), Hti; lia.
        - destruct Hshape as [-> ->].
          rewrite (target_is_stable γ _ n w Ht'), Hti; lia.
        - subst acc'; unfold muU, dflag; cbn.
          pose proof (Wt_le (set_life Σ γ1 n fn (Unloading Σ acc w' (Some e))) acc).
          destruct (disposed fn); lia. }
      Ltac fin Goal Ht Hrl :=
        rewrite Hrl; apply Goal; [eapply Ht; apply Hrl | cbn; auto].
      destruct P as [| |k a κ|k s P'|c P'].
      + cbn [load_step] in Ht |- *; fin Goal Ht Hrl.
      + cbn [load_step] in Ht |- *; fin Goal Ht Hrl.
      + rewrite (load_step_op K_eq_dec Σ prog γ n fn k a κ acc w) in Ht |- *.
        destruct (op_binding K_eq_dec Σ prog γ n fn k w) as [b|]; [|fin Goal Ht Hrl].
        destruct (run a (next γ) (bst Σ b)) as [[[s' g] o]|]; fin Goal Ht Hrl.
      + cbn [load_step] in Ht |- *.
        destruct (kmem K_eq_dec k (provs Σ (prog (fcomp fn)))); [|fin Goal Ht Hrl].
        destruct (binds γ k); fin Goal Ht Hrl.
      + cbn [load_step] in Ht |- *.
        destruct (conflict K_eq_dec Σ prog γ c); fin Goal Ht Hrl.
    - (* LDivert *)
      destruct (life fn) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w) eqn:Hti; [discriminate|]; injection H as <-.
      rewrite Hrl; specialize (Ht _ (Hrl _ _)).
      unfold mu; cbn [life]; rewrite Hl, Hti, Ht.
      unfold muU; rewrite (Wt_ext γ _ acc); [unfold dflag; cbn; lia|].
      intros x Hx; apply childflag_relife; [reflexivity|].
      apply (own_item_ne γ n fn x I Hn); rewrite Hl; exact Hx.
    - (* LLeave *)
      destruct (life fn) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w) eqn:Hti; [discriminate|]; injection H as <-.
      rewrite Hrl; specialize (Ht _ (Hrl _ _)).
      unfold mu; cbn [life]; rewrite Hl, Hti, Ht.
      unfold muU; rewrite (Wt_ext γ _ acc); [unfold dflag; cbn; lia|].
      intros x Hx; apply childflag_relife; [reflexivity|].
      apply (own_item_ne γ n fn x I Hn); rewrite Hl; exact Hx.
    - (* LUndo *)
      destruct (life fn) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      destruct (undo_step_shape K_eq_dec Σ γ γ' n fn u acc w z H) as (γ1 & -> & E).
      rewrite Hrl; specialize (Ht _ (Hrl _ _)).
      unfold mu; cbn [life]; rewrite Hl, Ht.
      unfold muU; cbn [Wt].
      rewrite (Wt_ext γ _ acc); [unfold dflag; cbn; destruct u; cbn; lia|].
      intros x Hx; apply childflag_relife; [exact E|].
      apply (own_item_ne γ n fn x I Hn); rewrite Hl; right; exact Hx.
    - (* LRetireChild *)
      destruct (life fn) as [| | |[|[k p t g|k p|mm] acc] w z] eqn:Hl; try discriminate.
      destruct (fibers γ mm) as [g|] eqn:Hg; [|discriminate].
      unheld H; destruct (disposed g) eqn:Hdg; [discriminate|]; injection H as <-.
      assert (Hmn : mm <> n)
        by (apply (own_item_ne γ n fn mm I Hn); rewrite Hl; left; reflexivity).
      assert (Hn' : fibers (set_fiber Σ γ mm (mkFiber Σ (fcomp g) (parent g) true (life g))) n
                    = Some fn).
      { cbn; unfold fupd; destruct (Nat.eqb_spec n mm); [congruence | exact Hn]. }
      rewrite Hn'; specialize (Ht _ Hn').
      unfold mu; rewrite Hl, Ht.
      unfold muU; cbn [Wt wt].
      assert (Hf : childflag (set_fiber Σ γ mm (mkFiber Σ (fcomp g) (parent g) true (life g))) mm = 0)
        by (unfold childflag; cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity).
      assert (Hf0 : childflag γ mm = 1) by (unfold childflag; rewrite Hg, Hdg; reflexivity).
      assert (Hm : Wt (set_fiber Σ γ mm (mkFiber Σ (fcomp g) (parent g) true (life g))) acc
                   <= Wt γ acc).
      { apply Wt_mono; intros x _; unfold childflag; cbn; unfold fupd.
        destruct (Nat.eqb_spec x mm) as [->|_]; [rewrite Hg, Hdg; cbn; lia | apply Nat.le_refl]. }
      rewrite Hf, Hf0; lia.
    - (* LUnloaded *)
      destruct (life fn) as [| | |[|u acc] w z] eqn:Hl; try discriminate; injection H as <-.
      rewrite Hrl; specialize (Ht _ (Hrl _ _)).
      unfold mu; cbn [life]; rewrite Hl, Ht.
      unfold muU; cbn [Wt].
      destruct z as [e|]; cbn; [unfold dflag; cbn; lia|].
      destruct (target γ n); unfold dflag; cbn; lia.
    - (* LRemove *)
      destruct (life fn) as [z| | |] eqn:Hl; try discriminate.
      destruct (disposed fn) eqn:Hd; [|discriminate]; cbn in H.
      destruct (negb (has_child Σ γ n)); [|discriminate]; injection H as <-.
      cbn; unfold fupd; rewrite Nat.eqb_refl.
      unfold mu; rewrite Hl; unfold dflag; rewrite Hd.
      destruct z; [lia|].
      assert (Htn : target γ n = None) by (unfold target; rewrite Hn, Hd; reflexivity).
      rewrite Htn; lia.
  Qed.

  (** ** The measure of the other fibers of rank at most that of [n] *)
  Lemma mu_other (γ γ' : State) (n : nat) (ℓ : @Label C) (fn : Fiber) (m : nat) (fm : Fiber) :
    TInv γ -> In ℓ (lifecycle_labels n) -> step γ ℓ = Some γ' -> fibers γ n = Some fn ->
    m <> n -> fibers γ m = Some fm -> frank fm <= frank fn ->
    fibers γ' m = Some fm /\ mu γ' m fm = mu γ m fm.
  Proof.
    intros I Hin H Hn Hmn Hm Hr.
    pose proof (lstep_effects γ γ' n ℓ fn I Hin H Hn) as EF.
    pose proof (lower_same γ γ' n fn m fm I EF Hn Hmn Hm Hr) as Hm'.
    split; [exact Hm'|].
    pose proof (target_stable γ γ' n fn m fm fm I EF Hn Hm Hm' eq_refl eq_refl Hr) as Ht.
    assert (Hfl : forall x, In (USpawn Σ x) (acc_of (life fm)) -> childflag γ' x = childflag γ x).
    { intros x Hx; destruct EF as (E1 & E2 & E3 & E5 & _).
      unfold childflag.
      destruct (fibers γ x) as [fx|] eqn:Hfx.
      - destruct (Nat.eq_dec x n) as [->|Hxn].
        + rewrite Hn in Hfx; injection Hfx as <-.
          destruct (fibers γ' n) as [fn'|] eqn:Hn'.
          * destruct (E3 fn' eq_refl) as [_ ->]; reflexivity.
          * rewrite (E5 eq_refl); reflexivity.
        + destruct (E1 x fx Hxn Hfx) as [->|[_ Hinn]]; [reflexivity|].
          exfalso.
          pose proof (t_so _ I m fm x fx Hm Hx Hfx) as P1.
          pose proof (t_so _ I n fn x fx Hn Hinn Hfx) as P2.
          congruence.
      - destruct (fibers γ' x) as [fx'|] eqn:Hfx'; [|reflexivity].
        destruct (E2 x fx' Hfx Hfx') as [Hxe _].
        pose proof (wf_spawn_lt K_eq_dec Σ prog γ (t_wf _ I) m fm x Hm Hx); lia. }
    unfold mu.
    destruct (life fm) as [[e|]|P acc w|acc w|acc w z] eqn:Hl.
    - reflexivity.
    - rewrite Ht; reflexivity.
    - rewrite (target_is_stable γ γ' m w Ht), Ht; unfold muU.
      rewrite (Wt_ext γ γ' acc); [reflexivity|].
      intros x Hx; apply Hfl; exact Hx.
    - rewrite (target_is_stable γ γ' m w Ht), Ht; unfold muU.
      rewrite (Wt_ext γ γ' acc); [reflexivity|].
      intros x Hx; apply Hfl; exact Hx.
    - rewrite Ht; unfold muU.
      rewrite (Wt_ext γ γ' acc); [reflexivity|].
      intros x Hx; apply Hfl; exact Hx.
  Qed.

  (** ** The measure of a state *)
  Fixpoint sumf (g : nat -> nat) (l : list nat) : nat :=
    match l with [] => 0 | x :: l' => g x + sumf g l' end.

  Definition contrib (γ : State) (r m : nat) : nat :=
    match fibers γ m with
    | Some f => if Nat.eqb (frank f) r then mu γ m f else 0
    | None => 0
    end.

  Definition Phi (γ : State) (r : nat) : nat := sumf (contrib γ r) (names Σ γ).

  Lemma sumf_app g l1 l2 : sumf g (l1 ++ l2) = sumf g l1 + sumf g l2.
  Proof. induction l1 as [|x l1 IH]; cbn; lia. Qed.

  Lemma sumf_zero g l : (forall x, In x l -> g x = 0) -> sumf g l = 0.
  Proof.
    induction l as [|x l IH]; intros H; cbn; [reflexivity|].
    rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]; intros; apply H; right; auto.
  Qed.

  Lemma sumf_eq g g' l : (forall x, In x l -> g' x = g x) -> sumf g' l = sumf g l.
  Proof.
    induction l as [|x l IH]; intros H; cbn; [reflexivity|].
    rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]; intros; apply H; right; auto.
  Qed.

  Lemma sumf_le g g' l : (forall x, In x l -> g' x <= g x) -> sumf g' l <= sumf g l.
  Proof.
    induction l as [|x l IH]; intros H; cbn; [lia|].
    pose proof (H x (or_introl eq_refl)).
    pose proof (IH (fun y Hy => H y (or_intror Hy))); lia.
  Qed.

  Lemma sumf_lt g g' l x0 :
    (forall x, In x l -> g' x <= g x) -> In x0 l -> g' x0 < g x0 -> sumf g' l < sumf g l.
  Proof.
    induction l as [|x l IH]; intros H Hin Hlt; [destruct Hin|]; cbn.
    destruct Hin as [<-|Hin].
    - pose proof (sumf_le g g' l (fun y Hy => H y (or_intror Hy))); lia.
    - pose proof (H x (or_introl eq_refl)).
      pose proof (IH (fun y Hy => H y (or_intror Hy)) Hin Hlt); lia.
  Qed.

  Lemma Phi_ext (γ : State) r M :
    WF γ -> next γ <= M -> Phi γ r = sumf (contrib γ r) (seq 0 M).
  Proof.
    intros W HM; unfold Phi, names.
    replace M with (next γ + (M - next γ)) by lia.
    rewrite seq_app, sumf_app.
    rewrite (sumf_zero _ (seq (0 + next γ) _)); [lia|].
    intros x Hx; apply in_seq in Hx; unfold contrib.
    destruct (fibers γ x) eqn:E; [|reflexivity].
    apply (wf_names K_eq_dec Σ prog γ W) in E; lia.
  Qed.

  (** ** The lexicographic order on [0 .. R] *)
  Definition lexR (R : nat) (v' v : nat -> nat) : Prop :=
    exists r, r <= R /\ (forall i, i < r -> v' i = v i) /\ v' r < v r.

  Lemma lexR_wf R : forall v, Acc (lexR R) v.
  Proof.
    induction R as [|R IH].
    - assert (G : forall a v, v 0 = a -> Acc (lexR 0) v).
      { intros a; pattern a; apply (well_founded_ind lt_wf); clear a.
        intros a IHa v Ea; constructor; intros v' (r & Hr & _ & Hlt).
        assert (r = 0) by lia; subst r.
        apply (IHa (v' 0)); [lia | reflexivity]. }
      intros v; exact (G (v 0) v eq_refl).
    - assert (Main : forall a v, v 0 = a -> forall u, Acc (lexR R) u ->
                (forall i, v (S i) = u i) -> Acc (lexR (S R)) v).
      { intros a; pattern a; apply (well_founded_ind lt_wf); clear a.
        intros a IHa v Ea u Hu; revert v Ea; induction Hu as [u _ IHu]; intros v Ea Hvu.
        constructor; intros v' (r & Hr & Heq & Hlt).
        destruct r as [|r].
        + apply (IHa (v' 0) ltac:(lia) v' eq_refl (fun i => v' (S i)) (IH _)).
          intros; reflexivity.
        + assert (E0 : v' 0 = a) by (rewrite (Heq 0 ltac:(lia)); exact Ea).
          apply (IHu (fun i => v' (S i))); [| exact E0 | intros; reflexivity].
          exists r; split; [lia|]; split.
          * intros i Hi; rewrite <- Hvu; apply Heq; lia.
          * rewrite <- Hvu; exact Hlt. }
      intros v; exact (Main (v 0) v eq_refl (fun i => v (S i)) (IH _) (fun _ => eq_refl)).
  Qed.

  (** ** Every lifecycle step decreases the measure *)
  Theorem phi_drop (γ γ' : State) (n : nat) (ℓ : @Label C) :
    TInv γ -> In ℓ (lifecycle_labels n) -> step γ ℓ = Some γ' ->
    lexR Rb (Phi γ') (Phi γ).
  Proof.
    intros I Hin H.
    destruct (fibers γ n) as [fn|] eqn:Hn.
    2: { rewrite (step_absent K_eq_dec Σ prog γ n ℓ Hn Hin) in H; discriminate. }
    pose proof (tinv_step γ γ' ℓ I H) as I'.
    pose proof (lstep_effects γ γ' n ℓ fn I Hin H Hn) as EF.
    pose proof EF as (E1 & E2 & E3 & E5 & _).
    set (r0 := frank fn).
    assert (P1 : forall r, r <= r0 -> forall m,
              contrib γ' r m <= contrib γ r m /\
              (m <> n \/ r < r0 -> contrib γ' r m = contrib γ r m)).
    { intros r Hr m; unfold contrib.
      destruct (Nat.eq_dec m n) as [->|Hmn].
      - rewrite Hn.
        pose proof (mu_drop γ γ' n ℓ fn I Hin H Hn) as Hd.
        destruct (fibers γ' n) as [fn'|] eqn:Hn'.
        + destruct (E3 fn' eq_refl) as [Hc _]; rewrite Hc.
          destruct (Nat.eqb_spec (frank fn) r) as [Er|Er].
          * split; [lia|]; intros [Cx|Cx]; [contradiction | subst r0; lia].
          * split; [lia | intros; reflexivity].
        + destruct (Nat.eqb_spec (frank fn) r) as [Er|Er].
          * split; [lia|]; intros [Cx|Cx]; [contradiction | subst r0; lia].
          * split; [lia | intros; reflexivity].
      - destruct (fibers γ m) as [fm|] eqn:Hm.
        + destruct (Compare_dec.le_lt_dec (frank fm) r0) as [Hle|Hgt].
          * destruct (mu_other γ γ' n ℓ fn m fm I Hin H Hn Hmn Hm Hle) as [Hm' Hmu].
            rewrite Hm', Hmu; split; [lia | auto].
          * destruct (E1 m fm Hmn Hm) as [Hm'|[Hm' _]]; rewrite Hm'; cbn [Calculus.comp];
              (destruct (Nat.eqb_spec (frank fm) r); [subst r0; lia | split; [lia | auto]]).
        + destruct (fibers γ' m) as [fm'|] eqn:Hm'; [|split; [lia | auto]].
          destruct (E2 m fm' Hm Hm') as [_ HS].
          assert (frank fn < frank fm') by (apply Hrank; right; left; exact HS).
          destruct (Nat.eqb_spec (frank fm') r); [subst r0; lia | split; [lia | auto]]. }
    assert (P2 : contrib γ' r0 n < contrib γ r0 n).
    { unfold contrib; rewrite Hn; subst r0; rewrite Nat.eqb_refl.
      pose proof (mu_drop γ γ' n ℓ fn I Hin H Hn) as Hd.
      destruct (fibers γ' n) as [fn'|] eqn:Hn'; [|exact Hd].
      destruct (E3 fn' eq_refl) as [Hc _]; rewrite Hc, Nat.eqb_refl; exact Hd. }
    set (M := next γ + next γ').
    pose proof (t_wf _ I) as W; pose proof (t_wf _ I') as W'.
    exists r0; split; [apply Hbnd|]; split.
    - intros i Hi.
      rewrite (Phi_ext γ' i M W') by lia; rewrite (Phi_ext γ i M W) by lia.
      apply sumf_eq; intros m _; apply (proj2 (P1 i ltac:(lia) m)); right; exact Hi.
    - rewrite (Phi_ext γ' r0 M W') by lia; rewrite (Phi_ext γ r0 M W) by lia.
      apply (sumf_lt _ _ _ n); [intros m _; exact (proj1 (P1 r0 (le_n _) m)) | | exact P2].
      apply in_seq; pose proof (wf_names K_eq_dec Σ prog γ W n fn Hn); lia.
  Qed.

  (** ** Termination *)
  Definition LStepRel (γ' γ : State) : Prop :=
    TInv γ /\ exists n ℓ, In ℓ (lifecycle_labels n) /\ step γ ℓ = Some γ'.

  (** Lifecycle steps alone always terminate. *)
  Theorem termination (γ : State) : TInv γ -> Acc LStepRel γ.
  Proof.
    assert (G : forall v, Acc (lexR Rb) v ->
                forall γ, TInv γ -> (forall r, Phi γ r = v r) -> Acc LStepRel γ).
    { intros v Hacc; induction Hacc as [v _ IH]; intros γ0 I E.
      constructor; intros γ1 [I0 (n & ℓ & Hin & H)].
      destruct (phi_drop γ0 γ1 n ℓ I0 Hin H) as (r & Hr & Heq & Hlt).
      apply (IH (Phi γ1)); [| exact (tinv_step γ0 γ1 ℓ I0 H) | intros; reflexivity].
      exists r; split; [exact Hr|]; split.
      - intros i Hi; rewrite <- E; apply Heq; exact Hi.
      - rewrite <- E; exact Hlt. }
    intros I; exact (G (Phi γ) (lexR_wf Rb _) γ I (fun _ => eq_refl)).
  Qed.

  (** Equivalently: there is no infinite sequence of lifecycle steps. *)
  Corollary no_infinite_run (γ : State) :
    TInv γ ->
    ~ exists g : nat -> State, g 0 = γ /\
        forall i, exists n ℓ, In ℓ (lifecycle_labels n) /\ step (g i) ℓ = Some (g (S i)).
  Proof.
    intros I (g & G0 & Gs).
    assert (Inv : forall i, TInv (g i)).
    { induction i as [|i IH]; [rewrite G0; exact I|].
      destruct (Gs i) as (n & ℓ & _ & H); exact (tinv_step _ _ ℓ IH H). }
    assert (A : forall x, Acc LStepRel x -> forall i, g i = x -> False).
    { intros x Hx; induction Hx as [x _ IHx]; intros i Ei.
      refine (IHx (g (S i)) _ (S i) eq_refl).
      rewrite <- Ei; split; [exact (Inv i) | exact (Gs i)]. }
    exact (A γ (termination γ I) 0 G0).
  Qed.

  (** From the initial state, after any orchestrated execution. *)
  Corollary termination_reachable ls (γ : State) :
    run_labels K_eq_dec Σ prog (@init K Σ C) ls = Some γ -> Acc LStepRel γ.
  Proof.
    assert (G : forall γ0 ls γ, TInv γ0 ->
                run_labels K_eq_dec Σ prog γ0 ls = Some γ -> TInv γ).
    { intros γ0 ls0; revert γ0; induction ls0 as [|ℓ ls0 IH]; cbn; intros γ0 γ1 I0 H.
      - injection H as <-; exact I0.
      - destruct (step γ0 ℓ) as [γ0'|] eqn:Hs; [|discriminate].
        exact (IH γ0' γ1 (tinv_step γ0 γ0' ℓ I0 Hs) H). }
    intros H; apply termination; exact (G _ ls γ tinv_init H).
  Qed.
End Termination.
