(** * Confluence (R3, fifth part): the control state

    Counterpart of the paper's Theorem 80, first layer: for components that
    spawn nothing, the control state a system settles at does not depend on
    the schedule. From a common state, any two executions of lifecycle steps
    that end quiet, with no fiber failed, leave the same fibers present, the
    same of them Active, and every key provided by the same fiber.

    The proof does not reorder executions. It shows that at every such
    final state the set of Active fibers solves one fixpoint equation (a
    fiber is Active iff each key it declares is provided by an Active
    fiber), over a domain fixed by the start state, and that the equation
    has one solution, by induction on the rank.

    Hypotheses, besides those of Termination.v:
    - no component's program spawns;
    - totality (the paper's Definition 76): every path of a program that
      reaches [Done] provides every key the component may provide. *)

From Stdlib Require Import List PeanoNat Bool Lia Wf_nat.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Recovery
  Progress Termination.
Import ListNotations.

Section Confluence.
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
  Local Notation is_active := (is_active Σ).
  Local Notation pid := (pid Σ).
  Local Notation owner := (owner Σ).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation WF := (WF K_eq_dec Σ prog).
  Local Notation Prov := (Prov Σ prog).
  Local Notation Above := (Above Σ prog).
  Local Notation SpawnIn := (SpawnIn Σ).
  Local Notation target := (target Σ prog).
  Local Notation cbody c := (body Σ (prog c)).
  Local Notation cdeps c := (deps Σ (prog c)).
  Local Notation cprovs c := (provs Σ (prog c)).

  (** ** Hypotheses *)
  Variable Kb : nat.
  Hypothesis HK : forall c, Bounded Σ Kb (cbody c).
  Variable rank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', Above c c' -> rank c < rank c'.
  Hypothesis Hbnd : forall c, rank c <= Rb.

  Local Notation TInv := (TInv K_eq_dec Σ prog Kb).

  Hypothesis NoSpawn : forall c c', ~ SpawnIn c' (cbody c).

  (** [AllDoneProv k P]: every path of [P] that reaches [Done] provides [k]. *)
  Inductive AllDoneProv (k : K) : Prog -> Prop :=
  | adp_fail : AllDoneProv k PFail
  | adp_op k' a κ : (forall o, AllDoneProv k (κ o)) -> AllDoneProv k (POp k' a κ)
  | adp_here s P : AllDoneProv k (PProvide k s P)
  | adp_prov k' s P : AllDoneProv k P -> AllDoneProv k (PProvide k' s P)
  | adp_spawn c P : AllDoneProv k P -> AllDoneProv k (PSpawn c P).

  Hypothesis Total : forall c k, In k (cprovs c) -> AllDoneProv k (cbody c).

  Lemma Hwf : well_founded (fun c' c => Above c c').
  Proof.
    apply (well_founded_lt_compat C (fun c => Rb - rank c)).
    intros c' c HA; pose proof (Hrank c c' HA); pose proof (Hbnd c'); lia.
  Qed.

  (** ** Two more invariants *)

  (** A Loading fiber has provided each of its keys or will on every path to
      [Done]; an Active fiber has provided each of them. *)
  Definition PIF (f : Fiber) : Prop :=
    match life f with
    | Loading _ P acc _ =>
        forall k, In k (cprovs (fcomp f)) -> (exists p, In (UProv Σ k p) acc) \/ AllDoneProv k P
    | Active _ acc _ => forall k, In k (cprovs (fcomp f)) -> exists p, In (UProv Σ k p) acc
    | _ => True
    end.

  Definition ProvideInv (γ : State) : Prop := forall n f, fibers γ n = Some f -> PIF f.

  (** No accumulator holds a spawn item. *)
  Definition NoSpawnInv (γ : State) : Prop :=
    forall n f m, fibers γ n = Some f -> ~ In (USpawn Σ m) (acc_of (life f)).

  Record CInv (γ : State) : Prop := {
    c_t : TInv γ;
    c_pi : ProvideInv γ;
    c_ns : NoSpawnInv γ
  }.

  Lemma cinv_init : CInv (@init K Σ C).
  Proof.
    split; [exact (tinv_init K_eq_dec Σ prog Kb) | intros n f H; discriminate
           | intros n f m H; discriminate].
  Qed.

  (** The part of [CInv] that holds with spawn. *)
  Record CInv0 (γ : State) : Prop := {
    c0_t : TInv γ;
    c0_pi : ProvideInv γ
  }.

  Lemma cinv_0 (γ : State) : CInv γ -> CInv0 γ.
  Proof. intros [I PI _]; split; assumption. Qed.

  Lemma pi_relife (γ γ1 : State) n f (l : Life) :
    ProvideInv γ ->
    (forall m fm, fibers γ1 m = Some fm ->
       fibers γ m = Some fm \/ exists z, life fm = Inactive Σ z) ->
    PIF (mkFiber Σ (fcomp f) (parent f) (disposed f) l) ->
    ProvideInv (set_life Σ γ1 n f l).
  Proof.
    intros PI Hlk Hl m fm H; apply fibers_set_life_inv in H as [[-> ->]|[_ H]]; [exact Hl|].
    destruct (Hlk m fm H) as [H0|[z Hz]]; [exact (PI m fm H0) | unfold PIF; rewrite Hz; exact Logic.I].
  Qed.

  Lemma ns_relife (γ γ1 : State) n f (l : Life) :
    NoSpawnInv γ ->
    (forall m fm, fibers γ1 m = Some fm ->
       fibers γ m = Some fm \/ exists z, life fm = Inactive Σ z) ->
    (forall m, ~ In (USpawn Σ m) (acc_of l)) ->
    NoSpawnInv (set_life Σ γ1 n f l).
  Proof.
    intros NS Hlk Hl x fx m H; apply fibers_set_life_inv in H as [[-> ->]|[_ H]]; [exact (Hl m)|].
    destruct (Hlk x fx H) as [H0|[z Hz]]; [exact (NS x fx m H0) | rewrite Hz; intros []].
  Qed.

  Lemma pi_same_life (f f' : Fiber) :
    fcomp f' = fcomp f -> life f' = life f -> PIF f -> PIF f'.
  Proof. intros Hc Hl; unfold PIF; rewrite Hc, Hl; auto. Qed.

  Theorem provide_step (γ γ' : State) ℓ :
    TInv γ -> ProvideInv γ -> step γ ℓ = Some γ' -> ProvideInv γ'.
  Proof.
    intros I PI H.
    destruct ℓ as [c|x|x|x|x|x|x|x|x|x|x|x i|x]; cbn [step] in H.
    - destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      intros m fm; cbn; unfold fupd; destruct (Nat.eqb_spec m (next γ));
        [intros [= <-]; exact Logic.I | apply PI].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate]; injection H as <-.
      intros m fm Hm; apply fibers_set_fiber_inv in Hm as [[-> ->]|[_ Hm]].
      + apply (pi_same_life f); [reflexivity | reflexivity | exact (PI _ f Hx)].
      + exact (PI m fm Hm).
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]| | |]; try discriminate; injection H as <-.
      apply (pi_relife γ γ); [exact PI | intros; left; assumption | exact Logic.I].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]| | |]; try discriminate.
      destruct (target γ x); [|discriminate]; injection H as <-.
      apply (pi_relife γ γ); [exact PI | intros; left; assumption |].
      intros k Hk; right; apply Total; exact Hk.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [|discriminate]; injection H as <-.
      pose proof (PI x f Hx) as Pf; unfold PIF in Pf; rewrite Hl in Pf.
      assert (Same : forall γ1 (l : Life), fibers γ1 = fibers γ ->
                PIF (mkFiber Σ (fcomp f) (parent f) (disposed f) l) ->
                ProvideInv (set_life Σ γ1 x f l)).
      { intros γ1 l E Hl'; apply (pi_relife γ γ1); [exact PI | intros m fm; rewrite E; left; auto | exact Hl']. }
      destruct P as [| |k a κ|k s P'|c P'].
      + cbn [load_step]; apply Same; [reflexivity|]; unfold PIF; cbn.
        intros k Hk; destruct (Pf k Hk) as [Hp|Ha]; [exact Hp | inversion Ha].
      + cbn [load_step]; apply Same; [reflexivity | exact Logic.I].
      + rewrite (load_step_op K_eq_dec Σ prog γ x f k a κ acc w).
        destruct (op_binding K_eq_dec Σ prog γ x f k w) as [b|]; [|apply Same; [reflexivity | exact Logic.I]].
        destruct (run a (next γ) (bst Σ b)) as [[[s' g] o]|]; [|apply Same; [reflexivity | exact Logic.I]].
        apply Same; [reflexivity|]; unfold PIF; cbn.
        intros k0 Hk0; destruct (Pf k0 Hk0) as [(p & Hp)|Ha].
        * left; exists p; right; exact Hp.
        * right; inversion Ha; auto.
      + cbn [load_step].
        destruct (kmem K_eq_dec k (provs Σ (prog (fcomp f)))); [|apply Same; [reflexivity | exact Logic.I]].
        destruct (binds γ k); [apply Same; [reflexivity | exact Logic.I]|].
        apply Same; [reflexivity|]; unfold PIF; cbn.
        intros k0 Hk0; destruct (Pf k0 Hk0) as [(p & Hp)|Ha].
        * left; exists p; right; exact Hp.
        * inversion Ha; subst.
          -- left; exists (next γ); left; reflexivity.
          -- right; assumption.
      + cbn [load_step].
        destruct (conflict K_eq_dec Σ prog γ c); [apply Same; [reflexivity | exact Logic.I]|].
        apply (pi_relife γ); [exact PI | |].
        * intros m fm; cbn; unfold fupd.
          destruct (Nat.eqb_spec m (next γ)) as [->|_];
            [intros [= <-]; right; eexists; reflexivity | intros Hm; left; exact Hm].
        * unfold PIF; cbn; intros k0 Hk0; destruct (Pf k0 Hk0) as [(p & Hp)|Ha].
          -- left; exists p; right; exact Hp.
          -- right; inversion Ha; auto.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [|P acc w| |]; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [discriminate|]; injection H as <-.
      apply (pi_relife γ γ); [exact PI | intros; left; assumption | exact Logic.I].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| |acc w|]; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [discriminate|]; injection H as <-.
      apply (pi_relife γ γ); [exact PI | intros; left; assumption | exact Logic.I].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z]; try discriminate.
      unheld H.
      destruct (undo_step_shape K_eq_dec Σ γ γ' x f u acc w z H) as (γ1 & -> & E).
      apply (pi_relife γ γ1); [exact PI | intros m fm; rewrite E; left; auto | exact Logic.I].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|[k p t g|k p|m0] acc] w z]; try discriminate.
      destruct (fibers γ m0) as [g|] eqn:Hg; [|discriminate].
      unheld H; destruct (disposed g); [discriminate|]; injection H as <-.
      intros m fm Hm; apply fibers_set_fiber_inv in Hm as [[-> ->]|[_ Hm]].
      + apply (pi_same_life g); [reflexivity | reflexivity | exact (PI _ g Hg)].
      + exact (PI m fm Hm).
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z]; try discriminate; injection H as <-.
      apply (pi_relife γ γ); [exact PI | intros; left; assumption | exact Logic.I].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z| | |]; try discriminate.
      destruct (disposed f && negb (has_child Σ γ x)); [|discriminate]; injection H as <-.
      intros m fm; cbn; unfold fupd; destruct (Nat.eqb_spec m x); [discriminate | apply PI].
    - (* OReact *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (nth_error (reacts Σ (prog (fcomp f))) i) as [c|]; [|discriminate].
      destruct (disposed f || conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      pose proof (PI x f Hx) as Pf; unfold PIF in Pf; rewrite Hl in Pf.
      apply (pi_relife γ); [exact PI | |].
      + intros m fm; cbn; unfold fupd; destruct (Nat.eqb_spec m (next γ)) as [->|_];
          [intros [= <-]; right; eexists; reflexivity | intros Hm; left; exact Hm].
      + unfold PIF; cbn; intros k Hk; destruct (Pf k Hk) as [p Hp]; exists p; right; exact Hp.
    - (* ORestart *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (disposed f); [discriminate|].
      destruct (life f) as [|P acc w|acc w|]; try discriminate; injection H as <-;
      (apply (pi_relife γ γ); [exact PI | intros; left; assumption | exact Logic.I]).
  Qed.

  Lemma cinv0_step (γ γ' : State) ℓ : CInv0 γ -> step γ ℓ = Some γ' -> CInv0 γ'.
  Proof.
    intros [I PI] H; split;
      [exact (tinv_step K_eq_dec Σ prog Kb HK γ γ' ℓ I H) | exact (provide_step γ γ' ℓ I PI H)].
  Qed.

  (** A reaction adds a child to an Active fiber, so it is excluded: the
      invariants of this file are about systems without spawn. *)
  Theorem cinv_step (γ γ' : State) ℓ : (forall n i, ℓ <> OReact n i) ->
    CInv γ -> step γ ℓ = Some γ' -> CInv γ'.
  Proof.
    intros Hnr [I PI NS] H.
    pose proof (t_wf K_eq_dec Σ prog Kb γ I) as W.
    pose proof (t_prov K_eq_dec Σ prog Kb γ I) as PV.
    split; [exact (tinv_step K_eq_dec Σ prog Kb HK γ γ' ℓ I H) | exact (provide_step γ γ' ℓ I PI H) |].
    destruct ℓ as [c|x|x|x|x|x|x|x|x|x|x|x i|x]; cbn [step] in H.
    - destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      intros m fm y; cbn; unfold fupd; destruct (Nat.eqb_spec m (next γ));
        [intros [= <-] [] | apply NS].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate]; injection H as <-.
      intros m fm y Hm; apply fibers_set_fiber_inv in Hm as [[-> ->]|[_ Hm]].
      + exact (NS _ f y Hx).
      + exact (NS m fm y Hm).
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]| | |]; try discriminate; injection H as <-.
      apply (ns_relife γ γ); [exact NS | intros; left; assumption | intros m []].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]| | |]; try discriminate.
      destruct (target γ x); [|discriminate]; injection H as <-.
      apply (ns_relife γ γ); [exact NS | intros; left; assumption | intros m []].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [|discriminate]; injection H as <-.
      pose proof (NS x f) as Nf; rewrite Hl in Nf; cbn in Nf.
      pose proof (proj1 (pv_fib Σ prog γ PV x f Hx) P acc w Hl) as Hsub.
      assert (Same : forall γ1 (l : Life), fibers γ1 = fibers γ ->
                (forall m, ~ In (USpawn Σ m) (acc_of l)) -> NoSpawnInv (set_life Σ γ1 x f l)).
      { intros γ1 l E Hl'; apply (ns_relife γ γ1); [exact NS | intros m fm; rewrite E; left; auto | exact Hl']. }
      assert (Cons : forall u, (forall m, u <> USpawn Σ m) ->
                forall m, ~ In (USpawn Σ m) (u :: acc)).
      { intros u Hu m [E|Hm]; [exact (Hu m E) | exact (Nf m Hx Hm)]. }
      destruct P as [| |k a κ|k s P'|c P'].
      + cbn [load_step]; apply Same; [reflexivity | intros m; exact (Nf m Hx)].
      + cbn [load_step]; apply Same; [reflexivity | intros m; exact (Nf m Hx)].
      + rewrite (load_step_op K_eq_dec Σ prog γ x f k a κ acc w).
        destruct (op_binding K_eq_dec Σ prog γ x f k w) as [b|];
          [|apply Same; [reflexivity | intros m; exact (Nf m Hx)]].
        destruct (run a (next γ) (bst Σ b)) as [[[s' g] o]|];
          [|apply Same; [reflexivity | intros m; exact (Nf m Hx)]].
        apply Same; [reflexivity|]; apply Cons; intros; discriminate.
      + cbn [load_step].
        destruct (kmem K_eq_dec k (provs Σ (prog (fcomp f))));
          [|apply Same; [reflexivity | intros m; exact (Nf m Hx)]].
        destruct (binds γ k); [apply Same; [reflexivity | intros m; exact (Nf m Hx)]|].
        apply Same; [reflexivity|]; apply Cons; intros; discriminate.
      + exfalso; apply (NoSpawn (fcomp f) c).
        apply (SpawnIn_Sub Σ c (PSpawn c P')); [exact Hsub | apply spi_here].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [discriminate|]; injection H as <-.
      apply (ns_relife γ γ); [exact NS | intros; left; assumption |].
      intros m Hm; apply (NS x f m Hx); rewrite Hl; exact Hm.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [discriminate|]; injection H as <-.
      apply (ns_relife γ γ); [exact NS | intros; left; assumption |].
      intros m Hm; apply (NS x f m Hx); rewrite Hl; exact Hm.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      destruct (undo_step_shape K_eq_dec Σ γ γ' x f u acc w z H) as (γ1 & -> & E).
      apply (ns_relife γ γ1); [exact NS | intros m fm; rewrite E; left; auto |].
      intros m Hm; apply (NS x f m Hx); rewrite Hl; right; exact Hm.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|[k p t g|k p|m0] acc] w z] eqn:Hl; try discriminate.
      exfalso; apply (NS x f m0 Hx); rewrite Hl; left; reflexivity.
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z]; try discriminate; injection H as <-.
      apply (ns_relife γ γ); [exact NS | intros; left; assumption | intros m []].
    - destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z| | |]; try discriminate.
      destruct (disposed f && negb (has_child Σ γ x)); [|discriminate]; injection H as <-.
      intros m fm y; cbn; unfold fupd; destruct (Nat.eqb_spec m x); [discriminate | apply NS].
    - exfalso; exact (Hnr x i eq_refl).
    - (* ORestart *)
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (disposed f); [discriminate|].
      destruct (life f) as [|P acc w|acc w|] eqn:Hl; try discriminate; injection H as <-;
      (apply (ns_relife γ γ); [exact NS | intros; left; assumption |];
       intros m Hm; apply (NS x f m Hx); rewrite Hl; exact Hm).
  Qed.

  (** ** Lifecycle runs keep the fibers, their components and their disposal *)
  Definition is_lifecycle (ℓ : @Label C) : Prop := exists n, In ℓ (lifecycle_labels n).

  Lemma lifecycle_not_react ℓ : is_lifecycle ℓ -> forall n i, ℓ <> OReact n i.
  Proof. intros (m & Hin) n i ->; cbn in Hin; intuition discriminate. Qed.

  Inductive LRun : State -> State -> Prop :=
  | lr_nil γ : LRun γ γ
  | lr_cons γ ℓ γ1 γ2 : is_lifecycle ℓ -> step γ ℓ = Some γ1 -> LRun γ1 γ2 -> LRun γ γ2.

  Definition Static (γ0 γ : State) : Prop :=
    (forall m fm, fibers γ m = Some fm ->
       exists f0, fibers γ0 m = Some f0 /\ fcomp fm = fcomp f0 /\ disposed fm = disposed f0) /\
    (forall m f0, fibers γ0 m = Some f0 -> disposed f0 = false -> exists fm, fibers γ m = Some fm).

  Lemma lstep_static (γ γ' : State) ℓ :
    CInv γ -> is_lifecycle ℓ -> step γ ℓ = Some γ' -> Static γ γ'.
  Proof.
    intros [I PI NS] (n & Hin) H.
    destruct (fibers γ n) as [fn|] eqn:Hn.
    2: { rewrite (step_absent K_eq_dec Σ prog γ n ℓ Hn Hin) in H; discriminate. }
    destruct (lstep_effects K_eq_dec Σ prog Kb rank Hrank γ γ' n ℓ fn I Hin H Hn)
      as (E1 & E2 & E3 & E5 & _).
    split.
    - intros m fm' Hm'.
      destruct (Nat.eq_dec m n) as [->|Hmn].
      + exists fn; split; [exact Hn | exact (E3 fm' Hm')].
      + destruct (fibers γ m) as [fm|] eqn:Hm.
        * destruct (E1 m fm Hmn Hm) as [E|[_ Hsp]].
          -- rewrite E in Hm'; injection Hm' as <-; exists fm; auto.
          -- exfalso; exact (NS n fn m Hn Hsp).
        * exfalso; destruct (E2 m fm' Hm Hm') as [_ HS]; exact (NoSpawn _ _ HS).
    - intros m fm Hm Hd.
      destruct (Nat.eq_dec m n) as [->|Hmn].
      + rewrite Hn in Hm; injection Hm as <-.
        destruct (fibers γ' n) as [fn'|] eqn:Hn'; [eauto|].
        rewrite (E5 eq_refl) in Hd; discriminate.
      + destruct (E1 m fm Hmn Hm) as [E|[_ Hsp]]; [eauto | exfalso; exact (NS n fn m Hn Hsp)].
  Qed.

  Lemma lrun_static (γ0 γ : State) :
    CInv γ0 -> LRun γ0 γ -> CInv γ /\ Static γ0 γ.
  Proof.
    intros I0 R; induction R as [γ|γ ℓ γ1 γ2 Hl Hs R IH].
    - split; [exact I0|]; split.
      + intros m fm H; exists fm; auto.
      + intros m f0 H _; eauto.
    - destruct (lstep_static γ γ1 ℓ I0 Hl Hs) as [S1 S2].
      destruct (IH (cinv_step γ γ1 ℓ (lifecycle_not_react ℓ Hl) I0 Hs)) as [I2 [T1 T2]].
      split; [exact I2|]; split.
      + intros m fm H; destruct (T1 m fm H) as (f1 & H1 & Hc1 & Hd1).
        destruct (S1 m f1 H1) as (f0 & H0 & Hc0 & Hd0).
        exists f0; split; [exact H0 | split; congruence].
      + intros m f0 H0 Hd; destruct (S2 m f0 H0 Hd) as [f1 H1].
        destruct (S1 m f1 H1) as (f0' & H0' & _ & Hd1).
        rewrite H0 in H0'; injection H0' as <-.
        apply (T2 m f1 H1); congruence.
  Qed.

  (** ** Settled states *)
  Definition NoFailed (γ : State) : Prop :=
    forall n f e, fibers γ n = Some f -> life f <> Inactive Σ (Some e).

  Lemma settled_shape (γ : State) n f :
    settled Σ prog γ -> NoFailed γ -> fibers γ n = Some f ->
    disposed f = false /\
    ((life f = Inactive Σ None /\ target γ n = None) \/
     (exists acc w, life f = Active Σ acc w /\ target γ n = Some w)).
  Proof.
    intros St NF Hn; pose proof (St n f Hn) as Sf; unfold settled_fiber in Sf.
    destruct (life f) as [[e|]|P acc w|acc w|acc w z] eqn:Hl; try contradiction.
    - exfalso; exact (NF n f e Hn Hl).
    - destruct Sf as [Hd Ht]; auto.
    - split; [|right; eauto].
      destruct (disposed f) eqn:Hd; [|reflexivity].
      unfold target in Sf; rewrite Hn, Hd in Sf; discriminate.
  Qed.

  Lemma resolve_some (γ : State) (ks : list K) :
    (forall k, In k ks -> exists p, visible Σ γ k = Some p) -> exists w, resolve Σ γ ks = Some w.
  Proof.
    induction ks as [|k ks IH]; intros H; cbn; [eauto|].
    destruct (H k (or_introl eq_refl)) as [p Hp]; rewrite Hp.
    destruct (IH (fun k' Hk' => H k' (or_intror Hk'))) as [w Hw]; rewrite Hw; eauto.
  Qed.

  (** An Active fiber binds each key it may provide. *)
  Lemma active_binds (γ : State) m fm k :
    CInv0 γ -> fibers γ m = Some fm -> is_active (life fm) = true -> In k (cprovs (fcomp fm)) ->
    exists b, binds γ k = Some b /\ owner b = m.
  Proof.
    intros [I PI] Hm Ha Hk.
    pose proof (PI m fm Hm) as P; unfold PIF in P.
    destruct (life fm) as [| |acc w|] eqn:Hl; try discriminate.
    destruct (P k Hk) as [p Hp].
    assert (Hin : In (UProv Σ k p) (acc_of (life fm))) by (rewrite Hl; exact Hp).
    destruct (wf_uprov K_eq_dec Σ prog γ (t_wf K_eq_dec Σ prog Kb γ I) m fm k p Hm Hin)
      as (b & Hb & _ & Ho); eauto.
  Qed.

  (** At a settled state, a fiber is Active iff every key it declares is
      provided by an Active fiber. *)
  Lemma active_iff (γ : State) n f :
    CInv0 γ -> settled Σ prog γ -> NoFailed γ -> fibers γ n = Some f ->
    (is_active (life f) = true <->
     forall k, In k (cdeps (fcomp f)) ->
       exists m fm, fibers γ m = Some fm /\ is_active (life fm) = true /\ In k (cprovs (fcomp fm))).
  Proof.
    intros CI St NF Hn.
    pose proof (t_wf K_eq_dec Σ prog Kb γ (c0_t _ CI)) as W.
    destruct (settled_shape γ n f St NF Hn) as [Hd [[Hl Ht]|(acc & w & Hl & Ht)]].
    - split; [rewrite Hl; discriminate|].
      intros Hall; exfalso.
      assert (Hv : forall k, In k (cdeps (fcomp f)) -> exists p, visible Σ γ k = Some p).
      { intros k Hk; destruct (Hall k Hk) as (m & fm & Hm & Ha & Hp).
        destruct (active_binds γ m fm k CI Hm Ha Hp) as (b & Hb & Ho).
        exists (pid b); unfold visible; rewrite Hb, Ho, Hm, Ha; reflexivity. }
      destruct (resolve_some γ _ Hv) as [w Hw].
      unfold target in Ht; rewrite Hn, Hd in Ht; congruence.
    - split; [intros _|rewrite Hl; reflexivity].
      intros k Hk.
      pose proof (resolve_spec Σ γ _ w (target_spec Σ prog γ n f w Hn Ht)) as [Hkeys Hvis].
      assert (Hin : exists p, In (k, p) w).
      { unfold fdeps in Hkeys; rewrite <- Hkeys in Hk.
        apply in_map_iff in Hk as ([k' p] & E & Hin); cbn in E; subst k'; eauto. }
      destruct Hin as [p Hin].
      destruct (visible_spec Σ γ k p (Hvis k p Hin)) as (b & fo & Hb & _ & Ho & Ha).
      destruct (wf_bind K_eq_dec Σ prog γ W k b Hb) as (fo' & Ho' & _ & Hko & _).
      rewrite Ho in Ho'; injection Ho' as <-.
      exists (owner b), fo; repeat split; auto.
      exact (kmem_In K_eq_dec k _ Hko).
  Qed.

  (** At a settled state, a key is bound by [m] iff [m] is Active and may
      provide it. *)
  Lemma owner_iff (γ : State) k m :
    CInv0 γ -> settled Σ prog γ -> NoFailed γ ->
    (option_map owner (binds γ k) = Some m <->
     exists fm, fibers γ m = Some fm /\ is_active (life fm) = true /\ In k (cprovs (fcomp fm))).
  Proof.
    intros CI St NF.
    pose proof (t_wf K_eq_dec Σ prog Kb γ (c0_t _ CI)) as W.
    split.
    - destruct (binds γ k) as [b|] eqn:Hb; cbn; [intros [= <-] | discriminate].
      destruct (wf_bind K_eq_dec Σ prog γ W k b Hb) as (fo & Ho & Hio & Hko & _).
      exists fo; split; [exact Ho|]; split; [|exact (kmem_In K_eq_dec k _ Hko)].
      destruct (settled_shape γ _ fo St NF Ho) as [_ [[Hl _]|(acc & w & Hl & _)]];
        rewrite Hl in *; [discriminate | reflexivity].
    - intros (fm & Hm & Ha & Hk).
      destruct (active_binds γ m fm k CI Hm Ha Hk) as (b & Hb & Ho).
      rewrite Hb; cbn; congruence.
  Qed.

  (** ** The fixpoint has one solution *)
  Lemma fix_unique (D : nat -> Prop) (Cm : nat -> C -> Prop) (S1 S2 : nat -> Prop) :
    (forall n c, D n -> Cm n c ->
       (S1 n <-> forall k, In k (cdeps c) ->
          exists m c', D m /\ Cm m c' /\ S1 m /\ In k (cprovs c'))) ->
    (forall n c, D n -> Cm n c ->
       (S2 n <-> forall k, In k (cdeps c) ->
          exists m c', D m /\ Cm m c' /\ S2 m /\ In k (cprovs c'))) ->
    forall n c, D n -> Cm n c -> (S1 n <-> S2 n).
  Proof.
    intros H1 H2.
    assert (G : forall r n c, rank c < r -> D n -> Cm n c -> (S1 n <-> S2 n)).
    { induction r as [|r IH]; intros n c Hr Hn Hc; [lia|].
      rewrite (H1 n c Hn Hc), (H2 n c Hn Hc).
      split; intros Hall k Hk; destruct (Hall k Hk) as (m & c' & Hm & Hc' & HS & Hp);
        exists m, c'; (split; [exact Hm | split; [exact Hc'|]]);
        (assert (Hlt : rank c' < rank c) by (apply Hrank; left; exists k; auto));
        (split; [|exact Hp]); apply (IH m c' ltac:(lia) Hm Hc'); exact HS. }
    intros n c; exact (G (S (rank c)) n c (Nat.lt_succ_diag_r _)).
  Qed.

  (** ** Control confluence *)
  Theorem control_confluence (γ0 γ1 γ2 : State) :
    CInv γ0 -> LRun γ0 γ1 -> LRun γ0 γ2 ->
    quiet K_eq_dec Σ prog γ1 -> quiet K_eq_dec Σ prog γ2 ->
    NoFailed γ1 -> NoFailed γ2 ->
    (forall n, (exists f, fibers γ1 n = Some f) <-> (exists f, fibers γ2 n = Some f)) /\
    (forall n f1 f2, fibers γ1 n = Some f1 -> fibers γ2 n = Some f2 ->
       fcomp f1 = fcomp f2 /\ is_active (life f1) = is_active (life f2)) /\
    (forall k, option_map owner (binds γ1 k) = option_map owner (binds γ2 k)).
  Proof.
    intros I0 R1 R2 Q1 Q2 NF1 NF2.
    destruct (lrun_static γ0 γ1 I0 R1) as [C1 [T1 U1]].
    destruct (lrun_static γ0 γ2 I0 R2) as [C2 [T2 U2]].
    assert (St1 : settled Σ prog γ1).
    { apply (quiet_settled K_eq_dec Σ prog Hwf γ1);
        [exact (t_wf K_eq_dec Σ prog Kb γ1 (c_t _ C1)) | exact (t_inv2 K_eq_dec Σ prog Kb γ1 (c_t _ C1))
        | exact Q1]. }
    assert (St2 : settled Σ prog γ2).
    { apply (quiet_settled K_eq_dec Σ prog Hwf γ2);
        [exact (t_wf K_eq_dec Σ prog Kb γ2 (c_t _ C2)) | exact (t_inv2 K_eq_dec Σ prog Kb γ2 (c_t _ C2))
        | exact Q2]. }
    set (D := fun n => exists f0, fibers γ0 n = Some f0 /\ disposed f0 = false).
    set (Cm := fun n c => exists f0, fibers γ0 n = Some f0 /\ fcomp f0 = c).
    (* presence in a final state is membership in D, with the component of γ0 *)
    assert (Pres : forall γ, Static γ0 γ -> settled Σ prog γ -> NoFailed γ ->
              forall n, (exists f, fibers γ n = Some f) <-> D n).
    { intros γ [Ta Ub] St NF n; split.
      - intros [f Hf]; destruct (Ta n f Hf) as (f0 & H0 & _ & Hd).
        exists f0; split; [exact H0|].
        rewrite <- Hd; exact (proj1 (settled_shape γ n f St NF Hf)).
      - intros (f0 & H0 & Hd); exact (Ub n f0 H0 Hd). }
    assert (Comp : forall γ, Static γ0 γ -> forall n f c, fibers γ n = Some f -> Cm n c ->
              fcomp f = c).
    { intros γ [Ta _] n f c Hf (f0 & H0 & Hc).
      destruct (Ta n f Hf) as (f0' & H0' & Hc' & _); congruence. }
    set (S1 := fun n => exists f, fibers γ1 n = Some f /\ is_active (life f) = true).
    set (S2 := fun n => exists f, fibers γ2 n = Some f /\ is_active (life f) = true).
    assert (Fix : forall γ (S : nat -> Prop), CInv γ -> Static γ0 γ -> settled Σ prog γ -> NoFailed γ ->
              (forall n, S n <-> exists f, fibers γ n = Some f /\ is_active (life f) = true) ->
              forall n c, D n -> Cm n c ->
                (S n <-> forall k, In k (cdeps c) ->
                   exists m c', D m /\ Cm m c' /\ S m /\ In k (cprovs c'))).
    { intros γ S CI TS St NF HS n c Hn Hc.
      destruct (proj2 (Pres γ TS St NF n) Hn) as [f Hf].
      pose proof (Comp γ TS n f c Hf Hc) as Efc.
      rewrite HS; split.
      - intros (f' & Hf' & Ha); rewrite Hf in Hf'; injection Hf' as <-.
        intros k Hk; rewrite <- Efc in Hk.
        destruct (proj1 (active_iff γ n f (cinv_0 _ CI) St NF Hf) Ha k Hk) as (m & fm & Hm & Ham & Hp).
        assert (Dm : D m) by (apply (Pres γ TS St NF m); eauto).
        destruct Dm as (f0 & H0 & Hd0).
        exists m, (fcomp f0); split; [exists f0; auto|]; split; [exists f0; auto|].
        split; [apply HS; eauto|].
        rewrite <- (Comp γ TS m fm (fcomp f0) Hm (ex_intro _ f0 (conj H0 eq_refl))); exact Hp.
      - intros Hall; exists f; split; [exact Hf|].
        apply (proj2 (active_iff γ n f (cinv_0 _ CI) St NF Hf)).
        intros k Hk; rewrite Efc in Hk.
        destruct (Hall k Hk) as (m & c' & Hm & Hc' & HSm & Hp).
        apply HS in HSm; destruct HSm as (fm & Hfm & Ha).
        exists m, fm; repeat split; auto.
        rewrite (Comp γ TS m fm c' Hfm Hc'); exact Hp. }
    assert (Same : forall n c, D n -> Cm n c -> (S1 n <-> S2 n)).
    { apply fix_unique.
      - apply (Fix γ1 S1 C1 (conj T1 U1) St1 NF1); intros; reflexivity.
      - apply (Fix γ2 S2 C2 (conj T2 U2) St2 NF2); intros; reflexivity. }
    assert (Same' : forall n, D n -> (S1 n <-> S2 n)).
    { intros n Hn; destruct Hn as (f0 & H0 & Hd0).
      apply (Same n (fcomp f0)); [exists f0; auto | exists f0; auto]. }
    split; [|split].
    - intros n; rewrite (Pres γ1 (conj T1 U1) St1 NF1 n), (Pres γ2 (conj T2 U2) St2 NF2 n).
      reflexivity.
    - intros n f1 f2 H1 H2.
      assert (Dn : D n) by (apply (Pres γ1 (conj T1 U1) St1 NF1); eauto).
      destruct (T1 n f1 H1) as (f0 & H0 & Hc1 & _).
      destruct (T2 n f2 H2) as (f0' & H0' & Hc2 & _).
      rewrite H0 in H0'; injection H0' as <-.
      split; [congruence|].
      pose proof (Same' n Dn) as E; unfold S1, S2 in E.
      destruct (is_active (life f1)) eqn:A1, (is_active (life f2)) eqn:A2; try reflexivity.
      + exfalso; destruct (proj1 E (ex_intro _ f1 (conj H1 A1))) as (f2' & H2' & A2').
        rewrite H2 in H2'; injection H2' as <-; congruence.
      + exfalso; destruct (proj2 E (ex_intro _ f2 (conj H2 A2))) as (f1' & H1' & A1').
        rewrite H1 in H1'; injection H1' as <-; congruence.
    - intros k.
      assert (Own : forall m, option_map owner (binds γ1 k) = Some m <->
                              option_map owner (binds γ2 k) = Some m).
      { intros m.
        rewrite (owner_iff γ1 k m (cinv_0 _ C1) St1 NF1), (owner_iff γ2 k m (cinv_0 _ C2) St2 NF2).
        split.
        - intros (fm & Hm & Ha & Hp).
          assert (Dm : D m) by (apply (Pres γ1 (conj T1 U1) St1 NF1); eauto).
          destruct (proj1 (Same' m Dm) (ex_intro _ fm (conj Hm Ha))) as (fm2 & Hm2 & Ha2).
          exists fm2; repeat split; auto.
          destruct (T1 m fm Hm) as (f0 & H0 & Hc1 & _).
          destruct (T2 m fm2 Hm2) as (f0' & H0' & Hc2 & _).
          rewrite H0 in H0'; injection H0' as <-; rewrite Hc2, <- Hc1; exact Hp.
        - intros (fm & Hm & Ha & Hp).
          assert (Dm : D m) by (apply (Pres γ2 (conj T2 U2) St2 NF2); eauto).
          destruct (proj2 (Same' m Dm) (ex_intro _ fm (conj Hm Ha))) as (fm1 & Hm1 & Ha1).
          exists fm1; repeat split; auto.
          destruct (T2 m fm Hm) as (f0 & H0 & Hc2 & _).
          destruct (T1 m fm1 Hm1) as (f0' & H0' & Hc1 & _).
          rewrite H0 in H0'; injection H0' as <-; rewrite Hc1, <- Hc2; exact Hp. }
      destruct (option_map owner (binds γ1 k)) as [m1|] eqn:O1,
               (option_map owner (binds γ2 k)) as [m2|] eqn:O2; try reflexivity.
      + pose proof (proj1 (Own m1) eq_refl) as E; congruence.
      + pose proof (proj1 (Own m1) eq_refl) as E; congruence.
      + pose proof (proj2 (Own m2) eq_refl) as E; congruence.
  Qed.
  (** ** A quiet state is always reached *)
  Theorem exists_quiet (γ : State) :
    CInv γ -> exists γ', LRun γ γ' /\ quiet K_eq_dec Σ prog γ'.
  Proof.
    intros I.
    pose proof (termination K_eq_dec Σ prog Kb HK rank Rb Hrank Hbnd γ (c_t _ I)) as A.
    revert I; induction A as [γ _ IH]; intros I.
    pose proof (t_wf K_eq_dec Σ prog Kb γ (c_t _ I)) as W.
    destruct (enabled K_eq_dec Σ prog γ) eqn:E.
    - apply existsb_exists in E as (n & _ & E).
      apply existsb_exists in E as (ℓ & Hin & E).
      destruct (step γ ℓ) as [γ1|] eqn:Hs; [|discriminate].
      destruct (IH γ1 (conj (c_t _ I) (ex_intro _ n (ex_intro _ ℓ (conj Hin Hs))))
                   (cinv_step γ γ1 ℓ (lifecycle_not_react ℓ (ex_intro _ n Hin)) I Hs)) as (γ' & R & Q).
      exists γ'; split; [|exact Q].
      apply (lr_cons γ ℓ γ1 γ'); [exists n; exact Hin | exact Hs | exact R].
    - exists γ; split; [constructor|].
      intros n ℓ Hin.
      destruct (fibers γ n) as [f|] eqn:Hn; [|exact (step_absent K_eq_dec Σ prog γ n ℓ Hn Hin)].
      destruct (step γ ℓ) as [γ'|] eqn:Hs; [|reflexivity].
      exfalso; apply (proj2 (not_true_iff_false _) E), existsb_exists.
      exists n; split; [exact (in_names K_eq_dec Σ prog γ n f W Hn)|].
      apply existsb_exists; exists ℓ; split; [exact Hin | rewrite Hs; reflexivity].
  Qed.
End Confluence.
