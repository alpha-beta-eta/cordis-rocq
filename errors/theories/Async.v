(** * Deterministic external reads (errors/DESIGN.md, section 5.2)

    A program may read the outside world: [EExt e κ] asks request [e] and
    continues with the answer, or fails if the world refuses. A read does
    not touch the managed state and leaves nothing to undo. An operation
    that needs outside data is written as a read followed by an operation
    taking the data as a parameter (DESIGN.md D6, [prepare]/[commit]).

    The world is deterministic: a function [world c : E -> option R] per
    component, the same answer to the same request for the whole run. Then
    the extended calculus is not a new calculus: unfolding every read
    against the world ([unfold]) gives a core program, and the component
    table [prog'] is an ordinary core table. Every theorem of the core,
    and of the other files of this directory (they are stated for any
    table), holds for [prog'] as it is. The only work is to state the
    component obligations on extended programs, so that they hold for
    every world:

    - [ebounded_unfold]: bounded, counting a read as free;
    - [eadp_unfold]: every path to [Done] provides a declared key;
    - [spawn_unfold], [above_eabove]: spawns, hence ranks, are read off the
      extended program.

    [atermination] and [acontrol_confluence] show two core theorems used
    this way. Confluence speaks of runs with the same inputs, and the
    world is one of them: two runs against the same world agree. To read
    the world afresh, the orchestrator replaces the component by one with
    a new world (dispose, then insert), as the core models a change of
    configuration (DESIGN.md difference l).

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool.
From Cordis Require Import Prelude Service Calculus Preservation Progress Termination Recovery
  Confluence.
Import ListNotations.

Section Async.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type}.
  Context (E R : Type).

  Local Notation Prog := (@Prog K Σ C).

  (** ** Extended programs *)
  Inductive EProg : Type :=
  | EDone
  | EFail
  | EOp (k : K) (a : Op Σ) (κ : Out Σ -> EProg)
  | EProvide (k : K) (s : St Σ) (P : EProg)
  | ESpawn (c : C) (P : EProg)
  | EExt (e : E) (κ : R -> EProg).

  Fixpoint unfold (ρ : E -> option R) (P : EProg) : Prog :=
    match P with
    | EDone => PDone
    | EFail => PFail
    | EOp k a κ => POp k a (fun o => unfold ρ (κ o))
    | EProvide k s P => PProvide k s (unfold ρ P)
    | ESpawn c P => PSpawn c (unfold ρ P)
    | EExt e κ => match ρ e with Some r => unfold ρ (κ r) | None => PFail end
    end.

  Record XComponent : Type := mkX {
    xdeps : list K;
    xprovs : list K;
    xbody : EProg;
    xreacts : list C
  }.

  Variable xprog : C -> XComponent.
  Variable world : C -> E -> option R.

  Definition prog' (c : C) : @Component K Σ C :=
    mkComponent (xdeps (xprog c)) (xprovs (xprog c)) (unfold (world c) (xbody (xprog c)))
                (xreacts (xprog c)).

  (** ** Obligations on extended programs *)
  Inductive EBounded : nat -> EProg -> Prop :=
  | ebd_done j : EBounded j EDone
  | ebd_fail j : EBounded j EFail
  | ebd_op j k a κ : (forall o, EBounded j (κ o)) -> EBounded (S j) (EOp k a κ)
  | ebd_prov j k s P : EBounded j P -> EBounded (S j) (EProvide k s P)
  | ebd_spawn j c P : EBounded j P -> EBounded (S j) (ESpawn c P)
  | ebd_ext j e κ : (forall r, EBounded j (κ r)) -> EBounded j (EExt e κ).

  Lemma ebounded_unfold ρ j P : EBounded j P -> Bounded Σ j (unfold ρ P).
  Proof.
    induction 1 as [j|j|j k a κ _ IH|j k s P _ IH|j c P _ IH|j e κ _ IH]; cbn.
    - constructor.
    - constructor.
    - constructor; exact IH.
    - constructor; exact IH.
    - constructor; exact IH.
    - destruct (ρ e) as [r|]; [exact (IH r) | constructor].
  Qed.

  Inductive EAllDoneProv (k : K) : EProg -> Prop :=
  | eadp_fail : EAllDoneProv k EFail
  | eadp_op k' a κ : (forall o, EAllDoneProv k (κ o)) -> EAllDoneProv k (EOp k' a κ)
  | eadp_here s P : EAllDoneProv k (EProvide k s P)
  | eadp_prov k' s P : EAllDoneProv k P -> EAllDoneProv k (EProvide k' s P)
  | eadp_spawn c P : EAllDoneProv k P -> EAllDoneProv k (ESpawn c P)
  | eadp_ext e κ : (forall r, EAllDoneProv k (κ r)) -> EAllDoneProv k (EExt e κ).

  Lemma eadp_unfold ρ k P : EAllDoneProv k P -> AllDoneProv Σ k (unfold ρ P).
  Proof.
    induction 1 as [|k' a κ _ IH|s P|k' s P _ IH|c P _ IH|e κ _ IH]; cbn.
    - constructor.
    - constructor; exact IH.
    - constructor.
    - constructor; exact IH.
    - constructor; exact IH.
    - destruct (ρ e) as [r|]; [exact (IH r) | constructor].
  Qed.

  Inductive ESpawnIn (c : C) : EProg -> Prop :=
  | espi_here P : ESpawnIn c (ESpawn c P)
  | espi_op k a κ o : ESpawnIn c (κ o) -> ESpawnIn c (EOp k a κ)
  | espi_prov k s P : ESpawnIn c P -> ESpawnIn c (EProvide k s P)
  | espi_spawn c' P : ESpawnIn c P -> ESpawnIn c (ESpawn c' P)
  | espi_ext e κ r : ESpawnIn c (κ r) -> ESpawnIn c (EExt e κ).

  Lemma spawn_unfold ρ c P : SpawnIn Σ c (unfold ρ P) -> ESpawnIn c P.
  Proof.
    induction P as [| |k a κ IH|k s P IH|c' P IH|e κ IH]; cbn; intros H.
    - inversion H.
    - inversion H.
    - inversion H; subst. eapply espi_op; apply IH; eassumption.
    - inversion H; subst; apply espi_prov, IH; assumption.
    - inversion H; subst; [apply espi_here | apply espi_spawn, IH; assumption].
    - destruct (ρ e) as [r|] eqn:Hr; [|inversion H].
      eapply espi_ext; apply IH; exact H.
  Qed.

  (** The dependency order, read off the extended programs. *)
  Definition EAbove (c c' : C) : Prop :=
    (exists k, In k (xprovs (xprog c)) /\ In k (xdeps (xprog c'))) \/
    ESpawnIn c' (xbody (xprog c)) \/ In c' (xreacts (xprog c)).

  Lemma above_eabove c c' : Above Σ prog' c c' -> EAbove c c'.
  Proof.
    intros [HP|[HS|HR]]; [left; exact HP| |right; right; exact HR].
    right; left; exact (spawn_unfold _ c' _ HS).
  Qed.

  (** ** Core theorems for the unfolded table *)
  Section Use.
    Variable Kb : nat.
    Hypothesis EHK : forall c, EBounded Kb (xbody (xprog c)).
    Variable rank : C -> nat.
    Variable Rb : nat.
    Hypothesis EHrank : forall c c', EAbove c c' -> rank c < rank c'.
    Hypothesis Hbnd : forall c, rank c <= Rb.

    Lemma HK' : forall c, Bounded Σ Kb (body Σ (prog' c)).
    Proof. intros c; exact (ebounded_unfold _ _ _ (EHK c)). Qed.

    Lemma Hrank' : forall c c', Above Σ prog' c c' -> rank c < rank c'.
    Proof. intros c c' H; exact (EHrank c c' (above_eabove c c' H)). Qed.

    (** Lifecycle steps terminate, whatever the world answers. *)
    Theorem atermination (γ : @State K Σ C) :
      TInv K_eq_dec Σ prog' Kb γ -> Acc (LStepRel K_eq_dec Σ prog' Kb) γ.
    Proof. exact (termination K_eq_dec Σ prog' Kb HK' rank Rb Hrank' Hbnd γ). Qed.

    Hypothesis ENoSpawn : forall c c', ~ ESpawnIn c' (xbody (xprog c)).
    Hypothesis ETotal : forall c k, In k (xprovs (xprog c)) -> EAllDoneProv k (xbody (xprog c)).

    (** Control confluence against a fixed world. *)
    Theorem acontrol_confluence (γ0 γ1 γ2 : @State K Σ C) :
      CInv K_eq_dec Σ prog' Kb γ0 -> LRun K_eq_dec Σ prog' γ0 γ1 -> LRun K_eq_dec Σ prog' γ0 γ2 ->
      quiet K_eq_dec Σ prog' γ1 -> quiet K_eq_dec Σ prog' γ2 ->
      NoFailed Σ γ1 -> NoFailed Σ γ2 ->
      (forall n, (exists f, fibers Σ γ1 n = Some f) <-> (exists f, fibers Σ γ2 n = Some f)) /\
      (forall n f1 f2, fibers Σ γ1 n = Some f1 -> fibers Σ γ2 n = Some f2 ->
         comp Σ f1 = comp Σ f2 /\ is_active Σ (life Σ f1) = is_active Σ (life Σ f2)) /\
      (forall k, option_map (owner Σ) (binds Σ γ1 k) = option_map (owner Σ) (binds Σ γ2 k)).
    Proof.
      apply (control_confluence K_eq_dec Σ prog' Kb HK' rank Rb Hrank' Hbnd).
      - intros c c' H; exact (ENoSpawn c c' (spawn_unfold _ c' _ H)).
      - intros c k Hk; exact (eadp_unfold _ k _ (ETotal c k Hk)).
    Qed.
  End Use.
End Async.
