(** * A registry and listeners, side by side

    A plugin system whose startup programs register entries in a
    name-keyed registry (tools, commands) and callbacks on events, and may
    look up registry entries other than those another fiber registers at
    the same key ([HG]). Each key
    holds a registry or a list of listeners. Two schedules that end quiet
    with no failure agree up to renaming ([Agree]), and each key ends with
    related states: the same entries for a registry key, the same callbacks
    (as a multiset) for an event key. *)

From Stdlib Require Import List.
From Cordis Require Import Prelude Service ServiceSeq Calculus Recovery Termination Progress
  Confluence StateInv Episode StateConf SpawnConf Compose Registry RegistryConf Listeners.

Section Composed.
  Context (Name V Cb : Type).
  Context (name_eq_dec : forall x y : Name, {x = y} + {x <> y}).
  Context (cb_eq_dec : forall x y : Cb, {x = y} + {x <> y}).

  Definition RegListeners : Service := Sum (Registry Name V name_eq_dec) (Listeners Cb cb_eq_dec).

  (** Which operations two fibers may perform at one key: anything but a
      lookup of a name the other fiber registers. *)
  Definition RegMeet : Op RegListeners -> Op RegListeners -> Prop :=
    sumG (Registry Name V name_eq_dec) (Listeners Cb cb_eq_dec) (reg_meet Name V) (fun _ _ => True).

  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context {C : Type} (prog : C -> @Component K RegListeners C).
  Variable Kb : nat.
  Hypothesis HK : forall c, Bounded RegListeners Kb (body RegListeners (prog c)).
  Variable rank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', Above RegListeners prog c c' -> rank c < rank c'.
  Hypothesis Hbnd : forall c, rank c <= Rb.
  Hypothesis Total : forall c k, In k (provs RegListeners (prog c)) ->
    AllDoneProv RegListeners k (body RegListeners (prog c)).
  Hypothesis HG : forall k a b, CoPair RegListeners prog k a b -> RegMeet a b.

  Theorem composed_confluence (γ0 γ1 γ2 : State RegListeners) :
    PInv K_eq_dec RegListeners prog Kb γ0 -> SLInv RegListeners γ0 ->
    LRun K_eq_dec RegListeners prog γ0 γ1 -> LRun K_eq_dec RegListeners prog γ0 γ2 ->
    quiet K_eq_dec RegListeners prog γ1 -> quiet K_eq_dec RegListeners prog γ2 ->
    NoFailed RegListeners γ1 -> NoFailed RegListeners γ2 ->
    Agree RegListeners γ1 γ2.
  Proof.
    exact (service_confluence RegMeet
             (sum_hyps _ _ _ _ (registry_hyps Name V name_eq_dec) (listeners_hyps Cb cb_eq_dec))
             K_eq_dec prog Kb HK rank Rb Hrank Hbnd Total HG γ0 γ1 γ2).
  Qed.
End Composed.
