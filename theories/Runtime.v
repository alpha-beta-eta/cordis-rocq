(** * Runtime effects (DESIGN.md, difference k)

    Once a plugin is Active, events reach it and its handlers run. A
    component lists its handlers ([reacts]); the environment rule
    [OReact n i] runs the i-th handler of an Active fiber [n] as a child
    fiber, whose operations form one runtime effect. The child is pushed on
    [n]'s accumulator like a spawn, so:
    - disposing the effect is disposing the child ([ODispose]); it unloads
      and is removed, and [n] keeps a stale spawn item that does nothing;
    - when [n] itself unloads, it retires every runtime child first
      ([Ordering.parent_waits_child]).

    [effect_exact]: once a runtime effect has come and gone, every binding's
    state is ≃ to the state the same execution reaches with the effect's
    operations left out, whatever the other fibers did meanwhile. This is
    [Recovery.recovery_exact] for the child; it asks independence only of
    operations two fibers may perform at one key ([CoPair]).

    A handler component provides no key in practice; [CoPair] then treats
    it as one that may run in several fibers at once, as handlers do (one
    effect per agent, say). *)

From Stdlib Require Import List.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Recovery.
Import ListNotations.

Section Runtime.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation life := (life Σ).
  Local Notation bst := (bst Σ).
  Local Notation step := (step K_eq_dec Σ prog).

  Hypothesis Hwb : forall a t, WellBehaved (Σ := Σ) a t.
  Hypothesis Hind : forall k a b ta tb, CoPair Σ prog k a b -> ta <> tb ->
    RevertIndep (Σ := Σ) a ta b tb.

  (** What a reaction does. *)
  Lemma react_shape (γ γ' : State) n i :
    step γ (OReact n i) = Some γ' ->
    exists f acc w c,
      fibers γ n = Some f /\ life f = Active Σ acc w /\
      nth_error (reacts Σ (prog (Calculus.comp Σ f))) i = Some c /\
      Calculus.disposed Σ f = false /\
      γ' = set_life Σ (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next Σ γ)
             (Some (mkFiber Σ c (Some n) false (Inactive Σ None)))))) n f
             (Active Σ (USpawn Σ (next Σ γ) :: acc) w).
  Proof.
    cbn [step]; destruct (fibers γ n) as [f|]; [|discriminate].
    destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
    destruct (nth_error (reacts Σ (prog (Calculus.comp Σ f))) i) as [c|] eqn:Hc; [|discriminate].
    destruct (Calculus.disposed Σ f) eqn:Hd; [discriminate|]; cbn.
    destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; intros [= <-].
    exists f, acc, w, c; auto.
  Qed.

  Lemma absent_no_pending (γ : State) n : fibers γ n = None -> no_pending K_eq_dec Σ n γ.
  Proof. intros H k p; unfold pacc; rewrite H; reflexivity. Qed.

  Lemma inactive_no_pending (γ : State) n f z :
    fibers γ n = Some f -> life f = Inactive Σ z -> no_pending K_eq_dec Σ n γ.
  Proof. intros H Hl k p; unfold pacc; rewrite H, Hl; reflexivity. Qed.

  (** A runtime effect, from before it exists to after it is gone, leaves
      every binding as if it had never run. [σ] is the store the shadow
      execution keeps, applying every operation and inverse but [n]'s. *)
  Theorem effect_exact (γ0 : State) ls γ σ n :
    WF K_eq_dec Σ prog γ0 -> Prov Σ prog γ0 -> fibers γ0 n = None ->
    shadow_run K_eq_dec Σ prog n γ0 ls (store Σ γ0) = Some (γ, σ) ->
    fibers γ n = None ->
    forall k, match binds γ k, σ k with
              | Some b, Some s => bst b ≃ s
              | None, None => True
              | _, _ => False
              end.
  Proof.
    intros W P H0 R H1.
    exact (recovery_exact K_eq_dec Σ prog Hwb Hind n γ0 ls γ σ W P
             (absent_no_pending γ0 n H0) R (absent_no_pending γ n H1)).
  Qed.

  (** The same, for an effect whose child is still present but Inactive. *)
  Theorem effect_exact_inactive (γ0 : State) ls γ σ n f z :
    WF K_eq_dec Σ prog γ0 -> Prov Σ prog γ0 -> fibers γ0 n = None ->
    shadow_run K_eq_dec Σ prog n γ0 ls (store Σ γ0) = Some (γ, σ) ->
    fibers γ n = Some f -> life f = Inactive Σ z ->
    forall k, match binds γ k, σ k with
              | Some b, Some s => bst b ≃ s
              | None, None => True
              | _, _ => False
              end.
  Proof.
    intros W P H0 R H1 Hl.
    exact (recovery_exact K_eq_dec Σ prog Hwb Hind n γ0 ls γ σ W P
             (absent_no_pending γ0 n H0) R (inactive_no_pending γ n f z H1 Hl)).
  Qed.
End Runtime.
