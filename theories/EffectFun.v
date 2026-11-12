(** * Effect functions, ⋄, witnessed effects, effect *)

From Stdlib Require Import List Lia.
From Cordis Require Import Prelude Twisted.
Import ListNotations.

(** ** 𝔈Γ := Γ → ∂Γ *)
Definition Eff (Γ : Type) : Type := Γ -> Dctx Γ.

(** ** 𝔈*Γ, as a predicate on 𝔈Γ:
    ∀ γ. let (δ, g) := e γ in g δ = γ *)
Definition Witnessed {Γ : Type} (e : Eff Γ) : Prop :=
  forall γ, let (δ, g) := e γ in g δ = γ.

(** The same condition written with projections, which is the form the
    proofs below use. *)
Lemma witnessed_iff {Γ : Type} (e : Eff Γ) :
  Witnessed e <-> forall γ, snd (e γ) (fst (e γ)) = γ.
Proof.
  split; intros H γ; specialize (H γ); destruct (e γ); exact H.
Qed.

(** ** The induced effect ⌜f, g⌝ := γ ↦ (f γ, g) *)
Definition induced {Γ : Type} (p : Twisted Γ) : Eff Γ :=
  fun γ => (fst p γ, snd p).

(** If g ∘ f = id then ⌜f, g⌝ ∈ 𝔈*Γ. *)
Lemma induced_witnessed {Γ : Type} (f g : End Γ) :
  g ∘ f = id -> Witnessed (induced (f, g)).
Proof. intros H γ; exact (equal_f H γ). Qed.

(** ** Effect composition
    e₁ ⋄ e₂ := γ ↦ let (δ, s) := e₂ γ in let (ε, t) := e₁ δ in (ε, s ∘ t).
    It is defined with projections, so that most laws hold by computation;
    [diamond_unfold] shows it agrees with the definition in the notes. *)
Definition diamond {Γ : Type} (e1 e2 : Eff Γ) : Eff Γ :=
  fun γ => (fst (e1 (fst (e2 γ))), snd (e2 γ) ∘ snd (e1 (fst (e2 γ)))).
Notation "e1 ⋄ e2" := (diamond e1 e2) (at level 40, left associativity).

Lemma diamond_unfold {Γ : Type} (e1 e2 : Eff Γ) (γ : Γ) :
  (e1 ⋄ e2) γ = let (δ, s) := e2 γ in let (ε, t) := e1 δ in (ε, s ∘ t).
Proof.
  unfold diamond; destruct (e2 γ) as [δ s]; cbn.
  destruct (e1 δ); reflexivity.
Qed.

(** η_Γ := γ ↦ (γ, id) *)
Definition eta {Γ : Type} : Eff Γ := fun γ => (γ, id).

(** 𝔈Γ is a monoid under ⋄ with unit η_Γ. *)
Theorem eff_monoid (Γ : Type) : IsMonoid (@diamond Γ) eta.
Proof.
  split.
  - reflexivity.
  - intros e; extensionality γ; unfold diamond, eta; cbn.
    destruct (e γ); reflexivity.
  - intros e; extensionality γ; unfold diamond, eta; cbn.
    destruct (e γ); reflexivity.
Qed.

(** ⌜-, -⌝ : 𝔗Γ → 𝔈Γ is a monoid homomorphism. *)
Theorem induced_hom (Γ : Type) :
  IsMonoidHom (@tcomp Γ) tunit diamond eta (@induced Γ).
Proof. split; reflexivity. Qed.

(** 𝔈*Γ is a submonoid of 𝔈Γ. *)
Theorem witnessed_submonoid (Γ : Type) :
  IsSubmonoid (@diamond Γ) eta Witnessed.
Proof.
  split.
  - intros γ; reflexivity.
  - intros e1 e2 H1 H2; apply witnessed_iff; intros γ.
    pose proof (proj1 (witnessed_iff e1) H1) as H1'.
    pose proof (proj1 (witnessed_iff e2) H2) as H2'.
    change (snd (e2 γ) (snd (e1 (fst (e2 γ))) (fst (e1 (fst (e2 γ))))) = γ).
    rewrite H1'; apply H2'.
Qed.

(** ** effect : 𝔈Γ → 𝔈(∂Γ)
    effect(e)(γ, φ) := let (δ, g) := e γ in ((δ, φ ∘ g), track(g, pr₁ ∘ e)) *)
Definition effect {Γ : Type} (e : Eff Γ) : Eff (Dctx Γ) :=
  fun x => ((fst (e (fst x)), snd x ∘ snd (e (fst x))),
            track (snd (e (fst x)), fst ∘ e)).

Lemma effect_unfold {Γ : Type} (e : Eff Γ) (γ : Γ) (φ : End Γ) :
  effect e (γ, φ) = let (δ, g) := e γ in ((δ, φ ∘ g), track (g, fst ∘ e)).
Proof. unfold effect; cbn; destruct (e γ); reflexivity. Qed.

(** effect(e₁ ⋄ e₂) = effect(e₁) ⋄ effect(e₂), and effect preserves the unit:
    effect is a monoid homomorphism 𝔈Γ → 𝔈(∂Γ). *)
Theorem effect_diamond {Γ : Type} (e1 e2 : Eff Γ) :
  effect (e1 ⋄ e2) = effect e1 ⋄ effect e2.
Proof. reflexivity. Qed.

Theorem effect_eta {Γ : Type} : effect (@eta Γ) = eta.
Proof.
  extensionality x; destruct x as [γ φ]; unfold effect, eta; cbn.
  f_equal; extensionality y; destruct y; reflexivity.
Qed.

Theorem effect_hom (Γ : Type) :
  IsMonoidHom (@diamond Γ) eta (@diamond (Dctx Γ)) eta (@effect Γ).
Proof. split; [apply effect_eta | apply effect_diamond]. Qed.

(** ** pr₁ relates each lifted map to the map it lifts (Theorem 14)
    With f := pr₁ ∘ e and f' := pr₁ ∘ effect(e):
    1. pr₁ ∘ f' = f ∘ pr₁;
    2. at each (γ, φ), the lifted inverse g' and the inverse g := pr₂(e γ)
       satisfy pr₁ ∘ g' = g ∘ pr₁. *)
Theorem effect_fwd_fst {Γ : Type} (e : Eff Γ) :
  fst ∘ (fst ∘ effect e) = (fst ∘ e) ∘ fst.
Proof. reflexivity. Qed.

Theorem effect_inv_fst {Γ : Type} (e : Eff Γ) (x : Dctx Γ) :
  fst ∘ snd (effect e x) = snd (e (fst x)) ∘ fst.
Proof. reflexivity. Qed.

(** ** The lifted inverse (the paper's Theorem 15)
    Let e ∈ 𝔈*Γ, f := pr₁ ∘ e, (δ, g) := e γ, (Δ, G) := effect(e)(γ, φ).
    Then G Δ = (γ, φ ∘ g ∘ f). *)
Section LiftedInverse.
  Context {Γ : Type} (e : Eff Γ) (He : Witnessed e).

  Let f : End Γ := fst ∘ e.

  Theorem effect_revert (γ : Γ) (φ : End Γ) :
    let (Δ, G) := effect e (γ, φ) in
    G Δ = (γ, φ ∘ snd (e γ) ∘ f).
  Proof.
    pose proof (proj1 (witnessed_iff e) He) as He'.
    change ((snd (e γ) (fst (e γ)), φ ∘ snd (e γ) ∘ f)
            = (γ, φ ∘ snd (e γ) ∘ f)).
    now rewrite He'.
  Qed.

  (** (φ ∘ g ∘ f)(γ) = φ(γ): the soundness invariant is preserved. *)
  Theorem effect_revert_sound (γ : Γ) (φ : End Γ) :
    (φ ∘ snd (e γ) ∘ f) γ = φ γ.
  Proof.
    pose proof (proj1 (witnessed_iff e) He) as He'.
    change (φ (snd (e γ) (fst (e γ))) = φ γ); now rewrite He'.
  Qed.

  (** effect(e) ∈ 𝔈*(∂Γ) iff every inverse e yields is a global left
      inverse of f: ∀ γ. let (_, g_γ) := e γ in g_γ ∘ f = id. *)
  Theorem effect_witnessed_iff :
    Witnessed (effect e) <-> forall γ, snd (e γ) ∘ f = id.
  Proof.
    pose proof (proj1 (witnessed_iff e) He) as He'.
    rewrite witnessed_iff; split.
    - intros H γ.
      specialize (H (γ, id)).
      apply (f_equal snd) in H; exact H.
    - intros H [γ φ].
      change ((snd (e γ) (fst (e γ)), φ ∘ (snd (e γ) ∘ f)) = (γ, φ)).
      rewrite He', H; reflexivity.
  Qed.
End LiftedInverse.

(** ** Sequences of effects (the Comment in the notes)
    A list [e₁; …; eₙ] is applied head first, so it denotes eₙ ⋄ ⋯ ⋄ e₁. *)
Fixpoint diamonds {Γ : Type} (es : list (Eff Γ)) : Eff Γ :=
  match es with
  | [] => eta
  | e :: es' => diamonds es' ⋄ e
  end.

Lemma diamonds_witnessed {Γ : Type} (es : list (Eff Γ)) :
  Forall Witnessed es -> Witnessed (diamonds es).
Proof.
  induction 1; cbn.
  - apply witnessed_submonoid.
  - apply witnessed_submonoid; assumption.
Qed.

(** effect(eₙ) ⋄ ⋯ ⋄ effect(e₁) = effect(eₙ ⋄ ⋯ ⋄ e₁) *)
Lemma effect_diamonds {Γ : Type} (es : list (Eff Γ)) :
  diamonds (map effect es) = effect (diamonds es).
Proof.
  induction es as [|e es IH]; cbn.
  - symmetry; apply effect_eta.
  - rewrite IH; symmetry; apply effect_diamond.
Qed.

(** Starting from (γ₀, id), run effect(e₁), …, effect(eₙ). Writing
    (γₙ, g₁ ∘ ⋯ ∘ gₙ) for the state reached and Gₙ for the composite
    inverse:
    - the accumulator is the composite inverse of the effects themselves;
    - (g₁ ∘ ⋯ ∘ gₙ)(γₙ) = γ₀;
    - Gₙ(Δₙ) = (γ₀, g₁ ∘ ⋯ ∘ gₙ ∘ fₙ ∘ ⋯ ∘ f₁);
    - that accumulator again sends γ₀ to γ₀. *)
Theorem sequence_recovery {Γ : Type} (es : list (Eff Γ)) (γ0 : Γ) :
  Forall Witnessed es ->
  let E := diamonds es in
  let '((γn, acc), G) := diamonds (map effect es) (γ0, id) in
  γn = fst (E γ0) /\
  acc = snd (E γ0) /\
  acc γn = γ0 /\
  G (γn, acc) = (γ0, acc ∘ (fst ∘ E)) /\
  (acc ∘ (fst ∘ E)) γ0 = γ0.
Proof.
  intros Hs E.
  pose proof (diamonds_witnessed es Hs) as HE.
  pose proof (proj1 (witnessed_iff _) HE) as HE'.
  rewrite effect_diamonds.
  change (fst (E γ0) = fst (E γ0) /\
          id ∘ snd (E γ0) = snd (E γ0) /\
          (id ∘ snd (E γ0)) (fst (E γ0)) = γ0 /\
          track (snd (E γ0), fst ∘ E) (fst (E γ0), id ∘ snd (E γ0))
            = (γ0, id ∘ snd (E γ0) ∘ (fst ∘ E)) /\
          (id ∘ snd (E γ0) ∘ (fst ∘ E)) γ0 = γ0).
  repeat split.
  - exact (HE' γ0).
  - change ((snd (E γ0) (fst (E γ0)), id ∘ snd (E γ0) ∘ (fst ∘ E))
            = (γ0, id ∘ snd (E γ0) ∘ (fst ∘ E))).
    now rewrite HE'.
  - change (id (snd (E γ0) (fst (E γ0))) = γ0); unfold id; now rewrite HE'.
Qed.

(** ** Reverting in LIFO order (Theorem 16)
    Let e₀, …, eₙ₋₁ ∈ 𝔈*Γ be applied in order from (γ₀, id) through
    effect, and then reverted in the reverse order. Then
    1. each revert recovers the context state its application ran against;
    2. every intermediate state satisfies the soundness invariant.
    Indices are 0-based here: [xs i] is the state before eᵢ is applied, and
    [ys m] is the state after the last m inverses have run. *)
Section LIFO.
  Context {Γ : Type} (e : nat -> Eff Γ) (n : nat) (γ0 : Γ).
  Hypothesis Hw : forall i, i < n -> Witnessed (e i).

  Fixpoint xs (i : nat) : Dctx Γ :=
    match i with
    | 0 => (γ0, id)
    | S i' => fst (effect (e i') (xs i'))
    end.

  (** The inverse effect(eᵢ) returns where it is applied. *)
  Definition lifted_inv (i : nat) : End (Dctx Γ) := snd (effect (e i) (xs i)).

  Fixpoint ys (m : nat) : Dctx Γ :=
    match m with
    | 0 => xs n
    | S m' => lifted_inv (n - S m') (ys m')
    end.

  Theorem lifo_apply_sound : forall i, i <= n -> sound γ0 (xs i).
  Proof.
    induction i as [|i IH]; intros Hi.
    - reflexivity.
    - pose proof (proj1 (witnessed_iff _) (Hw i ltac:(lia))) as Hwi.
      specialize (IH ltac:(lia)); unfold sound in *.
      change (snd (xs i) (snd (e i (fst (xs i))) (fst (e i (fst (xs i)))))
              = γ0).
      rewrite Hwi; exact IH.
  Qed.

  Theorem lifo_revert :
    forall m, m <= n -> fst (ys m) = fst (xs (n - m)) /\ sound γ0 (ys m).
  Proof.
    induction m as [|m IH]; intros Hm.
    - rewrite PeanoNat.Nat.sub_0_r; split; [reflexivity|].
      apply lifo_apply_sound; lia.
    - destruct (IH ltac:(lia)) as [IH1 IH2].
      assert (Hi : n - m = S (n - S m)) by lia.
      rewrite Hi in IH1.
      set (i := n - S m) in *.
      pose proof (proj1 (witnessed_iff _) (Hw i ltac:(lia))) as Hwi.
      set (γ := fst (xs i)).
      assert (Hy : fst (ys m) = fst (e i γ)) by exact IH1.
      unfold sound in *.
      change (snd (e i γ) (fst (ys m)) = γ /\
              snd (ys m) (fst (e i (snd (e i γ) (fst (ys m))))) = γ0).
      rewrite Hy, Hwi; split; [reflexivity|].
      rewrite <- Hy; exact IH2.
  Qed.
End LIFO.
