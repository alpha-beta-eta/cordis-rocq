(** * Twisted composition, effect context, track, recover *)

From Stdlib Require Import List.
From Cordis Require Import Prelude.
Import ListNotations.

(** ** 𝔗Γ := (Γ → Γ) × (Γ → Γ) *)
Definition Twisted (Γ : Type) : Type := (End Γ * End Γ)%type.

(** (f₁, g₁) ∘ (f₂, g₂) := (f₁ ∘ f₂, g₂ ∘ g₁) *)
Definition tcomp {Γ : Type} (p q : Twisted Γ) : Twisted Γ :=
  (fst p ∘ fst q, snd q ∘ snd p).

Definition tunit {Γ : Type} : Twisted Γ := (id, id).

(** 𝔗Γ is a monoid with unit (id, id). *)
Lemma twisted_monoid (Γ : Type) : IsMonoid (@tcomp Γ) tunit.
Proof.
  split.
  - reflexivity.
  - intros [f g]; reflexivity.
  - intros [f g]; reflexivity.
Qed.

(** ** ∂Γ := Γ × (Γ → Γ) *)
Definition Dctx (Γ : Type) : Type := (Γ * End Γ)%type.

(** ** track : 𝔗Γ → End(∂Γ), track(f, g)(γ, φ) := (f γ, φ ∘ g) *)
Definition track {Γ : Type} (p : Twisted Γ) : End (Dctx Γ) :=
  fun x => (fst p (fst x), snd x ∘ snd p).

(** track is a monoid homomorphism. *)
Theorem track_hom (Γ : Type) :
  IsMonoidHom (@tcomp Γ) tunit comp id (@track Γ).
Proof.
  split.
  - extensionality x; destruct x; reflexivity.
  - reflexivity.
Qed.

(** pr₁ ∘ track(f, g) = f ∘ pr₁ *)
Theorem track_fst {Γ : Type} (p : Twisted Γ) : fst ∘ track p = fst p ∘ fst.
Proof. reflexivity. Qed.

(** ** recover : End(∂Γ), recover(γ, φ) := (φ γ, id) *)
Definition recover {Γ : Type} : End (Dctx Γ) :=
  fun x => (snd x (fst x), id).

(** Pointwise form (the paper's Theorem 7): it is enough that g reverts f
    at the state where it is applied. *)
Theorem recover_track_at {Γ : Type} (f g : End Γ) (γ : Γ) (φ : End Γ) :
  g (f γ) = γ -> recover (track (f, g) (γ, φ)) = recover (γ, φ).
Proof.
  intros H; change ((φ (g (f γ)), id) = (φ γ, @id Γ)); now rewrite H.
Qed.

(** The form in the notes: if g ∘ f = id then recover ∘ track(f, g) = recover. *)
Theorem recover_track {Γ : Type} (f g : End Γ) :
  g ∘ f = id -> recover ∘ track (f, g) = recover.
Proof.
  intros H; extensionality x; destruct x as [γ φ].
  exact (recover_track_at f g γ φ (equal_f H γ)).
Qed.

(** ** Sequences of tracked pairs (the paper's equation (11))
    A list [p₁; …; pₙ] is applied head first:
    tracks [p₁; …; pₙ] = track(pₙ) ∘ ⋯ ∘ track(p₁). *)
Fixpoint tracks {Γ : Type} (ps : list (Twisted Γ)) : End (Dctx Γ) :=
  match ps with
  | [] => id
  | p :: ps' => tracks ps' ∘ track p
  end.

(** By Theorem 5, the composite is the track of the twisted composite
    (fₙ ∘ ⋯ ∘ f₁, g₁ ∘ ⋯ ∘ gₙ). *)
Fixpoint tcomps {Γ : Type} (ps : list (Twisted Γ)) : Twisted Γ :=
  match ps with
  | [] => tunit
  | p :: ps' => tcomp (tcomps ps') p
  end.

Lemma tracks_tcomps {Γ : Type} (ps : list (Twisted Γ)) :
  tracks ps = track (tcomps ps).
Proof.
  induction ps as [|p ps IH]; cbn [tracks tcomps].
  - symmetry; apply (hom_unit _ _ _ _ _ (track_hom Γ)).
  - rewrite IH; symmetry; apply (hom_mul _ _ _ _ _ (track_hom Γ)).
Qed.

(** δ₀ = γ, δᵢ = fᵢ(δᵢ₋₁), and gᵢ(δᵢ) = δᵢ₋₁ for every i. *)
Fixpoint reverts_along {Γ : Type} (ps : list (Twisted Γ)) (γ : Γ) : Prop :=
  match ps with
  | [] => True
  | p :: ps' => snd p (fst p γ) = γ /\ reverts_along ps' (fst p γ)
  end.

(** Equation (11). *)
Theorem recover_tracks {Γ : Type} (ps : list (Twisted Γ)) (γ : Γ) (φ : End Γ) :
  reverts_along ps γ -> recover (tracks ps (γ, φ)) = recover (γ, φ).
Proof.
  revert γ φ; induction ps as [|[f g] ps IH]; intros γ φ H.
  - reflexivity.
  - destruct H as [H1 H2].
    change (recover (tracks ps (f γ, φ ∘ g)) = recover (γ, φ)).
    rewrite (IH _ _ H2).
    exact (recover_track_at f g γ φ H1).
Qed.

(** From the initial effect context (γ₀, id), recovery returns to it. *)
Corollary recover_tracks_init {Γ : Type} (ps : list (Twisted Γ)) (γ0 : Γ) :
  reverts_along ps γ0 -> recover (tracks ps (γ0, id)) = (γ0, id).
Proof. intros H; exact (recover_tracks ps γ0 id H). Qed.

(** A pair with g ∘ f = id meets the hypothesis at every state. *)
Lemma reverts_along_global {Γ : Type} (ps : list (Twisted Γ)) (γ : Γ) :
  Forall (fun p => snd p ∘ fst p = id) ps -> reverts_along ps γ.
Proof.
  intros H; revert γ; induction H as [|p ps Hp _ IH]; intros γ; cbn.
  - exact I.
  - split; [exact (equal_f Hp γ) | apply IH].
Qed.

(** ** The soundness invariant φ(γ) = γ₀ of a state (γ, φ) ∈ ∂Γ *)
Definition sound {Γ : Type} (γ0 : Γ) (x : Dctx Γ) : Prop := snd x (fst x) = γ0.

Lemma sound_recover {Γ : Type} (γ0 : Γ) (x : Dctx Γ) :
  sound γ0 x <-> recover x = (γ0, id).
Proof.
  unfold sound, recover; split.
  - intros ->; reflexivity.
  - intros H; apply (f_equal fst) in H; exact H.
Qed.

(** Tracking a pair that reverts at the current state preserves soundness. *)
Lemma track_sound {Γ : Type} (γ0 : Γ) (f g : End Γ) (x : Dctx Γ) :
  g (f (fst x)) = fst x -> sound γ0 x -> sound γ0 (track (f, g) x).
Proof.
  destruct x as [γ φ]; unfold sound; cbn; intros H1 H2.
  change (φ (g (f γ)) = γ0); now rewrite H1.
Qed.
