(** * Ideal failure (errors/DESIGN.md, section 3, layer 2)

    An ideal trace ([Episode.Tr]) runs a component's program on its own,
    answering each operation from the initial state of the provision it
    resolves to, plus the trace's own earlier operations there. A program
    fails ideally under [ρ] when one of its ideal traces stops at a failure
    point: [PFail], an operation whose key does not resolve, or an
    operation that the ideal state rejects.

    - [fail_no_step]: an ideal trace does not go past a failure point;
    - [ideal_excl]: no program both reaches [Done] and fails ideally under
      the same [ρ] (traces are determined, [Episode.tr_det]);
    - [ideal_fails_ext], [ideal_done_ext]: both depend on [ρ] only at the
      keys the component declares.

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering Progress
  Recovery Termination Confluence StateInv Episode.
Import ListNotations.

Section IdealFail.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).
  Hypothesis Hwb : forall a t, WellBehaved (Σ := Σ) a t.

  Local Notation Prog := (@Prog K Σ C).
  Local Notation S := (St Σ).
  Local Notation Ev := (@Ev K Σ C).
  Local Notation Tr := (Tr K_eq_dec Σ prog).
  Local Notation resolveI := (resolveI K_eq_dec Σ prog).
  Local Notation ownIt := (ownIt K_eq_dec Σ).
  Local Notation cdeps c := (deps Σ (prog c)).

  Definition FailPt (c : C) (ρ : K -> option S) (evs : list Ev) (P : Prog) : Prop :=
    match P with
    | PFail => True
    | POp k a _ =>
        resolveI c ρ evs k = None \/
        exists s0 s1, resolveI c ρ evs k = Some s0 /\ Replay (ownIt k evs) s0 s1 /\ run a 0 s1 = None
    | _ => False
    end.

  Definition IdealFails (c : C) (ρ : K -> option S) : Prop :=
    exists evs P, Tr c ρ evs P /\ FailPt c ρ evs P.

  Definition IdealDone (c : C) (ρ : K -> option S) : Prop :=
    exists evs, Tr c ρ evs PDone.

  (** ** An ideal trace stops at a failure point *)
  Lemma fail_no_step c ρ evs P x Q :
    Tr c ρ evs P -> FailPt c ρ evs P -> Tr c ρ (x :: evs) Q -> False.
  Proof.
    intros T F T2.
    inversion T2 as [|e k a κ s0 s1 s' g o T3 R3 Rp3 X3|e k s P' T3|e c' P' T3]; subst;
      destruct (tr_det K_eq_dec Σ prog Hwb c ρ ρ evs evs P _ (fun _ _ => eq_refl) T T3 eq_refl)
        as [_ ->]; cbn in F; try contradiction.
    destruct F as [F|(s0' & s1' & F & Rp & X)]; [congruence|].
    rewrite R3 in F; injection F as <-.
    pose proof (replay_det _ _ _ _ Rp Rp3) as E.
    pose proof (wb_respects _ _ (Hwb a 0) s1' s1 E) as Hres; rewrite X, X3 in Hres; exact Hres.
  Qed.

  (** ** Reaching [Done] and failing ideally exclude each other *)
  Lemma ideal_excl c ρ : IdealDone c ρ -> IdealFails c ρ -> False.
  Proof.
    intros [e1 T1] (e2 & P & T2 & F).
    pose proof (tr_done_len K_eq_dec Σ prog Hwb c ρ ρ e1 e2 P (fun _ _ => eq_refl) T1 T2) as Hle.
    destruct (Nat.eq_dec (length e2) (length e1)) as [Heq|Hne].
    - destruct (tr_det K_eq_dec Σ prog Hwb c ρ ρ e1 e2 PDone P (fun _ _ => eq_refl) T1 T2
                  (eq_sym Heq)) as [_ <-].
      exact F.
    - set (d := length e1 - Datatypes.S (length e2)).
      assert (Hsk : length (skipn d e1) = Datatypes.S (length e2))
        by (rewrite length_skipn; unfold d; lia).
      rewrite <- (firstn_skipn d e1) in T1.
      destruct (skipn d e1) as [|x r] eqn:Es; [discriminate|]; cbn in Hsk; injection Hsk as Hsk.
      destruct (tr_drop K_eq_dec Σ prog c ρ _ _ _ T1) as (Q & T3).
      assert (Tr4 : exists P', Tr c ρ r P').
      { inversion T3; subst; eauto. }
      destruct Tr4 as (P' & T4).
      destruct (tr_det K_eq_dec Σ prog Hwb c ρ ρ r e2 P' P (fun _ _ => eq_refl) T4 T2 Hsk)
        as [-> _].
      exact (fail_no_step c ρ e2 P x Q T2 F T3).
  Qed.

  (** ** Only the declared keys of [ρ] matter *)
  Lemma resolveI_ext c ρ1 ρ2 evs k :
    (forall k, In k (cdeps c) -> ρ1 k = ρ2 k) -> resolveI c ρ1 evs k = resolveI c ρ2 evs k.
  Proof.
    intros E; unfold Episode.resolveI.
    destruct (kmem K_eq_dec k (cdeps c)) eqn:Hk; [|reflexivity].
    apply E, (kmem_In K_eq_dec k _ Hk).
  Qed.

  Lemma tr_ext_deps c ρ1 ρ2 evs P :
    (forall k, In k (cdeps c) -> ρ1 k = ρ2 k) -> Tr c ρ1 evs P -> Tr c ρ2 evs P.
  Proof.
    intros E H; induction H as [|evs k a κ s0 s1 s' g o T IH R Rp X|evs k s P T IH|evs c' P T IH].
    - constructor.
    - eapply tr_op; [exact IH | | exact Rp | exact X].
      rewrite <- (resolveI_ext c ρ1 ρ2 evs k E); exact R.
    - apply tr_prov; exact IH.
    - apply tr_spawn; exact IH.
  Qed.

  Lemma ideal_fails_ext c ρ1 ρ2 :
    (forall k, In k (cdeps c) -> ρ1 k = ρ2 k) -> IdealFails c ρ1 -> IdealFails c ρ2.
  Proof.
    intros E (evs & P & T & F); exists evs, P; split; [exact (tr_ext_deps c ρ1 ρ2 evs P E T)|].
    destruct P as [| |k a κ| |]; cbn in *; try exact F.
    rewrite <- (resolveI_ext c ρ1 ρ2 evs k E); exact F.
  Qed.

  Lemma ideal_done_ext c ρ1 ρ2 :
    (forall k, In k (cdeps c) -> ρ1 k = ρ2 k) -> IdealDone c ρ1 -> IdealDone c ρ2.
  Proof. intros E [evs T]; exists evs; exact (tr_ext_deps c ρ1 ρ2 evs PDone E T). Qed.
End IdealFail.
