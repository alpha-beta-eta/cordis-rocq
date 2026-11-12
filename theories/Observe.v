(** * Observational equivalence (§3.3.2: Definition 34, Lemma 35)

    An observer of a service state runs operations and reads their
    outcomes. A test is a word of letters: a forward letter runs an
    operation and records its outcome (the test is undefined where the
    operation fails); an inverse letter applies an inverse some operation
    may yield. Two states are indistinguishable ([Indist]) when every test
    gives the same result at both.

    An equivalence is admissible ([Admissible]) when every operation
    respects it: at related states an operation succeeds at both or at
    neither, with related successors and equal outcomes, and every inverse
    an operation may yield maps related states to related states.

    - [indist_admissible], [admissible_indist]: indistinguishability is the
      coarsest admissible equivalence (Lemma 35).
    - [wb_admissible]: the ≃ of a service whose operations are well behaved
      is admissible, so it is contained in indistinguishability.
    - [bus_no_commute]: on the ordered event bus with dispatch, no
      admissible equivalence lets two registrations of different callbacks
      commute. Dispatch reveals the order, so leaving dispatch out of the
      startup model ([Listeners]) is forced, not a choice. *)

From Stdlib Require Import RelationClasses List PeanoNat.
From Cordis Require Import Prelude Service EventBus.
Import ListNotations.

Section Observe.
  Context {Σ : Service}.
  Local Notation S := (St Σ).

  Inductive Letter : Type :=
  | LF (a : Op Σ) (t : nat)
  | LI (g : S -> S).

  (** Inverse letters must be inverses some operation may yield. *)
  Definition ValidTest (w : list Letter) : Prop :=
    forall g, In (LI g) w -> exists a t, yields (Σ := Σ) a t g.

  Fixpoint runTest (w : list Letter) (s : S) : option (list (Out Σ)) :=
    match w with
    | [] => Some []
    | LF a t :: w' =>
        match run a t s with
        | Some (s', _, o) => option_map (cons o) (runTest w' s')
        | None => None
        end
    | LI g :: w' => runTest w' (g s)
    end.

  Definition Indist (s s' : S) : Prop := forall w, ValidTest w -> runTest w s = runTest w s'.

  Definition Admissible (R : S -> S -> Prop) : Prop :=
    (forall a t s s', R s s' ->
       match run a t s, run a t s' with
       | None, None => True
       | Some (x, _, o), Some (x', _, o') => R x x' /\ o = o'
       | _, _ => False
       end) /\
    (forall a t g, yields (Σ := Σ) a t g -> forall s s', R s s' -> R (g s) (g s')).

  #[local] Instance indist_equiv : Equivalence Indist.
  Proof.
    split.
    - intros s w _; reflexivity.
    - intros s s' H w Hw; symmetry; exact (H w Hw).
    - intros s1 s2 s3 H1 H2 w Hw; rewrite (H1 w Hw); exact (H2 w Hw).
  Qed.

  Lemma valid_cons l w : ValidTest (l :: w) -> ValidTest w.
  Proof. intros H g Hg; exact (H g (or_intror Hg)). Qed.

  (** Every admissible relation is contained in indistinguishability. *)
  Theorem admissible_indist R : Admissible R -> forall s s', R s s' -> Indist s s'.
  Proof.
    intros [Hop Hinv] s s' H w Hw; revert s s' H.
    induction w as [|[a t|g] w IH]; intros s s' H; cbn; [reflexivity| |].
    - pose proof (Hop a t s s' H) as Ha.
      destruct (run a t s) as [[[x g] o]|], (run a t s') as [[[x' g'] o']|]; try contradiction; [|reflexivity].
      destruct Ha as [Hx <-]; rewrite (IH (valid_cons _ _ Hw) x x' Hx); reflexivity.
    - destruct (Hw g (or_introl eq_refl)) as (a & t & Hy).
      exact (IH (valid_cons _ _ Hw) (g s) (g s') (Hinv a t g Hy s s' H)).
  Qed.

  (** Indistinguishability is itself admissible. *)
  Theorem indist_admissible : Admissible Indist.
  Proof.
    split.
    - intros a t s s' H.
      assert (V1 : ValidTest [LF a t]) by (intros g [E|[]]; discriminate).
      pose proof (H [LF a t] V1) as H1.
      cbn in H1.
      destruct (run a t s) as [[[x g] o]|] eqn:E, (run a t s') as [[[x' g'] o']|] eqn:E'; cbn in H1;
        try discriminate; [|exact I].
      injection H1 as <-; split; [|reflexivity].
      intros w Hw; pose proof (H (LF a t :: w)) as H2; cbn in H2; rewrite E, E' in H2.
      assert (Hw' : ValidTest (LF a t :: w)).
      { intros h [Eh|Hh]; [discriminate | exact (Hw h Hh)]. }
      specialize (H2 Hw'); destruct (runTest w x), (runTest w x'); cbn in H2; congruence.
    - intros a t g Hy s s' H w Hw.
      assert (Hw' : ValidTest (LI g :: w)).
      { intros h [Eh|Hh]; [injection Eh as <-; exists a, t; exact Hy | exact (Hw h Hh)]. }
      exact (H (LI g :: w) Hw').
  Qed.

  (** The ≃ of a service whose operations are well behaved is admissible. *)
  Theorem wb_admissible : (forall a t, WellBehaved (Σ := Σ) a t) -> Admissible (@st_eq Σ).
  Proof.
    intros W; split.
    - intros a t s s' H; pose proof (wb_respects a t (W a t) s s' H) as R.
      destruct (run a t s) as [[[x g] o]|], (run a t s') as [[[x' g'] o']|]; cbn in R; try contradiction; [|exact I].
      destruct R as (Hx & _ & Ho); split; [exact Hx | exact Ho].
    - intros a t g (s0 & s0' & o & Hr) s s' H; exact (wb_inv a t (W a t) s0 s0' g o Hr s s' H).
  Qed.

  Corollary wb_indist : (forall a t, WellBehaved (Σ := Σ) a t) -> forall s s', s ≃ s' -> Indist s s'.
  Proof. intros W; exact (admissible_indist _ (wb_admissible W)). Qed.
End Observe.

(** ** Dispatch reveals the order of registrations *)
Section Bus.
  Context (Cb : Type) (cb_eq_dec : forall x y : Cb, {x = y} + {x <> y}).
  Local Notation Bus := (EventBus Cb cb_eq_dec).

  (** Whatever equivalence on hook lists every operation respects, two
      registrations of different callbacks under fresh tokens do not
      commute up to it. *)
  Theorem bus_no_commute (R : list (Tok * Cb) -> list (Tok * Cb) -> Prop) cb1 cb2 t1 t2 :
    Admissible (Σ := Bus) R -> cb1 <> cb2 -> t1 <> t2 ->
    ~ R [(t1, cb1); (t2, cb2)] [(t2, cb2); (t1, cb1)].
  Proof.
    intros A Hne Ht HR.
    pose proof (admissible_indist (Σ := Bus) R A _ _ HR [@LF Bus (Emit Cb) 0]) as H.
    assert (Hv : ValidTest (Σ := Bus) [@LF Bus (Emit Cb) 0]).
    { intros g [E|[]]; discriminate. }
    specialize (H Hv); cbn in H; injection H as H; congruence.
  Qed.
End Bus.
