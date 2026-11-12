(** * Service specifications (R1)

    A service is a state type with an equivalence ≃, a type of operations
    (arguments included), a type of outcomes, and the operations' semantics.
    Running an operation receives a fresh token from the runtime (used for
    generative identities such as event hooks) and either fails or yields a
    successor state, an inverse and an outcome. *)

From Stdlib Require Import RelationClasses Morphisms List.
From Cordis Require Import Prelude.
Import ListNotations.

Notation Tok := nat (only parsing).

Record Service := {
  St : Type;
  st_eq : St -> St -> Prop;
  st_eq_equiv : Equivalence st_eq;
  Op : Type;
  Out : Type;
  run : Op -> Tok -> St -> option (St * (St -> St) * Out)
}.
#[export] Existing Instance st_eq_equiv.

Arguments st_eq {_} _ _.
Arguments run {_} _ _ _.
Notation "x ≃ y" := (st_eq x y) (at level 70, no associativity).

Section Spec.
  Context {Σ : Service}.

  (** Inverses are compared pointwise. *)
  Definition fun_eq (g h : St Σ -> St Σ) : Prop := forall x, g x ≃ h x.

  Definition respects (g : St Σ -> St Σ) : Prop :=
    forall x y, x ≃ y -> g x ≃ g y.

  (** Two results of an operation are related: both fail, or both succeed
      with related successors, pointwise related inverses, equal outcomes. *)
  Definition res_eq (r1 r2 : option (St Σ * (St Σ -> St Σ) * Out Σ)) : Prop :=
    match r1, r2 with
    | None, None => True
    | Some (s1, g1, o1), Some (s2, g2, o2) => s1 ≃ s2 /\ fun_eq g1 g2 /\ o1 = o2
    | _, _ => False
    end.

  (** ** Well-behaved operations (the paper's Definition 24) *)

  (** The inverse reverts the operation where it was applied. *)
  Definition Witnessed (a : Op Σ) (t : Tok) : Prop :=
    forall s s' g o, run a t s = Some (s', g, o) -> g s' ≃ s.

  (** The operation respects ≃. *)
  Definition Respects (a : Op Σ) (t : Tok) : Prop :=
    forall s1 s2, s1 ≃ s2 -> res_eq (run a t s1) (run a t s2).

  (** Every inverse the operation yields respects ≃. *)
  Definition InvRespects (a : Op Σ) (t : Tok) : Prop :=
    forall s s' g o, run a t s = Some (s', g, o) -> respects g.

  Record WellBehaved (a : Op Σ) (t : Tok) : Prop := {
    wb_witness : Witnessed a t;
    wb_respects : Respects a t;
    wb_inv : InvRespects a t
  }.

  (** The inverses an operation may yield. *)
  Definition yields (a : Op Σ) (t : Tok) (g : St Σ -> St Σ) : Prop :=
    exists s s' o, run a t s = Some (s', g, o).

  (** ** Revert-independence

      [RevertIndep a ta b tb]: every inverse g that a may yield can be run
      after b without disturbing b:
      1. b fails at g x iff it fails at x; where it succeeds, its successor
         at g x is g applied to its successor at x, it yields a pointwise
         equal inverse and the same outcome;
      2. g commutes with every inverse b may yield.

      This is what withdrawing a's effect while b's stays in place needs.
      It does not ask the forward maps of a and b to commute. *)
  Definition shifted (g : St Σ -> St Σ)
      (r r' : option (St Σ * (St Σ -> St Σ) * Out Σ)) : Prop :=
    match r, r' with
    | None, None => True
    | Some (x1, h, o), Some (x2, h', o') => x2 ≃ g x1 /\ fun_eq h' h /\ o' = o
    | _, _ => False
    end.

  (** [shifted], for an operation that succeeds at the first state. *)
  Definition shifted_ok (g : St Σ -> St Σ)
      (r r' : option (St Σ * (St Σ -> St Σ) * Out Σ)) : Prop :=
    match r with
    | Some (x1, h, o) =>
        match r' with
        | Some (x2, h', o') => x2 ≃ g x1 /\ fun_eq h' h /\ o' = o
        | None => False
        end
    | None => True
    end.

  Lemma shifted_ok_of g r r' : shifted g r r' -> shifted_ok g r r'.
  Proof. destruct r as [[[x1 h] o]|], r' as [[[x2 h'] o']|]; cbn; tauto. Qed.

  Definition RevertIndep (a : Op Σ) (ta : Tok) (b : Op Σ) (tb : Tok) : Prop :=
    forall g, yields a ta g ->
      (forall x, shifted g (run b tb x) (run b tb (g x))) /\
      (forall h x, yields b tb h -> g (h x) ≃ h (g x)).

  (** ** Commutation of forward maps

      Running a then b and running b then a agree: both fail, or both
      succeed with related final states and the same outcomes. This is what
      reordering activations (confluence) needs, on top of revert-
      independence. *)
  Definition seq2 (a : Op Σ) (ta : Tok) (b : Op Σ) (tb : Tok) (s : St Σ)
    : option (St Σ * Out Σ * Out Σ) :=
    match run a ta s with
    | Some (s1, _, oa) =>
        match run b tb s1 with
        | Some (s2, _, ob) => Some (s2, oa, ob)
        | None => None
        end
    | None => None
    end.

  Definition Commute (a : Op Σ) (ta : Tok) (b : Op Σ) (tb : Tok) : Prop :=
    forall s,
      match seq2 a ta b tb s, seq2 b tb a ta s with
      | None, None => True
      | Some (s1, oa, ob), Some (s2, ob', oa') => s1 ≃ s2 /\ oa = oa' /\ ob = ob'
      | _, _ => False
      end.

  (** ** Omission on one service

      An operation a runs at s₀, then a sequence of foreign steps runs:
      foreign operations, and foreign inverses. Running a's inverse at the
      end gives, up to ≃, the state the same steps reach from s₀, and the
      foreign operations see the same outcomes. *)
  Inductive Step : Type :=
  | DoOp (b : Op Σ) (t : Tok)
  | DoInv (h : St Σ -> St Σ).

  (** A failing operation leaves the state as it is. *)
  Fixpoint exec (ts : list Step) (s : St Σ) : St Σ * list (option (Out Σ)) :=
    match ts with
    | [] => (s, [])
    | DoOp b t :: ts' =>
        match run b t s with
        | Some (s', _, o) => let r := exec ts' s' in (fst r, Some o :: snd r)
        | None => let r := exec ts' s in (fst r, None :: snd r)
        end
    | DoInv h :: ts' => exec ts' (h s)
    end.

  (** What a foreign step must satisfy relative to the inverse g. *)
  Definition admissible (g : St Σ -> St Σ) (st : Step) : Prop :=
    match st with
    | DoOp b t =>
        Respects b t /\ forall x, shifted g (run b t x) (run b t (g x))
    | DoInv h => respects h /\ forall x, g (h x) ≃ h (g x)
    end.

  Lemma exec_shift (g : St Σ -> St Σ) (ts : list Step) :
    Forall (admissible g) ts ->
    forall x y, g x ≃ y ->
      g (fst (exec ts x)) ≃ fst (exec ts y) /\ snd (exec ts x) = snd (exec ts y).
  Proof.
    induction 1 as [|st ts Hst Hts IH]; intros x y Hxy.
    - split; [exact Hxy | reflexivity].
    - destruct st as [b t | h]; cbn [exec].
      + destruct Hst as [Hresp Hsh].
        specialize (Hsh x).
        pose proof (Hresp (g x) y Hxy) as Hr.
        destruct (run b t x) as [[[x1 h1] o1]|] eqn:E1;
          destruct (run b t (g x)) as [[[x2 h2] o2]|] eqn:E2;
          cbn in Hsh; try contradiction.
        * destruct (run b t y) as [[[y1 k1] p1]|] eqn:E3; cbn in Hr; [|contradiction].
          destruct Hsh as [Hx2 [_ Ho2]]; destruct Hr as [Hy1 [_ Hp1]].
          destruct (IH x1 y1) as [IH1 IH2].
          { transitivity x2; [symmetry; exact Hx2 | exact Hy1]. }
          cbn [fst snd]; split; [exact IH1|].
          rewrite IH2; congruence.
        * destruct (run b t y) as [[[y1 k1] p1]|] eqn:E3; cbn in Hr; [contradiction|].
          destruct (IH x y Hxy) as [IH1 IH2].
          cbn [fst snd]; split; [exact IH1 | rewrite IH2; reflexivity].
      + destruct Hst as [Hh Hc].
        apply IH.
        transitivity (h (g x)); [apply Hc | apply Hh; exact Hxy].
  Qed.

  Theorem omission (a : Op Σ) (ta : Tok) (s0 s1 : St Σ) g o (ts : list Step) :
    Witnessed a ta ->
    run a ta s0 = Some (s1, g, o) ->
    Forall (admissible g) ts ->
    g (fst (exec ts s1)) ≃ fst (exec ts s0) /\ snd (exec ts s1) = snd (exec ts s0).
  Proof.
    intros Hw Hrun Hts.
    apply exec_shift; [exact Hts|].
    exact (Hw _ _ _ _ Hrun).
  Qed.

  (** Revert-independence makes every foreign operation admissible, and
      every inverse it may yield as well. *)
  Lemma revert_indep_admissible a ta b tb g :
    RevertIndep a ta b tb -> Respects b tb -> yields a ta g ->
    admissible g (DoOp b tb) /\
    (forall h, yields b tb h -> respects h -> admissible g (DoInv h)).
  Proof.
    intros HRI Hresp Hy.
    destruct (HRI g Hy) as [H1 H2]; split.
    - split; [exact Hresp | exact H1].
    - intros h Hyh Hh; split; [exact Hh|].
      intros x; exact (H2 h x Hyh).
  Qed.
End Spec.

Arguments Step : clear implicits.
