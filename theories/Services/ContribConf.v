(** * Contribution keys under the recovery and confluence theorems
      (docs/CONTRIB.md, stage E6b)

    - Confluent tier: contribution keys meet [ConfHyps] for the relation
      [contrib_meet], which allows any two contributions and any two reads
      but not a contribution beside a read ([contrib_hyps]). The excluded
      pair is exactly the one [contribute_read_not_commute] rules out. A
      startup program that never reads a contribution key covers the
      relation ([covers_no_read]), whatever names it contributes: two
      fibers contributing the same name is no longer an obstacle.
    - Revertible tier: the recovery theorem asks revert-independence at
      every state, not only after the operation ran. Removing one copy of
      [e] from a state without [e] is not undone by adding it, so two
      equal contributions are not revert-independent at such states. The
      relation [contrib_rev] therefore asks distinct entries
      ([contrib_revertible]); tagging by component (stage E6d) makes the
      entries of two components distinct.
    - The corollaries read the summary theorem through [resolve]: two
      orchestrated runs that end quiet with no failure resolve every name
      alike on every key bound in both ([contrib_confluence]), and so does
      static assembly ([contrib_static]); after a fiber is gone, every
      name resolves as in the shadow execution without it
      ([contrib_recovery]). *)

From Stdlib Require Import RelationClasses List PeanoNat Bool Permutation.
From Cordis Require Import Prelude Service ServiceSeq Calculus Recovery Compose
  Confluence SpawnConf Dynamic Summary Listeners Contrib.
Import ListNotations.

Section ContribConf.
  Context (Tag Name V : Type).
  Context (tag_eq_dec : forall x y : Tag, {x = y} + {x <> y}).
  Context (name_eq_dec : forall x y : Name, {x = y} + {x <> y}).
  Context (v_eq_dec : forall x y : V, {x = y} + {x <> y}).
  Context (public : Name -> bool) (prio : V -> nat).

  Local Notation CS := (Contrib Tag Name V tag_eq_dec name_eq_dec v_eq_dec public prio).
  Local Notation Entry := (Entry Tag Name V).
  Local Notation edec := (entry_eq_dec Tag Name V tag_eq_dec name_eq_dec v_eq_dec).
  Local Notation rf := (remove_first Entry edec).
  Local Notation resolve := (resolve Tag Name V tag_eq_dec name_eq_dec v_eq_dec public prio).

  (** ** The meeting relations *)
  Definition contrib_meet (a b : Op CS) : Prop :=
    match a, b with
    | Contribute _, Read _ _ | Read _ _, Contribute _ => False
    | _, _ => True
    end.

  Definition contrib_rev (a b : Op CS) : Prop :=
    match a, b with
    | Contribute e, Contribute e' => e <> e'
    | Contribute _, Read _ _ | Read _ _, Contribute _ => False
    | _, _ => True
    end.

  Lemma rev_meet a b : contrib_rev a b -> contrib_meet a b.
  Proof. destruct a, b; cbn; tauto. Qed.

  (** ** Confluent tier *)

  (** Operations only add entries: after [Contribute e], [e] stays. *)
  Lemma after_in (Good : Op CS -> Prop) e ta x :
    After (Σ := CS) Good (Contribute e) ta x -> In e x.
  Proof.
    intros H; induction H as [x x' g o Hr|w b tb w' h o Hw IH Gb Ht Hr].
    - cbn in Hr; injection Hr as <- _ _; left; reflexivity.
    - destruct b as [e'|q y]; cbn in Hr; injection Hr as <- _ _; [right|]; exact IH.
  Qed.

  Lemma inv_of_contribute e t g : yields (Σ := CS) (Contribute e) t g -> g = rf e.
  Proof. intros (s & s' & o & H); cbn in H; injection H as _ <- _; reflexivity. Qed.

  Lemma inv_of_read q x t g : yields (Σ := CS) (Read q x) t g -> g = fun s => s.
  Proof. intros (s & s' & o & H); cbn in H; injection H as _ <- _; reflexivity. Qed.

  Lemma contrib_revert_after : RevAfter CS contrib_meet.
  Proof.
    intros a b ta tb g Hab _ Hy x Hx.
    destruct a as [e|q y].
    - rewrite (inv_of_contribute e ta g Hy).
      destruct b as [e'|q y]; cbn in Hab; [|contradiction].
      pose proof (after_in _ e ta x Hx) as Hin; cbn.
      split; [symmetry; exact (rf_cons_in _ edec e e' x Hin) | split; [intros z; reflexivity | reflexivity]].
    - rewrite (inv_of_read q y ta g Hy).
      destruct b as [e'|q' y']; cbn; (split; [reflexivity | split; [intros z; reflexivity | reflexivity]]).
  Qed.

  Lemma contrib_com : ComG CS contrib_meet.
  Proof.
    intros a b ta tb Hab _.
    destruct a as [e|q x], b as [e'|q' x']; cbn in Hab; try contradiction.
    - apply contribute_commute.
    - apply read_commute.
  Qed.

  Theorem contrib_hyps : ConfHyps CS contrib_meet.
  Proof.
    split.
    - exact (contrib_well_behaved Tag Name V tag_eq_dec name_eq_dec v_eq_dec public prio).
    - exact (contrib_inverse_uniform Tag Name V tag_eq_dec name_eq_dec v_eq_dec public prio).
    - exact (contrib_token_irrelevant Tag Name V tag_eq_dec name_eq_dec v_eq_dec public prio).
    - exact contrib_revert_after.
    - exact contrib_com.
  Qed.

  (** ** Revertible tier *)
  Lemma rf_skip y e x : y <> e -> rf e (y :: x) = y :: rf e x.
  Proof. intros H; cbn; destruct (edec y e); [contradiction | reflexivity]. Qed.

  Lemma rf_comm e e' x : rf e (rf e' x) = rf e' (rf e x).
  Proof.
    induction x as [|y x IH]; [reflexivity|].
    destruct (edec y e') as [Ey'|Ny'], (edec y e) as [Ey|Ny].
    - subst y e'; reflexivity.
    - subst y; rewrite (rf_skip e' e x Ny), !rf_head; reflexivity.
    - subst y; rewrite (rf_skip e e' x Ny'), !rf_head; reflexivity.
    - rewrite (rf_skip y e' x Ny'), (rf_skip y e (rf e' x) Ny),
        (rf_skip y e x Ny), (rf_skip y e' (rf e x) Ny'), IH; reflexivity.
  Qed.

  Lemma contrib_revert_indep a b ta tb :
    contrib_rev a b -> RevertIndep (Σ := CS) a ta b tb.
  Proof.
    intros Hab g Hy.
    destruct a as [e|q y].
    - rewrite (inv_of_contribute e ta g Hy).
      destruct b as [e'|q y]; cbn in Hab; [|contradiction].
      split.
      + intros x; cbn [run Contrib crun shifted].
        rewrite (rf_skip e' e x (fun E => Hab (eq_sym E))).
        split; [reflexivity | split; [intros z; reflexivity | reflexivity]].
      + intros h x Hh; rewrite (inv_of_contribute e' tb h Hh); cbn.
        rewrite rf_comm; reflexivity.
    - rewrite (inv_of_read q y ta g Hy); split.
      + intros x; destruct b as [e'|q' y']; cbn;
          (split; [reflexivity | split; [intros z; reflexivity | reflexivity]]).
      + intros h x _; reflexivity.
  Qed.

  Theorem contrib_revertible : Revertible CS contrib_rev.
  Proof.
    split.
    - exact (contrib_well_behaved Tag Name V tag_eq_dec name_eq_dec v_eq_dec public prio).
    - intros a b ta tb Hab _; exact (contrib_revert_indep a b ta tb Hab).
  Qed.

  (** ** Coverage: startup programs that never read *)
  Section Cover.
    Context {K : Type} {C : Type} (prog : C -> @Component K CS C).

    Lemma covers_no_read :
      (forall c k q x, ~ OpAt CS k (Read q x) (body CS (prog c))) ->
      Covers CS prog contrib_meet.
    Proof.
      intros NR k a b (c & c' & Ha & Hb & _).
      destruct a as [e|q x]; [|exfalso; exact (NR c k q x Ha)].
      destruct b as [e'|q x]; [exact I | exfalso; exact (NR c' k q x Hb)].
    Qed.

    (** For recovery, two fibers must not contribute the same entry. *)
    Lemma covers_rev_no_read :
      (forall c k q x, ~ OpAt CS k (Read q x) (body CS (prog c))) ->
      (forall k e, ~ CoPair CS prog k (Contribute e) (Contribute e)) ->
      Covers CS prog contrib_rev.
    Proof.
      intros NR ND k a b Hab.
      destruct Hab as (c & c' & Ha & Hb & Hp) eqn:Hcp.
      destruct a as [e|q x]; [|exfalso; exact (NR c k q x Ha)].
      destruct b as [e'|q x]; [|exfalso; exact (NR c' k q x Hb)].
      cbn; intros ->; exact (ND k e' (ex_intro _ c (ex_intro _ c' (conj Ha (conj Hb Hp))))).
    Qed.
  End Cover.

  (** ** Corollaries of the summary theorem *)
  Section Summaries.
    Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
    Context {C : Type} (prog : C -> @Component K CS C).

    Lemma agree_resolve l1 l2 (γ1 γ2 : @State K CS C) :
      AgreeL CS l1 l2 γ1 γ2 ->
      forall k b1 b2, binds CS γ1 k = Some b1 -> binds CS γ2 k = Some b2 ->
        forall q x, resolve (bst CS b1) q x = resolve (bst CS b2) q x.
    Proof.
      intros A k b1 b2 H1 H2 q x.
      apply resolve_perm.
      destruct A as (_ & _ & _ & _ & _ & _ & _ & _ & St); exact (St k b1 b2 H1 H2).
    Qed.

    Theorem contrib_confluence Kb rank Rb ins (γ1 γ2 : @State K CS C) rs1 rs2 :
      Covers CS prog contrib_meet -> Obligations CS prog Kb rank Rb -> TotalProv CS prog ->
      DRun K_eq_dec CS prog (@init K CS C) [] ins γ1 rs1 ->
      DRun K_eq_dec CS prog (@init K CS C) [] ins γ2 rs2 ->
      quiet K_eq_dec CS prog γ1 -> quiet K_eq_dec CS prog γ2 -> NoFailed CS γ1 -> NoFailed CS γ2 ->
      forall k b1 b2, binds CS γ1 k = Some b1 -> binds CS γ2 k = Some b2 ->
        forall q x, resolve (bst CS b1) q x = resolve (bst CS b2) q x.
    Proof.
      intros HG HO HT R1 R2 Q1 Q2 N1 N2.
      exact (agree_resolve _ _ γ1 γ2
               (summary_confluence K_eq_dec CS prog contrib_meet Kb rank Rb ins γ1 γ2 rs1 rs2
                  contrib_hyps HG HO HT R1 R2 Q1 Q2 N1 N2)).
    Qed.

    Theorem contrib_static Kb rank Rb ins (γ γs : @State K CS C) rs rss :
      Covers CS prog contrib_meet -> Obligations CS prog Kb rank Rb -> TotalProv CS prog ->
      DRun K_eq_dec CS prog (@init K CS C) [] ins γ rs ->
      DRun K_eq_dec CS prog (@init K CS C) [] (map IIns (scomps ins)) γs rss ->
      quiet K_eq_dec CS prog γ -> quiet K_eq_dec CS prog γs -> NoFailed CS γ -> NoFailed CS γs ->
      forall k b bs, binds CS γ k = Some b -> binds CS γs k = Some bs ->
        forall q x, resolve (bst CS b) q x = resolve (bst CS bs) q x.
    Proof.
      intros HG HO HT R1 R2 Q1 Q2 N1 N2.
      exact (agree_resolve _ _ γ γs
               (summary_static K_eq_dec CS prog contrib_meet Kb rank Rb ins γ γs rs rss
                  contrib_hyps HG HO HT R1 R2 Q1 Q2 N1 N2)).
    Qed.

    Theorem contrib_recovery n ls (γ : @State K CS C) σ :
      Covers CS prog contrib_rev ->
      shadow_run K_eq_dec CS prog n (@init K CS C) ls (fun _ => None) = Some (γ, σ) ->
      match fibers CS γ n with Some f => is_installed CS (life CS f) = false | None => True end ->
      forall k, match binds CS γ k, σ k with
                | Some b, Some s => forall q x, resolve (bst CS b) q x = resolve s q x
                | None, None => True
                | _, _ => False
                end.
    Proof.
      intros HG HS Hn k.
      pose proof (summary_recovery K_eq_dec CS prog contrib_rev n ls γ σ
                    contrib_revertible HG HS Hn k) as H.
      destruct (binds CS γ k), (σ k); try exact H.
      intros q x; apply resolve_perm; exact H.
    Qed.
  End Summaries.
End ContribConf.
