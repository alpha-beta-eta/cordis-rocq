(** * Termination with failures scoped to their view (errors/DESIGN.md, section 1)

    [VClear] lets a failed fiber load again once its target has moved on,
    so the core measure, which counts a failed fiber as almost nothing, no
    longer decreases. [vmu] changes it in three places:

    - a failed Inactive fiber whose recorded view is no longer its target
      counts as one more than an Inactive fiber with that target (the
      [VClear] step, then a load or a removal);
    - an Unloading fiber with an error whose view is no longer its target
      counts its undo items, the final step, and the same;
    - a Loading fiber whose target has turned counts one more than in the
      core (it may now end failed and stale, one step longer than a divert).

    Everything else is the core's [Termination.mu]. The proof follows
    [Termination.v]: a step of [n] lowers [vmu] at [n] ([vmu_drop]), leaves
    fibers of rank at most that of [n] alone ([vmu_other]), and so lowers
    the measure lexicographically by rank ([vphi_drop]); [VClear] lowers it
    at [n] and touches nothing else. The core lemmas about targets, undo
    weights and ranks are reused as they are.

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Progress Recovery Termination.
From CordisErr Require Import ViewFail.
Import ListNotations.

Section VTermination.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Variable Kb : nat.
  Hypothesis HK : forall c, Bounded Σ Kb (body Σ (prog c)).
  Variable rank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', Above Σ prog c c' -> rank c < rank c'.
  Hypothesis Hbnd : forall c, rank c <= Rb.

  Local Notation State := (@State K Σ C).
  Local Notation Fiber := (@Fiber K Σ C).
  Local Notation Life := (@Life K Σ C).
  Local Notation View := (@View K).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation target := (Calculus.target Σ prog).
  Local Notation target_is := (target_is K_eq_dec Σ prog).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation frank f := (rank (fcomp f)).
  Local Notation TInv := (TInv K_eq_dec Σ prog Kb).
  Local Notation mu := (mu K_eq_dec Σ prog Kb).
  Local Notation muU := (muU Σ Kb).
  Local Notation Wt := (Wt Σ).
  Local Notation dflag := (dflag Σ).
  Local Notation Bm := (Bm Kb).
  Local Notation VState := (@VState K Σ C).
  Local Notation vstep := (vstep K_eq_dec Σ prog).
  Local Notation vcore := (ViewFail.vcore Σ).
  Local Notation fview := (ViewFail.fview Σ).

  (** ** The measure *)

  (** What a fiber with target [t] still owes once it is Inactive and not
      failed: a load, or (retired) a removal. *)
  Definition owe (f : Fiber) (t : option View) : nat :=
    match t with Some _ => Bm | None => dflag f end.

  Definition vmu (γ : State) (F : nat -> option View) (n : nat) (f : Fiber) : nat :=
    match life Σ f with
    | Inactive _ (Some _) =>
        match F n with
        | Some w => if target_is γ n w then dflag f else S (owe f (target γ n))
        | None => dflag f
        end
    | Loading _ _ acc w =>
        if target_is γ n w then 3 * Kb + 10 - length acc
        else S (2 * Kb + 1 + muU γ f [] None (target γ n) + (Kb - length acc))
    | Unloading _ acc w (Some e) =>
        if target_is γ n w then muU γ f acc (Some e) (target γ n)
        else Wt γ acc + 1 + S (owe f (target γ n))
    | _ => mu γ n f
    end.

  Lemma Wt_le' (γ : State) l : Wt γ l <= 2 * length l.
  Proof. apply (Wt_le Σ). Qed.

  (** ** The measure of [n] drops at a lifecycle step of [n] *)
  Lemma vmu_drop (γ γ' : State) (F : nat -> option View) (n : nat) ℓ (fn : Fiber) :
    TInv γ -> In ℓ (lifecycle_labels n) -> step γ ℓ = Some γ' -> fibers Σ γ n = Some fn ->
    let F' := match ℓ with
              | LUnloaded n0 => vupd F n0 (unloading_view Σ γ n0)
              | _ => F
              end in
    match fibers Σ γ' n with Some fn' => vmu γ' F' n fn' | None => 0 end < vmu γ F n fn.
  Proof.
    intros I Hin H Hn F'.
    pose proof (lstep_effects K_eq_dec Σ prog Kb rank Hrank γ γ' n ℓ fn I Hin H Hn) as EF.
    pose proof EF as (_ & _ & E3 & _ & _).
    assert (Ht : forall fn', fibers Σ γ' n = Some fn' -> target γ' n = target γ n).
    { intros fn' Hn'; destruct (E3 fn' Hn') as [Hc Hd].
      exact (target_stable K_eq_dec Σ prog Kb rank Hrank γ γ' n fn n fn fn' I EF Hn Hn Hn' Hc Hd
               (le_n _)). }
    assert (Hrl : forall γ1 (l : Life), fibers Σ (set_life Σ γ1 n fn l) n =
                    Some (mkFiber Σ (fcomp fn) (parent Σ fn) (disposed Σ fn) l))
      by (intros; rewrite fibers_set_life, Nat.eqb_refl; reflexivity).
    pose proof (t_lb K_eq_dec Σ prog Kb _ I) as LB.
    cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [step] in H; rewrite Hn in H|]);
      [| | | | | | | |destruct Hin]; subst F'.
    - (* LBegin *)
      destruct (life Σ fn) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (target γ n) as [w|] eqn:Htg; [|discriminate]; injection H as <-.
      rewrite Hrl; specialize (Ht _ (Hrl _ _)).
      unfold vmu, mu; cbn [life]; rewrite Hl, Htg.
      rewrite (proj2 (target_is_spec K_eq_dec Σ prog _ n w) Ht); cbn; unfold Bm; lia.
    - (* LStep *)
      destruct (life Σ fn) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (may_step K_eq_dec Σ prog γ n P w) eqn:Hms; [|discriminate]; injection H as <-.
      destruct (LB n fn P acc w Hn Hl) as [Hlen HbP].
      destruct (target_is γ n w) eqn:Hti.
      2: { (* an iteration landing after the target has turned *)
      assert (HnD : P <> PDone) by (intros ->; cbn in Hms; congruence).
      set (T := muU γ fn [] None (target γ n)).
      assert (Hmu : vmu γ F n fn = S (2 * Kb + 1 + T + (Kb - length acc)))
        by (unfold vmu; rewrite Hl, Hti; reflexivity).
      rewrite Hmu.
      assert (Goal : forall γ1 (l : Life),
                target (set_life Σ γ1 n fn l) n = target γ n ->
                (match l with
                 | Unloading _ acc' w' (Some _) => acc' = acc /\ w' = w
                 | Loading _ _ acc' w' => length acc' = S (length acc) /\ w' = w /\ length acc < Kb
                 | _ => False
                 end) ->
                vmu (set_life Σ γ1 n fn l) F n (mkFiber Σ (fcomp fn) (parent Σ fn) (disposed Σ fn) l)
                < S (2 * Kb + 1 + T + (Kb - length acc))).
      { intros γ1 l Ht' Hshape.
        unfold vmu; cbn [life].
        destruct l as [z'|P' acc' w'|acc' w'|acc' w' [e|]]; try contradiction.
        - destruct Hshape as (Hla & -> & Hlt).
          rewrite (target_is_stable K_eq_dec Σ prog γ _ n w Ht'), Hti, Ht'.
          unfold T, muU, dflag; cbn [Wt disposed].
          destruct (target γ n); destruct (disposed Σ fn); unfold Bm; lia.
        - destruct Hshape as [-> ->].
          rewrite (target_is_stable K_eq_dec Σ prog γ _ n w Ht'), Hti, Ht'.
          unfold T, muU, owe, dflag; cbn [Wt disposed].
          match goal with |- context [Wt ?g acc] => pose proof (Wt_le Σ g acc) end.
          destruct (target γ n); destruct (disposed Σ fn); unfold Bm; lia. }
      Ltac vfin2 Goal Ht Hrl :=
        rewrite Hrl; apply Goal; [eapply Ht; apply Hrl | cbn; repeat split; auto].
      destruct P as [| |k a κ|k s P'|c P'].
      + contradiction.
      + cbn [load_step] in Ht |- *; vfin2 Goal Ht Hrl.
      + assert (Hlt : length acc < Kb) by (inversion HbP; lia).
        rewrite (load_step_op K_eq_dec Σ prog γ n fn k a κ acc w) in Ht |- *.
        destruct (op_binding K_eq_dec Σ prog γ n fn k w) as [b|]; [|vfin2 Goal Ht Hrl].
        destruct (run a (next Σ γ) (bst Σ b)) as [[[s' g] o]|]; vfin2 Goal Ht Hrl.
      + assert (Hlt : length acc < Kb) by (inversion HbP; lia).
        cbn [load_step] in Ht |- *.
        destruct (kmem K_eq_dec k (provs Σ (prog (fcomp fn)))); [|vfin2 Goal Ht Hrl].
        destruct (binds Σ γ k); vfin2 Goal Ht Hrl.
      + assert (Hlt : length acc < Kb) by (inversion HbP; lia).
        cbn [load_step] in Ht |- *.
        destruct (conflict K_eq_dec Σ prog γ c); vfin2 Goal Ht Hrl. }
      assert (Hmu : vmu γ F n fn = 3 * Kb + 10 - length acc)
        by (unfold vmu; rewrite Hl, Hti; reflexivity).
      rewrite Hmu.
      assert (Goal : forall γ1 (l : Life),
                target (set_life Σ γ1 n fn l) n = target γ n ->
                (match l with
                 | Active _ acc' w' => acc' = acc /\ w' = w
                 | Unloading _ acc' w' (Some _) => acc' = acc /\ w' = w
                 | Loading _ _ acc' w' => length acc' = S (length acc) /\ w' = w
                 | _ => False
                 end) ->
                vmu (set_life Σ γ1 n fn l) F n (mkFiber Σ (fcomp fn) (parent Σ fn) (disposed Σ fn) l)
                < 3 * Kb + 10 - length acc).
      { intros γ1 l Ht' Hshape.
        unfold vmu; cbn [life].
        destruct l as [z'|P' acc' w'|acc' w'|acc' w' [e|]]; try contradiction.
        - destruct Hshape as [Hla ->].
          rewrite (target_is_stable K_eq_dec Σ prog γ _ n w Ht'), Hti; lia.
        - destruct Hshape as [-> ->].
          unfold mu; cbn [life].
          rewrite (target_is_stable K_eq_dec Σ prog γ _ n w Ht'), Hti; lia.
        - destruct Hshape as [-> ->].
          rewrite (target_is_stable K_eq_dec Σ prog γ _ n w Ht'), Hti.
          unfold muU, dflag; cbn.
          pose proof (Wt_le Σ (set_life Σ γ1 n fn (Unloading Σ acc w (Some e))) acc).
          destruct (disposed Σ fn); lia. }
      Ltac vfin Goal Ht Hrl :=
        rewrite Hrl; apply Goal; [eapply Ht; apply Hrl | cbn; auto].
      destruct P as [| |k a κ|k s P'|c P'].
      + cbn [load_step] in Ht |- *; vfin Goal Ht Hrl.
      + cbn [load_step] in Ht |- *; vfin Goal Ht Hrl.
      + rewrite (load_step_op K_eq_dec Σ prog γ n fn k a κ acc w) in Ht |- *.
        destruct (op_binding K_eq_dec Σ prog γ n fn k w) as [b|]; [|vfin Goal Ht Hrl].
        destruct (run a (next Σ γ) (bst Σ b)) as [[[s' g] o]|]; vfin Goal Ht Hrl.
      + cbn [load_step] in Ht |- *.
        destruct (kmem K_eq_dec k (provs Σ (prog (fcomp fn)))); [|vfin Goal Ht Hrl].
        destruct (binds Σ γ k); vfin Goal Ht Hrl.
      + cbn [load_step] in Ht |- *.
        destruct (conflict K_eq_dec Σ prog γ c); vfin Goal Ht Hrl.
    - (* LDivert *)
      destruct (life Σ fn) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is γ n w) eqn:Hti; [discriminate|]; injection H as <-.
      rewrite Hrl; specialize (Ht _ (Hrl _ _)).
      unfold vmu, mu; cbn [life]; rewrite Hl, Hti, Ht.
      destruct (LB n fn P acc w Hn Hl) as [Hlen _].
      unfold muU, dflag; cbn [Wt disposed].
      match goal with |- context [Wt ?g acc] => pose proof (Wt_le Σ g acc) end.
      destruct (target γ n); destruct (disposed Σ fn); unfold Bm; lia.
    - (* LLeave *)
      destruct (life Σ fn) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (target_is γ n w) eqn:Hti; [discriminate|]; injection H as <-.
      rewrite Hrl; specialize (Ht _ (Hrl _ _)).
      unfold vmu, mu; cbn [life]; rewrite Hl, Hti, Ht.
      unfold muU; rewrite (Wt_ext Σ γ _ acc); [unfold dflag; cbn; lia|].
      intros x Hx; apply childflag_relife; [reflexivity|].
      apply (own_item_ne K_eq_dec Σ prog Kb rank Hrank γ n fn x I Hn); rewrite Hl; exact Hx.
    - (* LUndo *)
      destruct (life Σ fn) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      destruct (undo_step_shape K_eq_dec Σ γ γ' n fn u acc w z H) as (γ1 & -> & E).
      rewrite Hrl; specialize (Ht _ (Hrl _ _)).
      assert (HW : Wt (set_life Σ γ1 n fn (Unloading Σ acc w z)) acc = Wt γ acc).
      { apply Wt_ext; intros x Hx; apply childflag_relife; [exact E|].
        apply (own_item_ne K_eq_dec Σ prog Kb rank Hrank γ n fn x I Hn); rewrite Hl; right; exact Hx. }
      assert (Hu : 1 <= wt Σ γ u) by (destruct u; cbn; lia).
      unfold vmu, mu; cbn [life]; rewrite Hl.
      destruct z as [e|].
      + rewrite (target_is_stable K_eq_dec Σ prog γ _ n w Ht), Ht.
        unfold muU, owe, dflag; cbn [Wt disposed]; rewrite HW.
        destruct (target_is γ n w); lia.
      + rewrite Ht; unfold muU, dflag; cbn [Wt disposed]; rewrite HW; lia.
    - (* LRetireChild *)
      destruct (life Σ fn) as [| | |[|[k p t g|k p|mm] acc] w z] eqn:Hl; try discriminate.
      destruct (fibers Σ γ mm) as [g|] eqn:Hg; [|discriminate].
      unheld H; destruct (disposed Σ g) eqn:Hdg; [discriminate|]; injection H as <-.
      assert (Hmn : mm <> n)
        by (apply (own_item_ne K_eq_dec Σ prog Kb rank Hrank γ n fn mm I Hn); rewrite Hl; left; reflexivity).
      set (γ2 := set_fiber Σ γ mm (mkFiber Σ (fcomp g) (parent Σ g) true (life Σ g))).
      assert (Hn' : fibers Σ γ2 n = Some fn).
      { subst γ2; cbn; unfold fupd; destruct (Nat.eqb_spec n mm); [congruence | exact Hn]. }
      rewrite Hn'; specialize (Ht _ Hn').
      assert (Hf : childflag Σ γ2 mm = 0)
        by (subst γ2; unfold childflag; cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity).
      assert (Hf0 : childflag Σ γ mm = 1) by (unfold childflag; rewrite Hg, Hdg; reflexivity).
      assert (Hm : Wt γ2 acc <= Wt γ acc).
      { apply Wt_mono; intros x _; subst γ2; unfold childflag; cbn; unfold fupd.
        destruct (Nat.eqb_spec x mm) as [->|_]; [rewrite Hg, Hdg; cbn; lia | apply Nat.le_refl]. }
      unfold vmu, mu; rewrite Hl; unfold γ2 in *.
      destruct z as [e|].
      + rewrite (target_is_stable K_eq_dec Σ prog γ _ n w Ht), Ht.
        unfold muU, owe; cbn [Wt wt]; rewrite Hf, Hf0.
        destruct (target_is γ n w); lia.
      + rewrite Ht; unfold muU; cbn [Wt wt]; rewrite Hf, Hf0; lia.
    - (* LUnloaded *)
      destruct (life Σ fn) as [| | |[|u acc] w z] eqn:Hl; try discriminate; injection H as <-.
      rewrite Hrl; specialize (Ht _ (Hrl _ _)).
      assert (HF : vupd F n (unloading_view Σ γ n) n = Some w)
        by (unfold vupd, unloading_view; rewrite Nat.eqb_refl, Hn, Hl; reflexivity).
      unfold vmu, mu; cbn [life]; rewrite Hl.
      destruct z as [e|].
      + rewrite HF, (target_is_stable K_eq_dec Σ prog γ _ n w Ht), Ht.
        unfold muU, owe, dflag; cbn [Wt disposed].
        destruct (target_is γ n w); lia.
      + rewrite Ht; unfold muU; cbn [Wt].
        destruct (target γ n); unfold dflag; cbn; lia.
    - (* LRemove *)
      destruct (life Σ fn) as [z| | |] eqn:Hl; try discriminate.
      destruct (disposed Σ fn) eqn:Hd; [|discriminate]; cbn in H.
      destruct (negb (has_child Σ γ n)); [|discriminate]; injection H as <-.
      cbn; unfold fupd; rewrite Nat.eqb_refl.
      unfold vmu, mu; rewrite Hl; unfold dflag; rewrite Hd.
      destruct z.
      + destruct (F n); [destruct (target_is γ n _)|]; lia.
      + assert (Htn : target γ n = None) by (unfold target; rewrite Hn, Hd; reflexivity).
        rewrite Htn; lia.
  Qed.

  (** The recorded views after a core step of [n]. *)
  Definition Fnext (ℓ : @Label C) (F : nat -> option View) (γ : State) : nat -> option View :=
    match ℓ with
    | LUnloaded n0 => vupd F n0 (unloading_view Σ γ n0)
    | _ => F
    end.

  Lemma Fnext_other ℓ F γ n m :
    In ℓ (lifecycle_labels n) -> m <> n -> Fnext ℓ F γ m = F m.
  Proof.
    intros Hin Hmn; cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn; try reflexivity|]); [|destruct Hin].
    unfold vupd; destruct (Nat.eqb_spec m n); [contradiction | reflexivity].
  Qed.

  (** ** Fibers of rank at most that of [n], other than [n], keep their measure *)
  Lemma vmu_other (γ γ' : State) F F' (n : nat) ℓ (fn : Fiber) (m : nat) (fm : Fiber) :
    TInv γ -> In ℓ (lifecycle_labels n) -> step γ ℓ = Some γ' -> fibers Σ γ n = Some fn ->
    m <> n -> fibers Σ γ m = Some fm -> frank fm <= frank fn -> F' m = F m ->
    fibers Σ γ' m = Some fm /\ vmu γ' F' m fm = vmu γ F m fm.
  Proof.
    intros I Hin H Hn Hmn Hm Hr HF.
    destruct (mu_other K_eq_dec Σ prog Kb rank Hrank γ γ' n ℓ fn m fm I Hin H Hn Hmn Hm Hr)
      as [Hm' Hmu].
    split; [exact Hm'|].
    pose proof (lstep_effects K_eq_dec Σ prog Kb rank Hrank γ γ' n ℓ fn I Hin H Hn) as EF.
    pose proof (target_stable K_eq_dec Σ prog Kb rank Hrank γ γ' n fn m fm fm I EF Hn Hm Hm'
                  eq_refl eq_refl Hr) as Ht.
    unfold vmu.
    destruct (life Σ fm) as [[e|]|P acc w|acc w|acc w [e|]] eqn:Hl.
    - rewrite HF; destruct (F m) as [w|]; [|reflexivity].
      rewrite (target_is_stable K_eq_dec Σ prog γ γ' m w Ht), Ht; reflexivity.
    - exact Hmu.
    - rewrite (target_is_stable K_eq_dec Σ prog γ γ' m w Ht), Ht; reflexivity.
    - exact Hmu.
    - unfold mu in Hmu; rewrite Hl in Hmu; unfold muU in Hmu; cbn in Hmu.
      rewrite (target_is_stable K_eq_dec Σ prog γ γ' m w Ht), Ht.
      unfold muU, owe; cbn; destruct (target_is γ m w); lia.
    - exact Hmu.
  Qed.

  (** ** [VClear] *)
  Lemma vclear_shape (vs vs' : VState) n :
    vstep vs (VClear n) = Some vs' ->
    exists f e w, fibers Σ (vcore vs) n = Some f /\ life Σ f = Inactive Σ (Some e) /\
      fview vs n = Some w /\ target_is (vcore vs) n w = false /\
      vcore vs' = set_life Σ (vcore vs) n f (Inactive Σ None) /\ fview vs' = fview vs.
  Proof.
    cbn [ViewFail.vstep]; unfold clearable.
    destruct (fibers Σ (vcore vs) n) as [f|] eqn:Hn; [|discriminate].
    destruct (fview vs n) as [w|] eqn:Hw; [|discriminate].
    destruct (life Σ f) as [[e|]| | |] eqn:Hl; try discriminate.
    destruct (target_is (vcore vs) n w) eqn:Ht; [discriminate|]; cbn.
    rewrite Hn, Hl; intros [= <-]; exists f, e, w; cbn; auto 10.
  Qed.

  Lemma visible_relife (γ : State) n f (l : Life) k :
    fibers Σ γ n = Some f -> is_active Σ (life Σ f) = false -> is_active Σ l = false ->
    visible Σ (set_life Σ γ n f l) k = visible Σ γ k.
  Proof.
    intros Hn Ha Hl; unfold visible; cbn [set_life set_fiber with_fibers binds].
    destruct (binds Σ γ k) as [b|]; [|reflexivity].
    rewrite fibers_set_life; destruct (Nat.eqb_spec (owner Σ b) n) as [->|]; [|reflexivity].
    rewrite Hn; cbn; rewrite Hl, Ha; reflexivity.
  Qed.

  Lemma resolve_eq (γ γ' : State) ks :
    (forall k, visible Σ γ' k = visible Σ γ k) -> resolve Σ γ' ks = resolve Σ γ ks.
  Proof.
    intros H; induction ks as [|k ks IH]; cbn; [reflexivity|]; rewrite H, IH; reflexivity.
  Qed.

  Lemma target_relife (γ : State) n f (l : Life) m :
    fibers Σ γ n = Some f -> is_active Σ (life Σ f) = false -> is_active Σ l = false ->
    target (set_life Σ γ n f l) m = target γ m.
  Proof.
    intros Hn Ha Hl; unfold target; rewrite fibers_set_life.
    assert (R : forall ks, resolve Σ (set_life Σ γ n f l) ks = resolve Σ γ ks)
      by (intros ks; apply resolve_eq; intros k; apply visible_relife; auto).
    destruct (Nat.eqb_spec m n) as [->|]; [rewrite Hn; cbn [Calculus.comp disposed]|].
    - destruct (disposed Σ f); [reflexivity | apply R].
    - destruct (fibers Σ γ m) as [g|]; [destruct (disposed Σ g); [reflexivity | apply R] | reflexivity].
  Qed.

  Lemma vclear_other (vs vs' : VState) n m fm :
    vstep vs (VClear n) = Some vs' -> m <> n -> fibers Σ (vcore vs) m = Some fm ->
    fibers Σ (vcore vs') m = Some fm /\ vmu (vcore vs') (fview vs') m fm = vmu (vcore vs) (fview vs) m fm.
  Proof.
    intros H Hmn Hm.
    destruct (vclear_shape vs vs' n H) as (f & e & w & Hn & Hl & _ & _ & E & EF).
    rewrite E, EF.
    assert (Ha : is_active Σ (life Σ f) = false) by (rewrite Hl; reflexivity).
    assert (Ht : target (set_life Σ (vcore vs) n f (Inactive Σ None)) m = target (vcore vs) m)
      by exact (target_relife _ n f (Inactive Σ None) m Hn Ha eq_refl).
    assert (HW : forall acc, Wt (set_life Σ (vcore vs) n f (Inactive Σ None)) acc = Wt (vcore vs) acc).
    { intros acc; apply Wt_ext; intros x _; unfold childflag; rewrite fibers_set_life.
      destruct (Nat.eqb_spec x n) as [->|]; [rewrite Hn; reflexivity | reflexivity]. }
    split; [rewrite fibers_set_life; destruct (Nat.eqb_spec m n); [contradiction | exact Hm]|].
    unfold vmu, mu, muU.
    destruct (life Σ fm) as [[e'|]|P acc w'|acc w'|acc w' [e'|]];
      try destruct (fview vs m) as [w0|];
      repeat rewrite (target_is_stable K_eq_dec Σ prog (vcore vs) _ m _ Ht);
      rewrite ?Ht, ?HW; reflexivity.
  Qed.

  Lemma vclear_drop (vs vs' : VState) n f :
    vstep vs (VClear n) = Some vs' -> fibers Σ (vcore vs) n = Some f ->
    exists f', fibers Σ (vcore vs') n = Some f' /\ fcomp f' = fcomp f /\
      vmu (vcore vs') (fview vs') n f' < vmu (vcore vs) (fview vs) n f.
  Proof.
    intros H Hn0.
    destruct (vclear_shape vs vs' n H) as (f1 & e & w & Hn & Hl & Hw & Hti & E & EF).
    rewrite Hn in Hn0; injection Hn0 as <-.
    rewrite E, EF; eexists; rewrite fibers_set_life, Nat.eqb_refl; split; [reflexivity|]; split;
      [reflexivity|].
    assert (Ha : is_active Σ (life Σ f1) = false) by (rewrite Hl; reflexivity).
    pose proof (target_relife _ n f1 (Inactive Σ None) n Hn Ha eq_refl) as Ht.
    unfold vmu, mu; cbn [life]; rewrite Hl, Hw, Hti, Ht.
    unfold owe, dflag; cbn [disposed]; lia.
  Qed.

  (** ** The measure of a state *)
  Definition vcontrib (vs : VState) (r m : nat) : nat :=
    match fibers Σ (vcore vs) m with
    | Some f => if Nat.eqb (frank f) r then vmu (vcore vs) (fview vs) m f else 0
    | None => 0
    end.

  Definition vPhi (vs : VState) (r : nat) : nat := sumf (vcontrib vs r) (names Σ (vcore vs)).

  Lemma vPhi_ext (vs : VState) r M :
    WF K_eq_dec Σ prog (vcore vs) -> next Σ (vcore vs) <= M ->
    vPhi vs r = sumf (vcontrib vs r) (seq 0 M).
  Proof.
    intros W HM; unfold vPhi, names.
    replace M with (next Σ (vcore vs) + (M - next Σ (vcore vs))) by lia.
    rewrite seq_app, sumf_app.
    rewrite (sumf_zero _ (seq (0 + next Σ (vcore vs)) _)); [lia|].
    intros x Hx; apply in_seq in Hx; unfold vcontrib.
    destruct (fibers Σ (vcore vs) x) eqn:E; [|reflexivity].
    apply (wf_names K_eq_dec Σ prog _ W) in E; lia.
  Qed.

  Definition vlstep (vs' vs : VState) : Prop :=
    (exists n ℓ, In ℓ (lifecycle_labels n) /\ vstep vs (ViewFail.VCore ℓ) = Some vs') \/
    (exists n, vstep vs (VClear n) = Some vs').

  Lemma vstep_core_fview (vs vs' : VState) ℓ :
    vstep vs (ViewFail.VCore ℓ) = Some vs' ->
    step (vcore vs) ℓ = Some (vcore vs') /\ fview vs' = Fnext ℓ (fview vs) (vcore vs).
  Proof.
    intros H; split; [exact (vstep_core K_eq_dec Σ prog vs vs' _ H)|].
    rewrite (vstep_fview K_eq_dec Σ prog vs vs' _ H); destruct ℓ; reflexivity.
  Qed.

  (** ** Every lifecycle step lowers the measure *)
  Theorem vphi_drop (vs vs' : VState) :
    TInv (vcore vs) -> vlstep vs' vs -> lexR Rb (vPhi vs') (vPhi vs).
  Proof.
    intros I [(n & ℓ & Hin & Hv)|(n & Hv)].
    - destruct (vstep_core_fview vs vs' ℓ Hv) as [H HF].
      set (γ := vcore vs) in *; set (γ' := vcore vs') in *; set (F := fview vs) in *.
      destruct (fibers Σ γ n) as [fn|] eqn:Hn.
      2: { rewrite (step_absent K_eq_dec Σ prog γ n ℓ Hn Hin) in H; discriminate. }
      pose proof (tinv_step K_eq_dec Σ prog Kb HK γ γ' ℓ I H) as I'.
      pose proof (lstep_effects K_eq_dec Σ prog Kb rank Hrank γ γ' n ℓ fn I Hin H Hn) as EF.
      pose proof EF as (E1 & E2 & E3 & E5 & _).
      pose proof (vmu_drop γ γ' F n ℓ fn I Hin H Hn) as Hd; cbn zeta in Hd.
      fold (Fnext ℓ F γ) in Hd; rewrite <- HF in Hd.
      set (r0 := frank fn).
      assert (P1 : forall r, r <= r0 -> forall m,
                vcontrib vs' r m <= vcontrib vs r m /\
                (m <> n \/ r < r0 -> vcontrib vs' r m = vcontrib vs r m)).
      { intros r Hr m; unfold vcontrib; fold γ γ' F.
        destruct (Nat.eq_dec m n) as [->|Hmn].
        - rewrite Hn.
          destruct (fibers Σ γ' n) as [fn'|] eqn:Hn'.
          + destruct (E3 fn' eq_refl) as [Hc _]; rewrite Hc.
            destruct (Nat.eqb_spec (frank fn) r) as [Er|Er].
            * split; [lia|]; intros [Cx|Cx]; [contradiction | subst r0; lia].
            * split; [lia | intros; reflexivity].
          + destruct (Nat.eqb_spec (frank fn) r) as [Er|Er].
            * split; [lia|]; intros [Cx|Cx]; [contradiction | subst r0; lia].
            * split; [lia | intros; reflexivity].
        - destruct (fibers Σ γ m) as [fm|] eqn:Hm.
          + destruct (Compare_dec.le_lt_dec (frank fm) r0) as [Hle|Hgt].
            * destruct (vmu_other γ γ' F (fview vs') n ℓ fn m fm I Hin H Hn Hmn Hm Hle)
                as [Hm' Hmu]; [rewrite HF; exact (Fnext_other ℓ F γ n m Hin Hmn)|].
              rewrite Hm', Hmu; split; [lia | auto].
            * destruct (E1 m fm Hmn Hm) as [Hm'|[Hm' _]]; rewrite Hm'; cbn [Calculus.comp];
                (destruct (Nat.eqb_spec (frank fm) r); [subst r0; lia | split; [lia | auto]]).
          + destruct (fibers Σ γ' m) as [fm'|] eqn:Hm'; [|split; [lia | auto]].
            destruct (E2 m fm' Hm Hm') as [_ HS].
            assert (frank fn < frank fm') by (apply Hrank; right; left; exact HS).
            destruct (Nat.eqb_spec (frank fm') r); [subst r0; lia | split; [lia | auto]]. }
      assert (P2 : vcontrib vs' r0 n < vcontrib vs r0 n).
      { unfold vcontrib; fold γ γ'; rewrite Hn; subst r0; rewrite Nat.eqb_refl.
        destruct (fibers Σ γ' n) as [fn'|] eqn:Hn'; [|exact Hd].
        destruct (E3 fn' eq_refl) as [Hc _]; rewrite Hc, Nat.eqb_refl; exact Hd. }
      set (M := next Σ γ + next Σ γ').
      pose proof (t_wf K_eq_dec Σ prog Kb _ I) as W; pose proof (t_wf K_eq_dec Σ prog Kb _ I') as W'.
      exists r0; split; [apply Hbnd|]; split.
      + intros i Hi.
        rewrite (vPhi_ext vs' i M W') by (subst M γ γ'; lia); rewrite (vPhi_ext vs i M W) by (subst M γ γ'; lia).
        apply sumf_eq; intros m _; apply (proj2 (P1 i ltac:(lia) m)); right; exact Hi.
      + rewrite (vPhi_ext vs' r0 M W') by (subst M γ γ'; lia); rewrite (vPhi_ext vs r0 M W) by (subst M γ γ'; lia).
        apply (sumf_lt _ _ _ n); [intros m _; exact (proj1 (P1 r0 (le_n _) m)) | | exact P2].
        apply in_seq; pose proof (wf_names K_eq_dec Σ prog γ W n fn Hn); lia.
    - destruct (vclear_shape vs vs' n Hv) as (f & e & w & Hn & _ & _ & _ & E & _).
      pose proof (tinv_step K_eq_dec Σ prog Kb HK _ _ _ I (vstep_core K_eq_dec Σ prog vs vs' _ Hv))
        as I'.
      destruct (vclear_drop vs vs' n f Hv Hn) as (f' & Hn' & Hc & Hd).
      set (r0 := frank f).
      assert (P1 : forall r m, vcontrib vs' r m <= vcontrib vs r m /\
                               (m <> n \/ r <> r0 -> vcontrib vs' r m = vcontrib vs r m)).
      { intros r m; unfold vcontrib.
        destruct (Nat.eq_dec m n) as [->|Hmn].
        - rewrite Hn, Hn', Hc.
          destruct (Nat.eqb_spec (frank f) r); [|split; [lia | auto]].
          split; [lia|]; intros [Cx|Cx]; [congruence | subst r0; congruence].
        - destruct (fibers Σ (vcore vs) m) as [fm|] eqn:Hm.
          + destruct (vclear_other vs vs' n m fm Hv Hmn Hm) as [Hm' Hmu].
            rewrite Hm', Hmu; split; [lia | auto].
          + rewrite E, fibers_set_life; destruct (Nat.eqb_spec m n); [contradiction|].
            rewrite Hm; split; [lia | auto]. }
      assert (P2 : vcontrib vs' r0 n < vcontrib vs r0 n).
      { unfold vcontrib; rewrite Hn, Hn', Hc; subst r0; rewrite Nat.eqb_refl; exact Hd. }
      set (M := next Σ (vcore vs) + next Σ (vcore vs')).
      pose proof (t_wf K_eq_dec Σ prog Kb _ I) as W; pose proof (t_wf K_eq_dec Σ prog Kb _ I') as W'.
      exists r0; split; [apply Hbnd|]; split.
      + intros i Hi.
        rewrite (vPhi_ext vs' i M W') by lia; rewrite (vPhi_ext vs i M W) by lia.
        apply sumf_eq; intros m _; apply (proj2 (P1 i m)); right; lia.
      + rewrite (vPhi_ext vs' r0 M W') by lia; rewrite (vPhi_ext vs r0 M W) by lia.
        apply (sumf_lt _ _ _ n); [intros m _; exact (proj1 (P1 r0 m)) | | exact P2].
        apply in_seq; pose proof (wf_names K_eq_dec Σ prog _ W n f Hn); lia.
  Qed.

  (** ** Termination *)
  Definition vLStepRel (vs' vs : VState) : Prop := TInv (vcore vs) /\ vlstep vs' vs.

  Theorem vtermination (vs : VState) : TInv (vcore vs) -> Acc vLStepRel vs.
  Proof.
    assert (G : forall v, Acc (lexR Rb) v ->
                forall vs, TInv (vcore vs) -> (forall r, vPhi vs r = v r) -> Acc vLStepRel vs).
    { intros v Hacc; induction Hacc as [v _ IH]; intros vs0 I E.
      constructor; intros vs1 [I0 Hs].
      pose proof (vphi_drop vs0 vs1 I0 Hs) as (r & Hr & Heq & Hlt).
      assert (I1 : TInv (vcore vs1)).
      { destruct Hs as [(n & ℓ & _ & Hv)|(n & Hv)];
          exact (tinv_step K_eq_dec Σ prog Kb HK _ _ _ I0 (vstep_core K_eq_dec Σ prog vs0 vs1 _ Hv)). }
      apply (IH (vPhi vs1)); [| exact I1 | intros; reflexivity].
      exists r; split; [exact Hr|]; split.
      - intros i Hi; rewrite <- E; apply Heq; exact Hi.
      - rewrite <- E; exact Hlt. }
    intros I; exact (G (vPhi vs) (lexR_wf Rb _) vs I (fun _ => eq_refl)).
  Qed.

  (** From the initial state, after any execution. *)
  Corollary vtermination_reachable (vs : VState) ls :
    vrun_labels K_eq_dec Σ prog (vinit Σ) ls = Some vs -> Acc vLStepRel vs.
  Proof.
    intros H; apply vtermination.
    pose proof (vrun_core K_eq_dec Σ prog _ _ ls H) as Hr; cbn in Hr.
    assert (G : forall γ0 ls γ, TInv γ0 ->
                run_labels K_eq_dec Σ prog γ0 ls = Some γ -> TInv γ).
    { intros γ0 ls0; revert γ0; induction ls0 as [|ℓ ls0 IH]; cbn; intros γ0 γ1 I0 Hr0.
      - injection Hr0 as <-; exact I0.
      - destruct (step γ0 ℓ) as [γ0'|] eqn:Hs; [|discriminate].
        exact (IH γ0' γ1 (tinv_step K_eq_dec Σ prog Kb HK γ0 γ0' ℓ I0 Hs) Hr0). }
    exact (G _ _ _ (tinv_init K_eq_dec Σ prog Kb) Hr).
  Qed.
End VTermination.
