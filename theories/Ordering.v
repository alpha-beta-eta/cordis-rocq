(** * Ordering and resolution coherence (R3, second part)

    Counterparts of the paper's Theorem 63 (ordering) and Theorem 64
    (resolution coherence) for the v1 calculus.

    - Every fiber follows the lifecycle automaton of Figure 2, keeps its
      component and parent, and keeps its view while it stays installed;
      new fibers start Inactive.
    - A fiber begins only when all its dependencies are visible, i.e. bound
      by an Active provider.
    - While a fiber is installed, every provision it resolved still exists
      and its provider is installed: providers outlive consumers. The view
      fixes the provision (its pid) for the whole episode. The paper's claim
      that the value read stays fixed has no counterpart here: service
      states are shared and change by design.
    - A provision is withdrawn only when no other installed fiber resolves
      it; a parent passes a spawn undo item only after the child is gone.
    - A Loading fiber takes a step only against its committed view; once
      its target differs, it can only divert. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service Calculus Preservation.
Import ListNotations.

Section Ordering.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).
  Local Notation Fiber := (@Fiber K Σ C).
  Local Notation Life := (@Life K Σ C).
  Local Notation Undo := (@Undo K Σ).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation next := (next Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation parent := (parent Σ).
  Local Notation disposed := (disposed Σ).
  Local Notation view_of := (view_of Σ).
  Local Notation acc_of := (acc_of Σ).
  Local Notation is_installed := (is_installed Σ).
  Local Notation is_active := (is_active Σ).
  Local Notation pid := (pid Σ).
  Local Notation owner := (owner Σ).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation WF := (WF K_eq_dec Σ prog).
  Local Notation target := (target Σ prog).

  (** ** The lifecycle automaton *)
  Definition tag (l : Life) : nat :=
    match l with
    | Inactive _ _ => 0 | Loading _ _ _ _ => 1 | Active _ _ _ => 2 | Unloading _ _ _ _ => 3
    end.

  (** Inactive → Loading → Active → Unloading → Inactive, with
      Loading → Unloading for a divert or a failure. *)
  Definition Edge (t t' : nat) : Prop :=
    t = t' \/ (t = 0 /\ t' = 1) \/ (t = 1 /\ t' = 2) \/ (t = 1 /\ t' = 3) \/
    (t = 2 /\ t' = 3) \/ (t = 3 /\ t' = 0).

  (** What a step may change about a fiber that stays present. *)
  Definition Same (fm fm' : Fiber) : Prop :=
    fcomp fm' = fcomp fm /\ parent fm' = parent fm /\
    Edge (tag (life fm)) (tag (life fm')) /\
    (is_installed (life fm) = true -> is_installed (life fm') = true ->
     view_of (life fm') = view_of (life fm)).

  Lemma Same_refl (fm : Fiber) : Same fm fm.
  Proof. unfold Same, Edge; auto. Qed.

  (** ** Shapes of the compound steps *)
  Definition keeps (γ γ1 : State) : Prop :=
    (forall m fm, fibers γ m = Some fm -> fibers γ1 m = Some fm) /\
    (forall m fm, fibers γ m = None -> fibers γ1 m = Some fm ->
       m = next γ /\ exists c q, fm = mkFiber Σ c (Some q) false (Inactive Σ None)).

  Lemma keeps_same (γ γ1 : State) : fibers γ1 = fibers γ -> keeps γ γ1.
  Proof. intros E; split; intros m fm; rewrite E; [auto | congruence]. Qed.

  Lemma load_step_shape (γ : State) n f P acc w :
    WF γ -> fibers γ n = Some f -> life f = Loading Σ P acc w ->
    exists γ1 l, load_step K_eq_dec Σ prog γ n f P acc w = set_life Σ γ1 n f l /\
                 keeps γ γ1 /\ view_of l = w /\ (tag l = 1 \/ tag l = 2 \/ tag l = 3).
  Proof.
    intros W Hn Hl.
    destruct P as [| |k a κ|k s P'|c P']; cbn [load_step].
    - eexists _, _; split; [reflexivity|]; split; [apply keeps_same; reflexivity|].
      cbn; auto.
    - eexists _, _; split; [reflexivity|]; split; [apply keeps_same; reflexivity|].
      cbn; auto.
    - match goal with |- exists _ _, match ?x with _ => _ end = _ /\ _ =>
        destruct x as [p|] end.
      2: { eexists _, _; split; [reflexivity|]; split; [apply keeps_same; reflexivity|].
           cbn; auto. }
      destruct (binds γ k) as [b|].
      2: { eexists _, _; split; [reflexivity|]; split; [apply keeps_same; reflexivity|].
           cbn; auto. }
      destruct (Nat.eqb (pid b) p).
      2: { eexists _, _; split; [reflexivity|]; split; [apply keeps_same; reflexivity|].
           cbn; auto. }
      destruct (run a (next γ) (bst Σ b)) as [[[s' g] o]|];
        (eexists _, _; split; [reflexivity|]; split; [apply keeps_same; reflexivity|];
         cbn; auto).
    - destruct (kmem K_eq_dec k (provs Σ (prog (fcomp f)))).
      2: { eexists _, _; split; [reflexivity|]; split; [apply keeps_same; reflexivity|].
           cbn; auto. }
      destruct (binds γ k);
        (eexists _, _; split; [reflexivity|]; split; [apply keeps_same; reflexivity|];
         cbn; auto).
    - destruct (conflict K_eq_dec Σ prog γ c).
      { eexists _, _; split; [reflexivity|]; split; [apply keeps_same; reflexivity|].
        cbn; auto. }
      eexists _, _; split; [reflexivity|]; split; [|cbn; auto].
      split; cbn; unfold fupd.
      + intros m fm Hm; destruct (Nat.eqb_spec m (next γ)) as [->|_]; [|exact Hm].
        apply (wf_names K_eq_dec Σ prog γ W) in Hm; lia.
      + intros m fm Hm; destruct (Nat.eqb_spec m (next γ)) as [->|_]; [|congruence].
        intros [= <-]; split; [reflexivity|]; eauto.
  Qed.

  Lemma undo_step_shape (γ γ' : State) n f u acc w z :
    undo_step K_eq_dec Σ γ n f u acc w z = Some γ' ->
    exists γ1, γ' = set_life Σ γ1 n f (Unloading Σ acc w z) /\ fibers γ1 = fibers γ.
  Proof.
    destruct u as [k p t g|k p|m]; cbn [undo_step].
    - destruct (binds γ k) as [b|]; [destruct (Nat.eqb (pid b) p)|];
        intros [= <-]; eexists; split; reflexivity.
    - destruct (relied Σ γ n p); [discriminate|].
      destruct (binds γ k) as [b|]; [destruct (Nat.eqb (pid b) p)|];
        intros [= <-]; eexists; split; reflexivity.
    - destruct (fibers γ m); [discriminate|].
      intros [= <-]; eexists; split; reflexivity.
  Qed.

  Lemma set_life_Same (γ γ1 : State) n f (l : Life) m fm fm' :
    fibers γ n = Some f ->
    (forall m fm, fibers γ m = Some fm -> fibers γ1 m = Some fm) ->
    Edge (tag (life f)) (tag l) ->
    (is_installed (life f) = true -> is_installed l = true -> view_of l = view_of (life f)) ->
    fibers γ m = Some fm -> fibers (set_life Σ γ1 n f l) m = Some fm' -> Same fm fm'.
  Proof.
    intros Hn Hk He Hv Hm H.
    apply fibers_set_life_inv in H as [[-> ->]|[_ H]].
    - rewrite Hn in Hm; injection Hm as <-; unfold Same; cbn; auto.
    - apply Hk in Hm; rewrite Hm in H; injection H as <-; apply Same_refl.
  Qed.

  Lemma set_fiber_Same (γ : State) n f b m fm fm' :
    fibers γ n = Some f -> fibers γ m = Some fm ->
    fibers (set_fiber Σ γ n (mkFiber Σ (fcomp f) (parent f) b (life f))) m = Some fm' ->
    Same fm fm'.
  Proof.
    intros Hn Hm H; apply fibers_set_fiber_inv in H as [[-> ->]|[_ H]].
    - rewrite Hn in Hm; injection Hm as <-; unfold Same, Edge; cbn; auto.
    - rewrite Hm in H; injection H as <-; apply Same_refl.
  Qed.

  Ltac edge := unfold Edge; cbn; lia.

  (** ** Every fiber follows the automaton *)
  Theorem fiber_step (γ γ' : State) ℓ m fm fm' :
    WF γ -> step γ ℓ = Some γ' ->
    fibers γ m = Some fm -> fibers γ' m = Some fm' -> Same fm fm'.
  Proof.
    intros W H Hm Hm'.
    assert (Id : forall m0 fm0, fibers γ m0 = Some fm0 -> fibers γ m0 = Some fm0)
      by (intros; assumption).
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [step] in H.
    - destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      cbn in Hm'; unfold fupd in Hm'.
      destruct (Nat.eqb_spec m (next γ)) as [->|_].
      + apply (wf_names K_eq_dec Σ prog γ W) in Hm; lia.
      + rewrite Hm in Hm'; injection Hm' as <-; apply Same_refl.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate]; injection H as <-.
      exact (set_fiber_Same γ n f true m fm fm' Hn Hm Hm').
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate; injection H as <-.
      match type of Hm' with context [set_life _ _ _ _ ?l] => apply (set_life_Same γ γ n f l m fm fm' Hn Id) end; [rewrite Hl; edge | | exact Hm | exact Hm'].
      rewrite Hl; cbn; discriminate.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (target γ n); [|discriminate]; injection H as <-.
      match type of Hm' with context [set_life _ _ _ _ ?l] => apply (set_life_Same γ γ n f l m fm fm' Hn Id) end; [rewrite Hl; edge | | exact Hm | exact Hm'].
      rewrite Hl; cbn; discriminate.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [|discriminate]; injection H as <-.
      destruct (load_step_shape γ n f P acc w W Hn Hl) as (γ1 & l & E & [Hk _] & Hv & Ht).
      rewrite E in Hm'.
      apply (set_life_Same γ γ1 n f l m fm fm' Hn Hk); [rewrite Hl; edge | | exact Hm | exact Hm'].
      rewrite Hl, Hv; reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [discriminate|]; injection H as <-.
      match type of Hm' with context [set_life _ _ _ _ ?l] => apply (set_life_Same γ γ n f l m fm fm' Hn Id) end; [rewrite Hl; edge | | exact Hm | exact Hm'].
      rewrite Hl; reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [discriminate|]; injection H as <-.
      match type of Hm' with context [set_life _ _ _ _ ?l] => apply (set_life_Same γ γ n f l m fm fm' Hn Id) end; [rewrite Hl; edge | | exact Hm | exact Hm'].
      rewrite Hl; reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      destruct (undo_step_shape γ γ' n f u acc w z H) as (γ1 & -> & E).
      assert (Hk : forall m0 fm0, fibers γ m0 = Some fm0 -> fibers γ1 m0 = Some fm0)
        by (intros m0 fm0; rewrite E; auto).
      match type of Hm' with context [set_life _ _ _ _ ?l] => apply (set_life_Same γ γ1 n f l m fm fm' Hn Hk) end; [rewrite Hl; edge | | exact Hm | exact Hm'].
      rewrite Hl; reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|[k p t g|k p|m0] acc] w z] eqn:Hl; try discriminate.
      destruct (fibers γ m0) as [g|] eqn:Hg; [|discriminate].
      destruct (disposed g); [discriminate|]; injection H as <-.
      exact (set_fiber_Same γ m0 g true m fm fm' Hg Hm Hm').
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      injection H as <-.
      match type of Hm' with context [set_life _ _ _ _ ?l] => apply (set_life_Same γ γ n f l m fm fm' Hn Id) end; [rewrite Hl; edge | | exact Hm | exact Hm'].
      cbn; discriminate.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [z| | |] eqn:Hl; try discriminate.
      destruct (disposed f && negb (has_child Σ γ n)); [|discriminate]; injection H as <-.
      cbn in Hm'; unfold fupd in Hm'.
      destruct (Nat.eqb_spec m n) as [->|_]; [discriminate|].
      rewrite Hm in Hm'; injection Hm' as <-; apply Same_refl.
    - (* OReact *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (nth_error (reacts Σ (prog (fcomp f))) i) as [c|]; [|discriminate].
      destruct (disposed f || conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      assert (Hk : forall m0 fm0, fibers γ m0 = Some fm0 ->
                fibers (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ)
                  (Some (mkFiber Σ c (Some n) false (Inactive Σ None)))))) m0 = Some fm0).
      { intros m0 fm0 H0; cbn; unfold fupd; pose proof (wf_names K_eq_dec Σ prog γ W m0 fm0 H0).
        destruct (Nat.eqb_spec m0 (next γ)); [lia | exact H0]. }
      match type of Hm' with context [set_life _ _ _ _ ?l] => apply (set_life_Same γ _ n f l m fm fm' Hn Hk) end;
        [rewrite Hl; edge | | exact Hm | exact Hm'].
      rewrite Hl; reflexivity.
    - (* ORestart *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (disposed f); [discriminate|].
      destruct (life f) as [|P acc w|acc w|] eqn:Hl; try discriminate; injection H as <-;
      (match type of Hm' with context [set_life _ _ _ _ ?l] => apply (set_life_Same γ γ n f l m fm fm' Hn Id) end;
        [rewrite Hl; edge | | exact Hm | exact Hm']; rewrite Hl; reflexivity).
  Qed.

  (** New fibers start Inactive, under the next name. *)
  Theorem new_fiber (γ γ' : State) ℓ m fm' :
    WF γ -> step γ ℓ = Some γ' ->
    fibers γ m = None -> fibers γ' m = Some fm' ->
    m = next γ /\ life fm' = Inactive Σ None.
  Proof.
    intros W H Hm Hm'.
    assert (Lift : forall γ1 n f (l : Life), fibers γ n = Some f -> keeps γ γ1 ->
              fibers (set_life Σ γ1 n f l) m = Some fm' ->
              m = next γ /\ life fm' = Inactive Σ None).
    { intros γ1 n f l Hn [_ Hk] H1.
      apply fibers_set_life_inv in H1 as [[-> _]|[_ H1]]; [congruence|].
      destruct (Hk m fm' Hm H1) as [-> (c & q & ->)]; auto. }
    assert (Lift0 : forall γ1 n f (l : Life), fibers γ n = Some f -> fibers γ1 = fibers γ ->
              fibers (set_life Σ γ1 n f l) m = Some fm' ->
              m = next γ /\ life fm' = Inactive Σ None).
    { intros γ1 n f l Hn E; apply Lift; [exact Hn | apply keeps_same; exact E]. }
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [step] in H.
    - destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      cbn in Hm'; unfold fupd in Hm'.
      destruct (Nat.eqb_spec m (next γ)) as [->|_]; [injection Hm' as <-; auto | congruence].
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate]; injection H as <-.
      apply fibers_set_fiber_inv in Hm' as [[-> _]|[_ Hm']]; congruence.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [[z|]| | |]; try discriminate; injection H as <-.
      eapply Lift0; eauto.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [[z|]| | |]; try discriminate.
      destruct (target γ n); [|discriminate]; injection H as <-.
      eapply Lift0; eauto.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [|discriminate]; injection H as <-.
      destruct (load_step_shape γ n f P acc w W Hn Hl) as (γ1 & l & E & Hk & _).
      rewrite E in Hm'; eapply Lift; eauto.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [|P acc w| |]; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [discriminate|]; injection H as <-.
      eapply Lift0; eauto.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| |acc w|]; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [discriminate|]; injection H as <-.
      eapply Lift0; eauto.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z]; try discriminate.
      destruct (undo_step_shape γ γ' n f u acc w z H) as (γ1 & -> & E).
      eapply Lift0; eauto.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|[k p t g|k p|m0] acc] w z]; try discriminate.
      destruct (fibers γ m0) as [g|] eqn:Hg; [|discriminate].
      destruct (disposed g); [discriminate|]; injection H as <-.
      apply fibers_set_fiber_inv in Hm' as [[-> _]|[_ Hm']]; congruence.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z]; try discriminate.
      injection H as <-; eapply Lift0; eauto.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [z| | |]; try discriminate.
      destruct (disposed f && negb (has_child Σ γ n)); [|discriminate]; injection H as <-.
      cbn in Hm'; unfold fupd in Hm'.
      destruct (Nat.eqb_spec m n); congruence.
    - (* OReact *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| |acc w|]; try discriminate.
      destruct (nth_error (reacts Σ (prog (fcomp f))) i) as [c|]; [|discriminate].
      destruct (disposed f || conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      apply fibers_set_life_inv in Hm' as [[-> _]|[_ Hm']]; [congruence|].
      cbn in Hm'; unfold fupd in Hm'.
      destruct (Nat.eqb_spec m (next γ)) as [->|]; [injection Hm' as <-; auto | congruence].
    - (* ORestart *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (disposed f); [discriminate|].
      destruct (life f) as [|P acc w|acc w|]; try discriminate; injection H as <-; eapply Lift0; eauto.
  Qed.

  (** ** Ordering *)

  (** A fiber begins only when every dependency is bound by an Active
      provider; it begins Loading against exactly those provisions. *)
  Theorem begin_requires_deps (γ γ' : State) n :
    step γ (LBegin n) = Some γ' ->
    exists f w,
      fibers γ n = Some f /\ life f = Inactive Σ None /\ target γ n = Some w /\
      map fst w = fdeps Σ prog f /\
      (forall k p, In (k, p) w ->
         exists b fo, binds γ k = Some b /\ pid b = p /\
                      fibers γ (owner b) = Some fo /\ is_active (life fo) = true) /\
      fibers γ' n = Some (mkFiber Σ (fcomp f) (parent f) (disposed f)
                            (Loading Σ (body Σ (prog (fcomp f))) [] w)).
  Proof.
    intros H; cbn [step] in H.
    destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
    destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate.
    destruct (target γ n) as [w|] eqn:Ht; [|discriminate]; injection H as <-.
    destruct (resolve_spec Σ γ _ w (target_spec Σ prog γ n f w Hn Ht)) as [Hk Hv].
    exists f, w; repeat split; auto.
    - intros k p Hin; exact (visible_spec Σ γ k p (Hv k p Hin)).
    - cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity.
  Qed.

  (** Providers outlive consumers: while a fiber is installed, every
      provision it resolved exists, under the pid it resolved, and its
      provider is installed. With [fiber_step], the pid is the same for the
      whole episode. *)
  Theorem provider_outlives (γ : State) m fm k p :
    WF γ -> fibers γ m = Some fm -> In (k, p) (view_of (life fm)) ->
    exists b fo, binds γ k = Some b /\ pid b = p /\ owner b <> m /\
                 fibers γ (owner b) = Some fo /\ is_installed (life fo) = true.
  Proof.
    intros W Hm Hin.
    destruct (wf_view K_eq_dec Σ prog γ W m fm k p Hm Hin) as (b & Hb & Hp & Ho).
    destruct (wf_bind K_eq_dec Σ prog γ W k b Hb) as (fo & Hfo & Hio & _).
    exists b, fo; auto.
  Qed.

  (** A provision is withdrawn only when no other installed fiber resolves
      it. *)
  Theorem withdraw_waits (γ γ' : State) n f k p acc w z :
    WF γ -> fibers γ n = Some f -> life f = Unloading Σ (UProv Σ k p :: acc) w z ->
    step γ (LUndo n) = Some γ' ->
    forall m fm k', m <> n -> fibers γ m = Some fm -> ~ In (k', p) (view_of (life fm)).
  Proof.
    intros W Hn Hl H m fm k' Hmn Hm Hin.
    cbn [step] in H; rewrite Hn, Hl in H; cbn [undo_step] in H.
    destruct (relied Σ γ n p) eqn:Hr; [discriminate|].
    eapply (relied_false K_eq_dec Σ prog γ n p m fm k' W Hr Hm Hmn); [|exact Hin].
    exact (view_installed Σ _ _ _ Hin).
  Qed.

  (** Conversely, the withdrawal is blocked while another installed fiber
      resolves the provision. *)
  Theorem withdraw_blocked (γ : State) n f k p acc w z m fm k' :
    WF γ -> fibers γ n = Some f -> life f = Unloading Σ (UProv Σ k p :: acc) w z ->
    m <> n -> fibers γ m = Some fm -> In (k', p) (view_of (life fm)) ->
    step γ (LUndo n) = None.
  Proof.
    intros W Hn Hl Hmn Hm Hin.
    destruct (step γ (LUndo n)) as [γ'|] eqn:H; [|reflexivity].
    exfalso; exact (withdraw_waits γ γ' n f k p acc w z W Hn Hl H m fm k' Hmn Hm Hin).
  Qed.

  (** A parent passes the undo item of a spawn only after the child is gone. *)
  Theorem parent_waits_child (γ γ' : State) n f m acc w z :
    fibers γ n = Some f -> life f = Unloading Σ (USpawn Σ m :: acc) w z ->
    step γ (LUndo n) = Some γ' -> fibers γ m = None.
  Proof.
    intros Hn Hl H; cbn [step] in H; rewrite Hn, Hl in H; cbn [undo_step] in H.
    destruct (fibers γ m); [discriminate | reflexivity].
  Qed.

  (** ** Resolution coherence *)
  Lemma target_is_spec (γ : State) n w :
    target_is K_eq_dec Σ prog γ n w = true <-> target γ n = Some w.
  Proof.
    unfold target_is; destruct (target γ n) as [w'|]; split; try discriminate.
    - destruct (view_eq_dec K_eq_dec w w') as [->|]; [reflexivity | discriminate].
    - intros [= ->]; destruct (view_eq_dec K_eq_dec w w); [reflexivity | contradiction].
  Qed.

  (** Every step of a transition runs against the committed view. *)
  Theorem step_coherent (γ γ' : State) n :
    step γ (LStep n) = Some γ' ->
    exists f P acc w, fibers γ n = Some f /\ life f = Loading Σ P acc w /\
                      target γ n = Some w.
  Proof.
    intros H; cbn [step] in H.
    destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
    destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
    destruct (target_is K_eq_dec Σ prog γ n w) eqn:Ht; [|discriminate].
    exists f, P, acc, w; repeat split; auto; apply target_is_spec; exact Ht.
  Qed.

  (** Once the target differs from the committed view, a Loading fiber
      cannot step and can divert ... *)
  Theorem divert_when_changed (γ : State) n f P acc w :
    fibers γ n = Some f -> life f = Loading Σ P acc w -> target γ n <> Some w ->
    step γ (LStep n) = None /\ exists γ', step γ (LDivert n) = Some γ'.
  Proof.
    intros Hn Hl Ht.
    assert (E : target_is K_eq_dec Σ prog γ n w = false).
    { destruct (target_is _ _ _ _ _ _) eqn:E; [|reflexivity].
      exfalso; apply Ht, target_is_spec, E. }
    cbn [step]; rewrite Hn, Hl, E; split; [reflexivity | eexists; reflexivity].
  Qed.

  (** ... and an Active fiber can leave. *)
  Theorem leave_when_changed (γ : State) n f acc w :
    fibers γ n = Some f -> life f = Active Σ acc w -> target γ n <> Some w ->
    exists γ', step γ (LLeave n) = Some γ'.
  Proof.
    intros Hn Hl Ht.
    assert (E : target_is K_eq_dec Σ prog γ n w = false).
    { destruct (target_is _ _ _ _ _ _) eqn:E; [|reflexivity].
      exfalso; apply Ht, target_is_spec, E. }
    cbn [step]; rewrite Hn, Hl, E; eexists; reflexivity.
  Qed.

  (** A divert or a leave is possible only when the target has changed. *)
  Theorem divert_only_when_changed (γ γ' : State) n :
    step γ (LDivert n) = Some γ' ->
    exists f P acc w, fibers γ n = Some f /\ life f = Loading Σ P acc w /\
                      target γ n <> Some w.
  Proof.
    intros H; cbn [step] in H.
    destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
    destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
    destruct (target_is K_eq_dec Σ prog γ n w) eqn:Ht; [discriminate|].
    exists f, P, acc, w; repeat split; auto.
    intros E; apply target_is_spec in E; congruence.
  Qed.

  Theorem leave_only_when_changed (γ γ' : State) n :
    step γ (LLeave n) = Some γ' ->
    exists f acc w, fibers γ n = Some f /\ life f = Active Σ acc w /\
                    target γ n <> Some w.
  Proof.
    intros H; cbn [step] in H.
    destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
    destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
    destruct (target_is K_eq_dec Σ prog γ n w) eqn:Ht; [discriminate|].
    exists f, acc, w; repeat split; auto.
    intros E; apply target_is_spec in E; congruence.
  Qed.
End Ordering.
