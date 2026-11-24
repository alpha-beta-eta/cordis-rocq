(** * Ordering and resolution coherence (R3, second part)

    Counterparts of the paper's Theorem 70 (ordering) and Theorem 71
    (resolution coherence) for the v1 calculus.

    - Every fiber follows the lifecycle automaton of Figure 2, keeps its
      component and parent, and keeps its view while it stays installed;
      new fibers start Inactive.
    - A fiber begins only when all its dependencies are visible, i.e. bound
      by an Active provider.
    - While a fiber is installed, every provision it resolved still exists
      and its provider is installed: providers outlive consumers. The view
      fixes the provision (its pid) for the whole episode. The paper's
      clause (3) also says which fibers may move the value: a fiber that
      declares or provides the key ([value_moves]).
    - An Unloading fiber undoes nothing while another installed fiber
      resolves one of its pending provisions; a parent passes a spawn undo
      item only after the child is gone.
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
      destruct (may_step K_eq_dec Σ prog γ n P w); [|discriminate]; injection H as <-.
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
      unheld H.
      destruct (undo_step_shape γ γ' n f u acc w z H) as (γ1 & -> & E).
      assert (Hk : forall m0 fm0, fibers γ m0 = Some fm0 -> fibers γ1 m0 = Some fm0)
        by (intros m0 fm0; rewrite E; auto).
      match type of Hm' with context [set_life _ _ _ _ ?l] => apply (set_life_Same γ γ1 n f l m fm fm' Hn Hk) end; [rewrite Hl; edge | | exact Hm | exact Hm'].
      rewrite Hl; reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|[k p t g|k p|m0] acc] w z] eqn:Hl; try discriminate.
      destruct (fibers γ m0) as [g|] eqn:Hg; [|discriminate].
      unheld H; destruct (disposed g); [discriminate|]; injection H as <-.
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
      destruct (may_step K_eq_dec Σ prog γ n P w); [|discriminate]; injection H as <-.
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
      unheld H; destruct (undo_step_shape γ γ' n f u acc w z H) as (γ1 & -> & E).
      eapply Lift0; eauto.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|[k p t g|k p|m0] acc] w z]; try discriminate.
      destruct (fibers γ m0) as [g|] eqn:Hg; [|discriminate].
      unheld H; destruct (disposed g); [discriminate|]; injection H as <-.
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
    cbn [step] in H; rewrite Hn, Hl in H.
    unheld H; cbn [undo_step] in H.
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
    intros Hn Hl H; cbn [step] in H; rewrite Hn, Hl in H.
    unheld H; cbn [undo_step] in H.
    destruct (fibers γ m); [discriminate | reflexivity].
  Qed.

  (** An Unloading fiber undoes nothing, and retires no child, while any
      provision it has yet to withdraw is still resolved by another
      installed fiber: its dependents tear down against all of its effects,
      not only against the provision itself (Cordis waits for every
      dependent before starting any disposer). *)
  Theorem unload_waits (γ γ' : State) n f acc w z ℓ :
    WF γ -> fibers γ n = Some f -> life f = Unloading Σ acc w z ->
    (ℓ = LUndo n \/ ℓ = LRetireChild n) -> step γ ℓ = Some γ' ->
    forall k p m fm k', In (UProv Σ k p) acc -> m <> n -> fibers γ m = Some fm ->
    ~ In (k', p) (view_of (life fm)).
  Proof.
    intros W Hn Hl Hℓ H k p m fm k' Hu Hmn Hm Hin.
    assert (Hh : held Σ γ n acc = false).
    { destruct Hℓ as [->| ->]; cbn [step] in H; rewrite Hn, Hl in H.
      - destruct acc as [|u acc]; [discriminate|].
        unheld H; reflexivity.
      - destruct acc as [|[k0 p0 t0 g0|k0 p0|m0] acc]; try discriminate.
        destruct (fibers γ m0) as [g|]; [|discriminate].
        unheld H; reflexivity. }
    assert (Hr : relied Σ γ n p = false).
    { destruct (relied Σ γ n p) eqn:Hr; [|reflexivity].
      exfalso; apply (proj2 (not_true_iff_false _) Hh), existsb_exists.
      exists (UProv Σ k p); split; [exact Hu | exact Hr]. }
    eapply (relied_false K_eq_dec Σ prog γ n p m fm k' W Hr Hm Hmn); [|exact Hin].
    exact (view_installed Σ _ _ _ Hin).
  Qed.

  (** Conversely, both rules are blocked while such a dependent remains. *)
  Theorem unload_blocked (γ : State) n f acc w z k p m fm k' :
    WF γ -> fibers γ n = Some f -> life f = Unloading Σ acc w z ->
    In (UProv Σ k p) acc -> m <> n -> fibers γ m = Some fm ->
    In (k', p) (view_of (life fm)) ->
    step γ (LUndo n) = None /\ step γ (LRetireChild n) = None.
  Proof.
    intros W Hn Hl Hu Hmn Hm Hin.
    split.
    - destruct (step γ (LUndo n)) as [γ'|] eqn:H; [|reflexivity]; exfalso.
      exact (unload_waits γ γ' n f acc w z (LUndo n) W Hn Hl (or_introl eq_refl) H
               k p m fm k' Hu Hmn Hm Hin).
    - destruct (step γ (LRetireChild n)) as [γ'|] eqn:H; [|reflexivity]; exfalso.
      exact (unload_waits γ γ' n f acc w z (LRetireChild n) W Hn Hl (or_intror eq_refl) H
               k p m fm k' Hu Hmn Hm Hin).
  Qed.

  (** ** Resolution coherence *)
  Lemma target_is_spec (γ : State) n w :
    target_is K_eq_dec Σ prog γ n w = true <-> target γ n = Some w.
  Proof.
    unfold target_is; destruct (target γ n) as [w'|]; split; try discriminate.
    - destruct (view_eq_dec K_eq_dec w w') as [->|]; [reflexivity | discriminate].
    - intros [= ->]; destruct (view_eq_dec K_eq_dec w w); [reflexivity | contradiction].
  Qed.

  (** Every step of a transition runs against the committed view [w],
      whatever the target has become since; only the finishing step needs
      the target to agree with it. An iteration may thus land after the
      target has turned (the paper's inertial host, §4.4). *)
  Theorem step_coherent (γ γ' : State) n :
    step γ (LStep n) = Some γ' ->
    exists f P acc w, fibers γ n = Some f /\ life f = Loading Σ P acc w /\
                      γ' = load_step K_eq_dec Σ prog γ n f P acc w /\
                      (P = PDone -> target γ n = Some w).
  Proof.
    intros H; cbn [step] in H.
    destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
    destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
    destruct (may_step K_eq_dec Σ prog γ n P w) eqn:Ht; [|discriminate].
    injection H as <-.
    exists f, P, acc, w; repeat split; auto.
    intros ->; apply target_is_spec; exact Ht.
  Qed.

  (** Once the target differs from the committed view, a Loading fiber
      can divert, and cannot finish (it may still land the iterations it
      has left) ... *)
  Theorem divert_when_changed (γ : State) n f P acc w :
    fibers γ n = Some f -> life f = Loading Σ P acc w -> target γ n <> Some w ->
    (P = PDone -> step γ (LStep n) = None) /\ exists γ', step γ (LDivert n) = Some γ'.
  Proof.
    intros Hn Hl Ht.
    assert (E : target_is K_eq_dec Σ prog γ n w = false).
    { destruct (target_is _ _ _ _ _ _) eqn:E; [|reflexivity].
      exfalso; apply Ht, target_is_spec, E. }
    cbn [step]; rewrite Hn, Hl, E; split; [intros ->; cbn; rewrite E; reflexivity | eexists; reflexivity].
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
  (** ** Who moves a binding's value (the paper's Theorem 70(3))

      The paper's clause (3) says that, during a dependent's episode, the
      provider's entry at the key exists ([provider_outlives]) and moves only
      by operations at that key of fibers declaring it. Here a fiber may
      operate at a key it declares or provides, so the counterpart reads:
      across a step that keeps a binding's pid, its value moves only by an
      [L-Step] or [L-Undo] of a fiber that declares or provides the key
      ([value_moves]). The undo case rests on an invariant: an operation
      undo item sits only in the accumulator of a fiber that declares or
      provides its key ([Decl], [decl_reachable]). *)
  Definition Declares (f : Fiber) (k : K) : Prop :=
    kmem K_eq_dec k (deps Σ (prog (fcomp f))) = true \/
    kmem K_eq_dec k (provs Σ (prog (fcomp f))) = true.

  Definition DeclF (f : Fiber) : Prop :=
    forall k p t g, In (UOp Σ k p t g) (acc_of (life f)) -> Declares f k.

  Definition Decl (γ : State) : Prop :=
    forall m f, fibers γ m = Some f -> DeclF f.

  Lemma decl_init : Decl (@init K Σ C).
  Proof. intros m f H; discriminate H. Qed.

  Lemma decl_relife (γ γ1 : State) n f (l : Life) :
    Decl γ -> fibers γ n = Some f ->
    (forall m fm, fibers γ1 m = Some fm ->
       fibers γ m = Some fm \/ exists z, life fm = Inactive Σ z) ->
    (forall k p t g, In (UOp Σ k p t g) (acc_of l) ->
       In (UOp Σ k p t g) (acc_of (life f)) \/ Declares f k) ->
    Decl (set_life Σ γ1 n f l).
  Proof.
    intros D Hn Hlk Hl m fm H.
    apply fibers_set_life_inv in H as [[-> ->]|[_ H]].
    - intros k p t g I; cbn in I.
      destruct (Hl k p t g I) as [I'|Hd]; [exact (D n f Hn k p t g I') | exact Hd].
    - destruct (Hlk m fm H) as [H0|[z Hz]]; [exact (D m fm H0)|].
      intros k p t g I; rewrite Hz in I; destruct I.
  Qed.

  Lemma decl_refiber (γ : State) n f b :
    Decl γ -> fibers γ n = Some f ->
    Decl (set_fiber Σ γ n (mkFiber Σ (fcomp f) (parent f) b (life f))).
  Proof.
    intros D Hn m fm H; apply fibers_set_fiber_inv in H as [[-> ->]|[_ H]].
    - intros k p t g I; exact (D n f Hn k p t g I).
    - exact (D m fm H).
  Qed.

  (** An operation of [n] at [k] resolves only if [n] declares [k] or owns
      its binding, and an owner provides the key. *)
  Lemma resolved_declares (γ : State) n f k :
    WF γ -> fibers γ n = Some f ->
    (kmem K_eq_dec k (deps Σ (prog (fcomp f))) = false ->
     exists b, binds γ k = Some b /\ owner b = n) ->
    Declares f k.
  Proof.
    intros W Hn H; unfold Declares.
    destruct (kmem K_eq_dec k (deps Σ (prog (fcomp f)))) eqn:Hd; [left; reflexivity|right].
    destruct (H eq_refl) as (b & Hb & Ho).
    destruct (wf_bind K_eq_dec Σ prog γ W k b Hb) as (fo & Hfo & _ & Hk & _).
    rewrite Ho, Hn in Hfo; injection Hfo as <-; exact Hk.
  Qed.

  Ltac rp_declares W Hn Hrp :=
    apply (resolved_declares _ _ _ _ W Hn); intros Hd; rewrite Hd in Hrp; cbv beta iota in Hrp;
    lazymatch type of Hrp with
    | (match binds ?g ?k with _ => _ end) = Some _ =>
        destruct (binds g k) as [b0|] eqn:Hb0; [|discriminate Hrp]
    | _ => idtac
    end;
    lazymatch type of Hrp with
    | (if Nat.eqb (owner ?b1) ?n then _ else _) = Some _ =>
        destruct (Nat.eqb_spec (owner b1) n) as [Ho|]; [|discriminate Hrp];
        exists b1; split; [assumption | exact Ho]
    end.

  Theorem decl_step (γ γ' : State) ℓ :
    WF γ -> Decl γ -> step γ ℓ = Some γ' -> Decl γ'.
  Proof.
    intros W D H.
    assert (Same0 : forall m fm, fibers γ m = Some fm ->
              fibers γ m = Some fm \/ exists z, life fm = Inactive Σ z)
      by (intros; left; assumption).
    assert (Fresh : forall c q m fm,
              fibers (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ)
                 (Some (mkFiber Σ c q false (Inactive Σ None)))))) m = Some fm ->
              fibers γ m = Some fm \/ exists z, life fm = Inactive Σ z).
    { intros c q m fm Hm; cbn in Hm; unfold fupd in Hm.
      destruct (Nat.eqb m (next γ));
        [injection Hm as <-; right; eexists; reflexivity | left; exact Hm]. }
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [step] in H.
    - (* OInsert *)
      destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      intros m fm Hm; destruct (Fresh c None m fm Hm) as [H0|[z Hz]]; [exact (D m fm H0)|].
      intros k p t g I; rewrite Hz in I; destruct I.
    - (* ODispose *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate]; injection H as <-.
      exact (decl_refiber γ n f true D Hn).
    - (* OReset *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate; injection H as <-.
      apply (decl_relife γ γ n f); [exact D | exact Hn | exact Same0 | intros k p t g []].
    - (* LBegin *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (target γ n); [|discriminate]; injection H as <-.
      apply (decl_relife γ γ n f); [exact D | exact Hn | exact Same0 | intros k p t g []].
    - (* LStep *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [|P0 acc w| |] eqn:Hl; try discriminate.
      destruct (may_step K_eq_dec Σ prog γ n P0 w); [|discriminate]; injection H as <-.
      assert (Keep : forall γ1 (l : Life),
                (forall m fm, fibers γ1 m = Some fm ->
                   fibers γ m = Some fm \/ exists z, life fm = Inactive Σ z) ->
                (forall k p t g, In (UOp Σ k p t g) (acc_of l) ->
                   In (UOp Σ k p t g) acc \/ Declares f k) ->
                Decl (set_life Σ γ1 n f l)).
      { intros γ1 l Hlk Hit; apply (decl_relife γ γ1 n f l D Hn Hlk).
        intros k p t g I; rewrite Hl; exact (Hit k p t g I). }
      destruct P0 as [| |k a κ|k s P'|c P']; cbn [load_step].
      + apply Keep; [exact Same0 | intros k p t g I; left; exact I].
      + apply Keep; [exact Same0 | intros k p t g I; left; exact I].
      + match goal with |- Decl (match ?x with _ => _ end) => destruct x as [p|] eqn:Hrp end.
        2: { apply Keep; [exact Same0 | intros k0 p0 t0 g0 I; left; exact I]. }
        destruct (binds γ k) as [b|] eqn:Hb.
        2: { apply Keep; [exact Same0 | intros k0 p0 t0 g0 I; left; exact I]. }
        destruct (Nat.eqb (pid b) p).
        2: { apply Keep; [exact Same0 | intros k0 p0 t0 g0 I; left; exact I]. }
        destruct (run a (next γ) (bst Σ b)) as [[[s' g] o]|].
        * apply Keep; [exact Same0|].
          intros k0 p0 t0 g0 [E|I]; [|left; exact I].
          injection E as E1 _ _ _; subst k0; right.
          rp_declares W Hn Hrp.
        * apply Keep; [exact Same0 | intros k0 p0 t0 g0 I; left; exact I].
      + destruct (kmem K_eq_dec k (provs Σ (prog (fcomp f)))).
        2: { apply Keep; [exact Same0 | intros k0 p0 t0 g0 I; left; exact I]. }
        destruct (binds γ k).
        { apply Keep; [exact Same0 | intros k0 p0 t0 g0 I; left; exact I]. }
        apply Keep; [exact Same0 | intros k0 p0 t0 g0 [E|I]; [discriminate E | left; exact I]].
      + destruct (conflict K_eq_dec Σ prog γ c).
        { apply Keep; [exact Same0 | intros k0 p0 t0 g0 I; left; exact I]. }
        apply Keep;
          [exact (Fresh c (Some n)) | intros k0 p0 t0 g0 [E|I]; [discriminate E | left; exact I]].
    - (* LDivert *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [|P0 acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [discriminate|]; injection H as <-.
      apply (decl_relife γ γ n f); [exact D | exact Hn | exact Same0 |].
      intros k p t g I; left; rewrite Hl; exact I.
    - (* LLeave *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [discriminate|]; injection H as <-.
      apply (decl_relife γ γ n f); [exact D | exact Hn | exact Same0 |].
      intros k p t g I; left; rewrite Hl; exact I.
    - (* LUndo *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      apply undo_step_shape in H as (γ1 & -> & E).
      apply (decl_relife γ γ1 n f); [exact D | exact Hn | |].
      + intros m fm Hm; left; rewrite <- E; exact Hm.
      + intros k p t g I; left; rewrite Hl; right; exact I.
    - (* LRetireChild *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|[k0 p0 t0 g0|k0 p0|m0] acc] w z] eqn:Hl; try discriminate.
      destruct (fibers γ m0) as [g|] eqn:Hg; [|discriminate].
      unheld H.
      destruct (disposed g); [discriminate|]; injection H as <-.
      exact (decl_refiber γ m0 g true D Hg).
    - (* LUnloaded *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate; injection H as <-.
      apply (decl_relife γ γ n f); [exact D | exact Hn | exact Same0 | intros k p t g []].
    - (* LRemove *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [z| | |] eqn:Hl; try discriminate.
      destruct (disposed f && negb (has_child Σ γ n)); [|discriminate]; injection H as <-.
      intros m fm Hm; cbn in Hm; unfold fupd in Hm.
      destruct (Nat.eqb m n); [discriminate | exact (D m fm Hm)].
    - (* OReact *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (nth_error (reacts Σ (prog (fcomp f))) i) as [c|]; [|discriminate].
      destruct (disposed f || conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      apply (decl_relife γ _ n f); [exact D | exact Hn | exact (Fresh c (Some n)) |].
      intros k p t g [E|I]; [discriminate E | left; rewrite Hl; exact I].
    - (* ORestart *)
      apply (restart_shape K_eq_dec Σ prog) in H as (f & acc & w & Hn & _ & [P Hl] & ->).
      apply (decl_relife γ γ n f); [exact D | exact Hn | exact Same0 |].
      intros k p t g I; left; destruct Hl as [Hl|Hl]; rewrite Hl; exact I.
  Qed.

  Corollary decl_reachable (γ : State) (ls : list Label) :
    run_labels K_eq_dec Σ prog (@init K Σ C) ls = Some γ -> Decl γ.
  Proof.
    assert (G : forall γ0 ls γ, WF γ0 -> Decl γ0 ->
              run_labels K_eq_dec Σ prog γ0 ls = Some γ -> Decl γ).
    { intros γ0 ls0; revert γ0; induction ls0 as [|ℓ ls0 IH]; cbn; intros γ0 γ1 W0 D0 H.
      - injection H as <-; exact D0.
      - destruct (step γ0 ℓ) as [γ0'|] eqn:Hs; [|discriminate].
        exact (IH γ0' γ1 (preservation K_eq_dec Σ prog γ0 γ0' ℓ W0 Hs)
                 (decl_step γ0 γ0' ℓ W0 D0 Hs) H). }
    intros H; exact (G _ ls γ (wf_init K_eq_dec Σ prog) decl_init H).
  Qed.

  (** A binding that keeps its pid across a step either keeps its value or
      is moved by an [L-Step] or [L-Undo] of a fiber that declares or
      provides its key. *)
  Theorem value_moves (γ γ' : State) ℓ k b b' :
    WF γ -> Decl γ -> step γ ℓ = Some γ' ->
    binds γ k = Some b -> binds γ' k = Some b' -> pid b' = pid b ->
    b' = b \/
    exists n f, fibers γ n = Some f /\ (ℓ = LStep n \/ ℓ = LUndo n) /\ Declares f k.
  Proof.
    intros W D H Hb Hb' Hp.
    assert (Keep : binds γ k = Some b' -> b' = b \/
              exists n f, fibers γ n = Some f /\ (ℓ = LStep n \/ ℓ = LUndo n) /\ Declares f k).
    { intros E; left; rewrite Hb in E; injection E as <-; reflexivity. }
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [step] in H.
    - destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      apply Keep; exact Hb'.
    - destruct (fibers γ n) as [f|]; [|discriminate]; injection H as <-; apply Keep; exact Hb'.
    - destruct (fibers γ n) as [f|]; [|discriminate].
      destruct (life f) as [[z|]| | |]; try discriminate; injection H as <-; apply Keep; exact Hb'.
    - destruct (fibers γ n) as [f|]; [|discriminate].
      destruct (life f) as [[z|]| | |]; try discriminate.
      destruct (target γ n); [|discriminate]; injection H as <-; apply Keep; exact Hb'.
    - (* LStep *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [|P0 acc w| |] eqn:Hl; try discriminate.
      destruct (may_step K_eq_dec Σ prog γ n P0 w); [|discriminate]; injection H as <-.
      destruct P0 as [| |k0 a κ|k0 s P'|c P']; cbn [load_step] in Hb' |- *.
      + apply Keep; exact Hb'.
      + apply Keep; exact Hb'.
      + match type of Hb' with context [match ?x with Some _ => _ | None => _ end] =>
          match x with binds _ _ => fail 1 | _ => destruct x as [p|] eqn:Hrp end end.
        2: { apply Keep; exact Hb'. }
        destruct (binds γ k0) as [b0|] eqn:Hb0.
        2: { apply Keep; exact Hb'. }
        destruct (Nat.eqb (pid b0) p).
        2: { apply Keep; exact Hb'. }
        destruct (run a (next γ) (bst Σ b0)) as [[[s' g] o]|].
        * cbn in Hb'; unfold bupd, keqb in Hb'.
          destruct (K_eq_dec k k0) as [->|Ne].
          -- right; exists n, f; split; [exact Hn | split; [left; reflexivity|]].
             rp_declares W Hn Hrp.
          -- apply Keep; exact Hb'.
        * apply Keep; exact Hb'.
      + destruct (kmem K_eq_dec k0 (provs Σ (prog (fcomp f)))).
        2: { apply Keep; exact Hb'. }
        destruct (binds γ k0) as [b0|] eqn:Hb0.
        { apply Keep; exact Hb'. }
        cbn in Hb'; unfold bupd, keqb in Hb'.
        destruct (K_eq_dec k k0) as [->|Ne]; [congruence | apply Keep; exact Hb'].
      + destruct (conflict K_eq_dec Σ prog γ c); apply Keep; exact Hb'.
    - destruct (fibers γ n) as [f|]; [|discriminate].
      destruct (life f) as [|P0 acc w| |]; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [discriminate|]; injection H as <-.
      apply Keep; exact Hb'.
    - destruct (fibers γ n) as [f|]; [|discriminate].
      destruct (life f) as [| |acc w|]; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [discriminate|]; injection H as <-.
      apply Keep; exact Hb'.
    - (* LUndo *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      destruct u as [k0 p0 t0 g0|k0 p0|m0]; cbn [undo_step] in H.
      + destruct (binds γ k0) as [b0|] eqn:Hb0.
        2: { injection H as <-; apply Keep; exact Hb'. }
        destruct (Nat.eqb (pid b0) p0).
        2: { injection H as <-; apply Keep; exact Hb'. }
        injection H as <-; cbn in Hb'; unfold bupd, keqb in Hb'.
        destruct (K_eq_dec k k0) as [->|Ne].
        * right; exists n, f; split; [exact Hn | split; [right; reflexivity|]].
          apply (D n f Hn k0 p0 t0 g0); rewrite Hl; left; reflexivity.
        * apply Keep; exact Hb'.
      + destruct (relied Σ γ n p0); [discriminate|].
        destruct (binds γ k0) as [b0|] eqn:Hb0.
        2: { injection H as <-; apply Keep; exact Hb'. }
        destruct (Nat.eqb (pid b0) p0).
        2: { injection H as <-; apply Keep; exact Hb'. }
        injection H as <-; cbn in Hb'; unfold bupd, keqb in Hb'.
        destruct (K_eq_dec k k0) as [->|Ne]; [discriminate Hb' | apply Keep; exact Hb'].
      + destruct (fibers γ m0); [discriminate|]; injection H as <-; apply Keep; exact Hb'.
    - destruct (fibers γ n) as [f|]; [|discriminate].
      destruct (life f) as [| | |[|[k0 p0 t0 g0|k0 p0|m0] acc] w z]; try discriminate.
      destruct (fibers γ m0) as [g|]; [|discriminate].
      unheld H.
      destruct (disposed g); [discriminate|]; injection H as <-; apply Keep; exact Hb'.
    - destruct (fibers γ n) as [f|]; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z]; try discriminate; injection H as <-.
      apply Keep; exact Hb'.
    - destruct (fibers γ n) as [f|]; [|discriminate].
      destruct (life f) as [z| | |]; try discriminate.
      destruct (disposed f && negb (has_child Σ γ n)); [|discriminate]; injection H as <-.
      apply Keep; exact Hb'.
    - destruct (fibers γ n) as [f|]; [|discriminate].
      destruct (life f) as [| |acc w|]; try discriminate.
      destruct (nth_error (reacts Σ (prog (fcomp f))) i) as [c|]; [|discriminate].
      destruct (disposed f || conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      apply Keep; exact Hb'.
    - apply (restart_shape K_eq_dec Σ prog) in H as (f & acc & w & Hn & _ & _ & ->).
      apply Keep; exact Hb'.
  Qed.
End Ordering.
