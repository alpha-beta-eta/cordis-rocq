(** * The admission queue (errors/DESIGN.md, section 5.1)

    The core refuses [O-Insert] of a component whose provisions meet those
    of a fiber still in the table, even one that is retired and will be
    removed. A conflict with a retired fiber goes away by itself, so it
    should be waited out, not refused (principle P2).

    A queued component is not a fiber yet. The state gets a FIFO queue of
    (ticket, component):

    - [QIns c]: refused if [c] meets a fiber that is not retired, or a
      component already queued; otherwise [c] joins the queue. Queued
      components count as claimants, so they are pairwise disjoint and
      disjoint from every live fiber.
    - [QAdmit] (a lifecycle rule): the head of the queue is inserted with
      the core [O-Insert], once that applies. Names are drawn at this
      moment, exactly as in the core.
    - [QCancel t]: the orchestrator withdraws a queued component.
    - [QCore ℓ]: every core rule except [O-Insert].

    Results:
    - [qstep_core], [qrun_core]: every step either leaves the core state
      alone or is a core step ([QAdmit] is the core [O-Insert]); so every
      execution is a core execution, with the same names, and safety
      carries over ([qwf_reachable]).
    - [qtermination]: lifecycle steps (the core's and [QAdmit]) do not go
      on forever (queue length, then the core measure).
    - [qquiet_empty]: a quiet reachable state has an empty queue, when
      spawned components provide nothing ([HKids]).
    - the cordiverse/cordis#358 sequence has a single outcome under the
      queue: the new provider waits, then everything is Active
      ([q358_blocked], [q358_obs]).

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service Calculus Preservation Progress Termination Recovery.
Import ListNotations.

Section Queue.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).
  Local Notation Label := (@Label C).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation cprovs c := (provs Σ (prog c)).
  Local Notation overlaps := (overlaps K_eq_dec).

  (** ** State and rules *)
  Record QState : Type := mkQ {
    core : State;
    queue : list (nat * C);
    ticket : nat
  }.

  Definition qinit : QState := mkQ (@init K Σ C) [] 0.

  Inductive QLabel : Type :=
  | QIns (c : C)
  | QCancel (t : nat)
  | QAdmit
  | QCore (ℓ : Label).

  (** [c] meets a fiber that is not retired. *)
  Definition live_conflict (γ : State) (c : C) : bool :=
    existsb (fun m =>
      match fibers Σ γ m with
      | Some f => negb (disposed Σ f) && overlaps (cprovs c) (cprovs (comp Σ f))
      | None => false
      end) (names Σ γ).

  (** [c] meets a queued component. *)
  Definition qconflict (q : list (nat * C)) (c : C) : bool :=
    existsb (fun e => overlaps (cprovs c) (cprovs (snd e))) q.

  Definition qstep (qs : QState) (ℓ : QLabel) : option QState :=
    match ℓ with
    | QIns c =>
        if live_conflict (core qs) c || qconflict (queue qs) c then None
        else Some (mkQ (core qs) (queue qs ++ [(ticket qs, c)]) (S (ticket qs)))
    | QCancel t =>
        if existsb (fun e => Nat.eqb (fst e) t) (queue qs)
        then Some (mkQ (core qs) (filter (fun e => negb (Nat.eqb (fst e) t)) (queue qs)) (ticket qs))
        else None
    | QAdmit =>
        match queue qs with
        | (_, c) :: q =>
            match step (core qs) (OInsert c) with
            | Some γ' => Some (mkQ γ' q (ticket qs))
            | None => None
            end
        | [] => None
        end
    | QCore (OInsert _) => None
    | QCore ℓ =>
        match step (core qs) ℓ with
        | Some γ' => Some (mkQ γ' (queue qs) (ticket qs))
        | None => None
        end
    end.

  Fixpoint qrun_labels (qs : QState) (ls : list QLabel) : option QState :=
    match ls with
    | [] => Some qs
    | ℓ :: ls' => match qstep qs ℓ with Some qs' => qrun_labels qs' ls' | None => None end
    end.

  (** ** Correspondence with the core *)

  (** The core label a step performs, if any. *)
  Definition qcore_label (qs : QState) (ℓ : QLabel) : option Label :=
    match ℓ with
    | QIns _ | QCancel _ => None
    | QAdmit => match queue qs with (_, c) :: _ => Some (OInsert c) | [] => None end
    | QCore ℓ => Some ℓ
    end.

  Lemma qstep_core (qs qs' : QState) ℓ :
    qstep qs ℓ = Some qs' ->
    match qcore_label qs ℓ with
    | None => core qs' = core qs
    | Some ℓ' => step (core qs) ℓ' = Some (core qs')
    end.
  Proof.
    destruct ℓ as [c|t| |ℓ]; cbn [qstep qcore_label].
    - destruct (_ || _); [discriminate | intros [= <-]; reflexivity].
    - destruct (existsb _ _); [intros [= <-]; reflexivity | discriminate].
    - destruct (queue qs) as [|[t c] q]; [discriminate|].
      destruct (step (core qs) (OInsert c)); [intros [= <-]; reflexivity | discriminate].
    - destruct ℓ; try discriminate;
        (destruct (step (core qs) _); [intros [= <-]; reflexivity | discriminate]).
  Qed.

  Theorem qrun_core (qs0 qs : QState) ls :
    qrun_labels qs0 ls = Some qs ->
    exists ls', run_labels K_eq_dec Σ prog (core qs0) ls' = Some (core qs).
  Proof.
    revert qs0; induction ls as [|ℓ ls IH]; cbn; intros qs0 H.
    - injection H as <-; exists []; reflexivity.
    - destruct (qstep qs0 ℓ) as [qs1|] eqn:Hs; [|discriminate].
      destruct (IH qs1 H) as [ls' Hr].
      pose proof (qstep_core qs0 qs1 ℓ Hs) as Hc.
      destruct (qcore_label qs0 ℓ) as [ℓ'|].
      + exists (ℓ' :: ls'); cbn; rewrite Hc; exact Hr.
      + exists ls'; rewrite <- Hc; exact Hr.
  Qed.

  Corollary qwf_reachable (qs : QState) ls :
    qrun_labels qinit ls = Some qs -> WF K_eq_dec Σ prog (core qs).
  Proof.
    intros H; destruct (qrun_core _ _ ls H) as [ls' Hr].
    exact (wf_reachable K_eq_dec Σ prog _ ls' Hr).
  Qed.

  (** A core lifecycle label goes through unchanged. *)
  Lemma qcore_lifecycle (qs qs' : QState) n ℓ :
    In ℓ (lifecycle_labels n) -> qstep qs (QCore ℓ) = Some qs' ->
    step (core qs) ℓ = Some (core qs') /\ queue qs' = queue qs.
  Proof.
    intros Hin H; cbn in Hin.
    repeat (destruct Hin as [<-|Hin];
            [cbn [qstep] in H; destruct (step (core qs) _); [injection H as <-; auto | discriminate]|]).
    destruct Hin.
  Qed.

  Lemma qcore_lifecycle_back (qs : QState) n ℓ γ' :
    In ℓ (lifecycle_labels n) -> step (core qs) ℓ = Some γ' ->
    qstep qs (QCore ℓ) = Some (mkQ γ' (queue qs) (ticket qs)).
  Proof.
    intros Hin H; cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [qstep]; rewrite H; reflexivity|]).
    destruct Hin.
  Qed.

  (** ** Termination *)
  Section Term.
    Variable Kb : nat.
    Hypothesis HK : forall c, Bounded Σ Kb (body Σ (prog c)).
    Variable rank : C -> nat.
    Variable Rb : nat.
    Hypothesis Hrank : forall c c', Above Σ prog c c' -> rank c < rank c'.
    Hypothesis Hbnd : forall c, rank c <= Rb.

    Local Notation TInv := (TInv K_eq_dec Σ prog Kb).

    Definition qLStepRel (qs' qs : QState) : Prop :=
      TInv (core qs) /\
      (qstep qs QAdmit = Some qs' \/
       exists n ℓ, In ℓ (lifecycle_labels n) /\ qstep qs (QCore ℓ) = Some qs').

    Lemma qacc_len k : forall qs, length (queue qs) = k -> TInv (core qs) -> Acc qLStepRel qs.
    Proof.
      induction k as [k IHk] using (well_founded_induction Wf_nat.lt_wf).
      assert (G : forall γ, Acc (LStepRel K_eq_dec Σ prog Kb) γ ->
                  forall qs, core qs = γ -> length (queue qs) = k -> TInv γ -> Acc qLStepRel qs).
      { intros γ A; induction A as [γ _ IHA]; intros qs Hc Hk I.
        constructor; intros qs' [_ [Ha|(n & ℓ & Hin & Hs)]].
        - cbn [qstep] in Ha.
          destruct (queue qs) as [|[t c] q] eqn:Hq; [discriminate|].
          destruct (step (core qs) (OInsert c)) as [γ'|] eqn:Hs; [|discriminate].
          injection Ha as <-.
          apply (IHk (length q)); [cbn in Hk; lia | reflexivity |].
          exact (tinv_step K_eq_dec Σ prog Kb HK _ _ _ (eq_ind _ _ I _ (eq_sym Hc)) Hs).
        - destruct (qcore_lifecycle qs qs' n ℓ Hin Hs) as [Hs' Hq'].
          rewrite Hc in Hs'.
          apply (IHA (core qs')).
          + split; [exact I|]; exists n, ℓ; auto.
          + reflexivity.
          + rewrite Hq'; exact Hk.
          + exact (tinv_step K_eq_dec Σ prog Kb HK _ _ _ I Hs'). }
      intros qs Hk I.
      exact (G (core qs) (termination K_eq_dec Σ prog Kb HK rank Rb Hrank Hbnd _ I)
               qs eq_refl Hk I).
    Qed.

    Theorem qtermination (qs : QState) : TInv (core qs) -> Acc qLStepRel qs.
    Proof. apply (qacc_len (length (queue qs))); reflexivity. Qed.

    Corollary qtermination_reachable (qs : QState) ls :
      qrun_labels qinit ls = Some qs -> Acc qLStepRel qs.
    Proof.
      intros H; apply qtermination.
      destruct (qrun_core _ _ ls H) as [ls' Hr].
      assert (G : forall γ0 ls γ, TInv γ0 ->
                  run_labels K_eq_dec Σ prog γ0 ls = Some γ -> TInv γ).
      { intros γ0 ls0; revert γ0; induction ls0 as [|ℓ ls0 IH]; cbn; intros γ0 γ1 I0 Hr0.
        - injection Hr0 as <-; exact I0.
        - destruct (step γ0 ℓ) as [γ0'|] eqn:Hs; [|discriminate].
          exact (IH γ0' γ1 (tinv_step K_eq_dec Σ prog Kb HK γ0 γ0' ℓ I0 Hs) Hr0). }
      exact (G _ ls' _ (tinv_init K_eq_dec Σ prog Kb) Hr).
    Qed.

    (** ** A quiet state has an empty queue *)

    (** Spawned components provide nothing. (The design asks only that their
        provisions be statically disjoint from every other component's; this
        file proves the special case.) *)
    Hypothesis HKids : forall c c', Spawns Σ prog c c' -> cprovs c' = [].

    (** Queued components are pairwise disjoint. *)
    Fixpoint QDisj (q : list (nat * C)) : Prop :=
      match q with
      | [] => True
      | e :: q' => (forall e', In e' q' -> overlaps (cprovs (snd e)) (cprovs (snd e')) = false) /\
                   QDisj q'
      end.

    (** No queued component meets a fiber that is not retired. *)
    Definition QLive (qs : QState) : Prop :=
      forall e x fx, In e (queue qs) -> fibers Σ (core qs) x = Some fx -> disposed Σ fx = false ->
        overlaps (cprovs (snd e)) (cprovs (comp Σ fx)) = false.

    Definition QInv (qs : QState) : Prop :=
      TInv (core qs) /\ QDisj (queue qs) /\ QLive qs.

    Lemma overlaps_nil_r (l : list K) : overlaps l [] = false.
    Proof. induction l; cbn; auto. Qed.

    Lemma qdisj_app (q : list (nat * C)) e :
      QDisj q -> (forall e', In e' q -> overlaps (cprovs (snd e')) (cprovs (snd e)) = false) ->
      QDisj (q ++ [e]).
    Proof.
      induction q as [|e0 q IH]; cbn; intros D H.
      - split; [intros _ []|exact I].
      - destruct D as [D0 D]; split.
        + intros e' Hin; apply in_app_or in Hin as [Hin|[<-|[]]]; [exact (D0 e' Hin)|].
          exact (H e0 (or_introl eq_refl)).
        + apply IH; [exact D | intros e' Hin; exact (H e' (or_intror Hin))].
    Qed.

    Lemma qdisj_filter (q : list (nat * C)) p : QDisj q -> QDisj (filter p q).
    Proof.
      induction q as [|e q IH]; cbn; [auto|]; intros [D0 D].
      destruct (p e); cbn; [split|]; auto.
      intros e' Hin; apply filter_In in Hin as [Hin _]; exact (D0 e' Hin).
    Qed.

    (** A fiber that is not retired after a core step that is not
        [O-Insert]: it was there before, with the same component and not
        retired, or it is a spawned child. *)
    Lemma live_after (γ γ' : State) ℓ x fx' :
      TInv γ -> step γ ℓ = Some γ' -> (forall c, ℓ <> OInsert c) ->
      fibers Σ γ' x = Some fx' -> disposed Σ fx' = false ->
      (exists fx, fibers Σ γ x = Some fx /\ comp Σ fx = comp Σ fx' /\ disposed Σ fx = false) \/
      cprovs (comp Σ fx') = [].
    Proof.
      intros I H Hno Hx Hd.
      (* Lifecycle labels: the core's [Effects]. *)
      assert (LC : forall n, In ℓ (lifecycle_labels n) ->
                   (exists fx, fibers Σ γ x = Some fx /\ comp Σ fx = comp Σ fx' /\ disposed Σ fx = false) \/
                   cprovs (comp Σ fx') = []).
      { intros n Hin.
        destruct (fibers Σ γ n) as [fn|] eqn:Hn;
          [|rewrite (step_absent K_eq_dec Σ prog γ n ℓ Hn Hin) in H; discriminate].
        destruct (lstep_effects K_eq_dec Σ prog Kb rank Hrank γ γ' n ℓ fn I Hin H Hn)
          as (E1 & E2 & E3 & _ & _).
        destruct (fibers Σ γ x) as [fx|] eqn:Hx0.
        - destruct (Nat.eq_dec x n) as [->|Hxn].
          + rewrite Hn in Hx0; injection Hx0 as <-.
            destruct (E3 fx' Hx) as [Hc Hdd]; left; exists fn; repeat split; congruence.
          + destruct (E1 x fx Hxn Hx0) as [Hs|[Hs _]]; rewrite Hs in Hx; injection Hx as <-.
            * left; eauto.
            * cbn in Hd; discriminate.
        - destruct (E2 x fx' Hx0 Hx) as [_ Hsp].
          right; apply (HKids (comp Σ fn)); left; exact Hsp. }
      destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n];
        try (apply (LC n); cbn; tauto).
      - exfalso; exact (Hno c eq_refl).
      - (* ODispose *)
        cbn [step] in H; destruct (fibers Σ γ n) as [fn|] eqn:Hn; [|discriminate].
        injection H as <-; unfold set_fiber, with_fibers, fupd in Hx; cbn in Hx.
        destruct (Nat.eqb_spec x n) as [->|]; [injection Hx as <-; cbn in Hd; discriminate|].
        left; eauto.
      - (* OReset *)
        cbn [step] in H; destruct (fibers Σ γ n) as [fn|] eqn:Hn; [|discriminate].
        destruct (life Σ fn) as [[z|]| | |]; try discriminate; injection H as <-.
        rewrite fibers_set_life in Hx; destruct (Nat.eqb_spec x n) as [->|].
        + injection Hx as <-; left; exists fn; cbn in *; auto.
        + left; eauto.
      - (* OReact *)
        cbn [step] in H; destruct (fibers Σ γ n) as [fn|] eqn:Hn; [|discriminate].
        destruct (life Σ fn) as [| |acc w|]; try discriminate.
        destruct (nth_error (reacts Σ (prog (comp Σ fn))) i) as [c|] eqn:Hc; [|discriminate].
        destruct (disposed Σ fn || conflict K_eq_dec Σ prog γ c); [discriminate|].
        injection H as <-.
        rewrite fibers_set_life in Hx; destruct (Nat.eqb_spec x n) as [->|].
        + injection Hx as <-; left; exists fn; cbn in *; auto.
        + cbn in Hx; unfold fupd in Hx; destruct (Nat.eqb_spec x (next Σ γ)) as [->|].
          * injection Hx as <-; right; cbn; apply (HKids (comp Σ fn)); right.
            exact (nth_error_In _ _ Hc).
          * left; eauto.
      - (* ORestart *)
        apply restart_shape in H as (fn & acc & w & Hn & _ & _ & ->).
        rewrite fibers_set_life in Hx; destruct (Nat.eqb_spec x n) as [->|].
        + injection Hx as <-; left; exists fn; cbn in *; auto.
        + left; eauto.
    Qed.

    Lemma qlive_core (qs : QState) ℓ γ' :
      TInv (core qs) -> QLive qs -> step (core qs) ℓ = Some γ' -> (forall c, ℓ <> OInsert c) ->
      QLive (mkQ γ' (queue qs) (ticket qs)).
    Proof.
      intros I L H Hno e x fx' He Hx Hd; cbn in *.
      destruct (live_after _ _ ℓ x fx' I H Hno Hx Hd) as [(fx & Hx0 & Hc & Hd0)|Hnil].
      - rewrite <- Hc; exact (L e x fx He Hx0 Hd0).
      - rewrite Hnil; apply overlaps_nil_r.
    Qed.

    Lemma existsb_false {A} (p : A -> bool) l x : existsb p l = false -> In x l -> p x = false.
    Proof.
      intros H Hin; destruct (p x) eqn:Hp; [|reflexivity].
      rewrite (proj2 (existsb_exists p l) (ex_intro _ x (conj Hin Hp))) in H; discriminate.
    Qed.

    Theorem qinv_step (qs qs' : QState) ℓ :
      QInv qs -> qstep qs ℓ = Some qs' -> QInv qs'.
    Proof.
      intros (I & D & L) H.
      pose proof (qstep_core qs qs' ℓ H) as Hc.
      destruct ℓ as [c|t| |ℓ]; cbn [qstep qcore_label] in H, Hc.
      - (* QIns *)
        destruct (live_conflict (core qs) c || qconflict (queue qs) c) eqn:E; [discriminate|].
        apply orb_false_iff in E as [El Eq]; injection H as <-; cbn.
        split; [exact I|]; split.
        + apply qdisj_app; [exact D|]; intros e' Hin.
          rewrite overlaps_sym; exact (existsb_false _ _ _ Eq Hin).
        + intros e x fx He Hx Hd; cbn in *.
          apply in_app_or in He as [He|[<-|[]]]; [exact (L e x fx He Hx Hd)|cbn].
          assert (Hn : In x (names Σ (core qs))).
          { exact (in_names K_eq_dec Σ prog _ x fx (t_wf K_eq_dec Σ prog Kb _ I) Hx). }
          pose proof (existsb_false _ _ _ El Hn) as Hf; cbn in Hf; rewrite Hx, Hd in Hf; exact Hf.
      - (* QCancel *)
        destruct (existsb _ _); [|discriminate]; injection H as <-; cbn.
        split; [exact I|]; split; [apply qdisj_filter; exact D|].
        intros e x fx He Hx Hd; cbn in *; apply filter_In in He as [He _].
        exact (L e x fx He Hx Hd).
      - (* QAdmit *)
        destruct (queue qs) as [|[t c] q] eqn:Hq; [discriminate|].
        destruct (step (core qs) (OInsert c)) as [γ'|] eqn:Hs; [|discriminate].
        injection H as <-; cbn [core queue ticket] in *.
        destruct D as [D0 D].
        split; [exact (tinv_step K_eq_dec Σ prog Kb HK _ _ _ I Hs)|]; split; [exact D|].
        intros e x fx He Hx Hd; cbn [core queue ticket] in *.
        cbn [step] in Hs; destruct (conflict K_eq_dec Σ prog (core qs) c); [discriminate|].
        injection Hs as <-; cbn in Hx; unfold fupd in Hx.
        destruct (Nat.eqb_spec x (next Σ (core qs))) as [->|].
        + injection Hx as <-; cbn; rewrite overlaps_sym; exact (D0 e He).
        + apply (L e x fx); [rewrite Hq; right; exact He | exact Hx | exact Hd].
      - (* QCore *)
        assert (Hno : forall c, ℓ <> OInsert c) by (destruct ℓ; try discriminate; congruence).
        assert (H' : step (core qs) ℓ = Some (core qs') /\ queue qs' = queue qs /\ ticket qs' = ticket qs).
        { destruct ℓ; try (exfalso; exact (Hno _ eq_refl));
            (destruct (step (core qs) _); [injection H as <-; auto | discriminate]). }
        destruct H' as (Hs & Hq & Ht); destruct qs' as [γ' q' t']; cbn in *; subst q' t'.
        split; [exact (tinv_step K_eq_dec Σ prog Kb HK _ _ _ I Hs)|]; split; [exact D|].
        exact (qlive_core qs ℓ γ' I L Hs Hno).
    Qed.

    Corollary qinv_reachable (qs : QState) ls :
      qrun_labels qinit ls = Some qs -> QInv qs.
    Proof.
      assert (G : forall qs0 ls qs, QInv qs0 -> qrun_labels qs0 ls = Some qs -> QInv qs).
      { intros qs0 ls0; revert qs0; induction ls0 as [|ℓ ls0 IH]; cbn; intros qs0 qs1 I0 H.
        - injection H as <-; exact I0.
        - destruct (qstep qs0 ℓ) as [qs0'|] eqn:Hs; [|discriminate].
          exact (IH qs0' qs1 (qinv_step qs0 qs0' ℓ I0 Hs) H). }
      apply G; split; [exact (tinv_init K_eq_dec Σ prog Kb)|]; split; [exact I|].
      intros e x fx [].
    Qed.

    Definition qquiet (qs : QState) : Prop :=
      qstep qs QAdmit = None /\
      forall n ℓ, In ℓ (lifecycle_labels n) -> qstep qs (QCore ℓ) = None.

    (** A settled state has no retired fiber. *)
    Lemma settled_live (γ : State) x fx :
      settled Σ prog γ -> fibers Σ γ x = Some fx -> disposed Σ fx = false.
    Proof.
      intros S Hx; pose proof (S x fx Hx) as Sf; unfold settled_fiber in Sf.
      destruct (life Σ fx) as [[z|]|P acc w|acc w|acc w z]; try contradiction.
      - exact Sf.
      - exact (proj1 Sf).
      - destruct (disposed Σ fx) eqn:Hd; [|reflexivity].
        unfold target in Sf; rewrite Hx, Hd in Sf; discriminate.
    Qed.

    Theorem qquiet_empty (Hwf : well_founded (fun c' c => Above Σ prog c c')) (qs : QState) ls :
      qrun_labels qinit ls = Some qs -> qquiet qs -> queue qs = [].
    Proof.
      intros H [QA QL].
      destruct (qrun_core _ _ ls H) as [ls' Hr].
      assert (S : settled Σ prog (core qs)).
      { destruct (progress_reachable K_eq_dec Σ prog Hwf ls' _ Hr) as [S|(n & ℓ & γ' & Hin & Hs)];
          [exact S|].
        pose proof (QL n ℓ Hin) as Hq0.
        rewrite (qcore_lifecycle_back qs n ℓ γ' Hin Hs) in Hq0; discriminate. }
      destruct (qinv_reachable qs ls H) as (I & _ & L).
      destruct (queue qs) as [|[t c] q] eqn:Hq; [reflexivity|exfalso].
      cbn [qstep] in QA; rewrite Hq in QA.
      destruct (step (core qs) (OInsert c)) eqn:Hs; [discriminate|].
      cbn [step] in Hs.
      destruct (conflict K_eq_dec Σ prog (core qs) c) eqn:Hcf; [|discriminate].
      unfold conflict in Hcf; apply existsb_exists in Hcf as (x & _ & Hx).
      destruct (fibers Σ (core qs) x) as [fx|] eqn:Hfx; [|discriminate].
      assert (Hd : disposed Σ fx = false) by exact (settled_live _ x fx S Hfx).
      assert (He : In (t, c) (queue qs)) by (rewrite Hq; left; reflexivity).
      pose proof (L (t, c) x fx He Hfx Hd) as Hl; cbn in Hl; rewrite Hl in Hx; discriminate.
    Qed.
  End Term.
End Queue.

(** ** cordiverse/cordis#358 under the queue *)

From Cordis Require Import Services.Registry Examples.Basic.

Definition qrunEx := qrun_labels Nat.eq_dec ΣR progEx.
Definition qstepEx := qstep Nat.eq_dec ΣR progEx.

(** Insert the provider and the consumer, load both, dispose the provider
    (the consumer still holds it), and ask for a new provider at once. *)
Definition q_requested :=
  qrunEx (qinit ΣR)
    [QIns 0; QAdmit; QIns 1; QAdmit;
     QCore (LBegin 0); QCore (LStep 0); QCore (LStep 0);
     QCore (LBegin 1); QCore (LStep 1); QCore (LStep 1);
     QCore (ODispose 0); QCore (LLeave 0); QCore (LLeave 1);
     QIns 0].

(** The old provider (fiber 0) is retired but not removed, so the core
    refuses the insertion; the queue takes it instead, and it cannot be
    admitted yet. *)
Example q358_queued :
  match q_requested with Some qs => length (queue _ qs) | None => 0 end = 1.
Proof. reflexivity. Qed.

Example q358_blocked :
  match q_requested with Some qs => qstepEx qs QAdmit | None => Some (qinit ΣR) end = None.
Proof. reflexivity. Qed.

(** Old provider, consumer, new provider (name 4), [tools], queue length. *)
Definition qobs (qs : option (QState ΣR)) :=
  match qs with
  | Some qs => Some (tag (core _ qs) 0, tag (core _ qs) 1, tag (core _ qs) 4,
                     tool (core _ qs) 7, length (queue _ qs))
  | None => None
  end.

(** The only way on: the old fiber drains, then the new provider is admitted
    and loads, then the consumer reloads. *)
Definition q_done :=
  match q_requested with
  | Some qs =>
      qrunEx qs [QCore (LUndo 1); QCore (LUnloaded 1); QCore (LUndo 0);
                 QCore (LUnloaded 0); QCore (LRemove 0);
                 QAdmit; QCore (LBegin 4); QCore (LStep 4); QCore (LStep 4);
                 QCore (LBegin 1); QCore (LStep 1); QCore (LStep 1)]
  | None => None
  end.

Example q358_obs : qobs q_done = Some (None, Some 2, Some 2, Some (Some 42), 0).
Proof. reflexivity. Qed.
