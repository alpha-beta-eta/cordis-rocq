(** * Releasing external resources may fail (errors/DESIGN.md, section 5.3)

    Undoing an operation on the managed state does not fail (principle P3;
    the contribution model meets it by construction). What may fail is
    releasing a resource in the outside world: killing a child process,
    clearing a timer, deleting a file. A resource is acquired by an
    operation the service marks with [IsAcq] (the managed state records the
    handle); releasing it is undoing that operation. The managed state
    drops the record either way; whether the outside world let go is a
    separate fact, which the runtime logs.

    The state adds two logs of operation tokens: [released] and [leaked].
    [RCore (LUndo n)] undoes an acquire and logs it released; [RFail n]
    undoes it in the managed state too, but logs it leaked.

    - [rstep_core], [rrun_core]: every step is a core step ([RFail n] is
      [LUndo n]); so safety, progress, termination and recovery exactness
      on the managed state hold as in the core, whatever releases fail.
    - [rinv_step], [rinv_reachable]: every acquire ever performed is still
      held by a fiber (its undo item is in an accumulator), or was
      released, or is logged as leaked. Nothing leaks silently.
    - [all_unloaded]: once no fiber is installed, every acquire was
      released or is logged as leaked.

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Progress.
Import ListNotations.

Section Resource.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).
  Variable IsAcq : Op Σ -> bool.

  Local Notation State := (@State K Σ C).
  Local Notation Label := (@Label C).
  Local Notation step := (step K_eq_dec Σ prog).

  Record RState : Type := mkR {
    rcore : State;
    released : list nat;
    leaked : list nat
  }.

  Definition rinit : RState := mkR (@init K Σ C) [] [].

  Inductive RLabel : Type :=
  | RCore (ℓ : Label)
  | RFail (n : nat).

  (** The acquire at the head of [n]'s accumulator, if [n] is undoing one. *)
  Definition popped (γ : State) (n : nat) : option nat :=
    match fibers Σ γ n with
    | Some f =>
        match life Σ f with
        | Unloading _ (UOp _ _ _ t _ :: _) _ _ =>
            match oplog Σ γ t with
            | Some a => if IsAcq a then Some t else None
            | None => None
            end
        | _ => None
        end
    | None => None
    end.

  Definition rstep (rs : RState) (ℓ : RLabel) : option RState :=
    match ℓ with
    | RCore (LUndo n) =>
        match step (rcore rs) (LUndo n) with
        | Some γ' =>
            Some (mkR γ' (match popped (rcore rs) n with
                          | Some t => t :: released rs
                          | None => released rs
                          end) (leaked rs))
        | None => None
        end
    | RCore ℓ =>
        match step (rcore rs) ℓ with
        | Some γ' => Some (mkR γ' (released rs) (leaked rs))
        | None => None
        end
    | RFail n =>
        match popped (rcore rs) n with
        | Some t =>
            match step (rcore rs) (LUndo n) with
            | Some γ' => Some (mkR γ' (released rs) (t :: leaked rs))
            | None => None
            end
        | None => None
        end
    end.

  Fixpoint rrun_labels (rs : RState) (ls : list RLabel) : option RState :=
    match ls with
    | [] => Some rs
    | ℓ :: ls' => match rstep rs ℓ with Some rs' => rrun_labels rs' ls' | None => None end
    end.

  (** ** Every step is a core step *)
  Definition rlabel (ℓ : RLabel) : Label :=
    match ℓ with RCore ℓ => ℓ | RFail n => LUndo n end.

  Lemma rstep_core (rs rs' : RState) ℓ :
    rstep rs ℓ = Some rs' -> step (rcore rs) (rlabel ℓ) = Some (rcore rs').
  Proof.
    destruct ℓ as [ℓ|n]; cbn [rstep rlabel].
    - destruct ℓ; destruct (step (rcore rs) _); try discriminate; intros [= <-]; reflexivity.
    - destruct (popped (rcore rs) n); [|discriminate].
      destruct (step (rcore rs) (LUndo n)); [intros [= <-]; reflexivity | discriminate].
  Qed.

  Theorem rrun_core (rs0 rs : RState) ls :
    rrun_labels rs0 ls = Some rs ->
    run_labels K_eq_dec Σ prog (rcore rs0) (map rlabel ls) = Some (rcore rs).
  Proof.
    revert rs0; induction ls as [|ℓ ls IH]; cbn; intros rs0 H.
    - injection H as <-; reflexivity.
    - destruct (rstep rs0 ℓ) as [rs1|] eqn:Hs; [|discriminate].
      rewrite (rstep_core rs0 rs1 ℓ Hs); exact (IH rs1 H).
  Qed.

  Corollary rwf_reachable (rs : RState) ls :
    rrun_labels rinit ls = Some rs -> WF K_eq_dec Σ prog (rcore rs).
  Proof. intros H; exact (wf_reachable K_eq_dec Σ prog _ _ (rrun_core _ _ ls H)). Qed.

  (** ** Undo items survive a step, except the one an undo pops *)
  Definition Live (γ : State) (t : nat) : Prop :=
    exists n f k p g, fibers Σ γ n = Some f /\ In (UOp Σ k p t g) (acc_of Σ (life Σ f)).

  Lemma load_step_keeps (γ : State) n f P acc w x :
    In x acc ->
    exists f', fibers Σ (load_step K_eq_dec Σ prog γ n f P acc w) n = Some f' /\ In x (acc_of Σ (life Σ f')).
  Proof.
    intros Hx; unfold load_step; destruct P; cbn zeta;
      repeat match goal with |- context [match ?y with _ => _ end] => destruct y end;
      eexists; rewrite fibers_set_life, Nat.eqb_refl; (split; [reflexivity|]); cbn; auto.
  Qed.

  Lemma load_step_other_fiber (γ : State) n f P acc w m :
    m <> n -> m <> next Σ γ ->
    fibers Σ (load_step K_eq_dec Σ prog γ n f P acc w) m = fibers Σ γ m.
  Proof.
    intros Hmn Hmx; unfold load_step; destruct P; cbn zeta;
      repeat match goal with |- context [match ?y with _ => _ end] => destruct y end;
      rewrite fibers_set_life; destruct (Nat.eqb_spec m n); try contradiction; cbn; try reflexivity.
    unfold fupd; destruct (Nat.eqb_spec m (next Σ γ)); [contradiction | reflexivity].
  Qed.

  Lemma item_after (γ γ' : State) ℓ n f x :
    WF K_eq_dec Σ prog γ -> step γ ℓ = Some γ' -> fibers Σ γ n = Some f -> In x (acc_of Σ (life Σ f)) ->
    (exists f', fibers Σ γ' n = Some f' /\ In x (acc_of Σ (life Σ f'))) \/
    (ℓ = LUndo n /\ exists acc w z, life Σ f = Unloading Σ (x :: acc) w z).
  Proof.
    intros W H Hn Hx.
    pose proof (wf_names K_eq_dec Σ prog γ W n f Hn) as Hlt.
    assert (Keep : fibers Σ γ' n = fibers Σ γ n ->
              (exists f', fibers Σ γ' n = Some f' /\ In x (acc_of Σ (life Σ f'))) \/
              (ℓ = LUndo n /\ exists acc w z, life Σ f = Unloading Σ (x :: acc) w z))
      by (intros E; left; exists f; rewrite E; auto).
    assert (Rel : forall γ1 n0 f0 (l : Life Σ), fibers Σ γ1 = fibers Σ γ -> fibers Σ γ n0 = Some f0 ->
              (n0 = n -> forall y, In y (acc_of Σ (life Σ f0)) -> In y (acc_of Σ l)) ->
              (exists f', fibers Σ (set_life Σ γ1 n0 f0 l) n = Some f' /\ In x (acc_of Σ (life Σ f')))).
    { intros γ1 n0 f0 l E Hn0 Hsub; rewrite fibers_set_life.
      destruct (Nat.eqb_spec n n0) as [->|]; [|rewrite E; eauto].
      eexists; split; [reflexivity|]; cbn; rewrite Hn in Hn0; injection Hn0 as <-; exact (Hsub eq_refl x Hx). }
    destruct ℓ as [c|n0|n0|n0|n0|n0|n0|n0|n0|n0|n0|n0 i|n0]; cbn [Calculus.step] in H.
    - destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      apply Keep; cbn; unfold fupd; destruct (Nat.eqb_spec n (next Σ γ)); [lia | reflexivity].
    - destruct (fibers Σ γ n0) as [f0|] eqn:Hn0; [|discriminate]; injection H as <-.
      left; unfold set_fiber, with_fibers, fupd; cbn.
      destruct (Nat.eqb_spec n n0) as [->|]; [rewrite Hn in Hn0; injection Hn0 as <-; eexists; split; [reflexivity|]; exact Hx|].
      eauto.
    - destruct (fibers Σ γ n0) as [f0|] eqn:Hn0; [|discriminate].
      destruct (life Σ f0) as [[z|]| | |] eqn:Hl0; try discriminate; injection H as <-.
      left; apply (Rel γ n0 f0); auto; intros -> y Hy; rewrite Hl0 in Hy; destruct Hy.
    - destruct (fibers Σ γ n0) as [f0|] eqn:Hn0; [|discriminate].
      destruct (life Σ f0) as [[z|]| | |] eqn:Hl0; try discriminate.
      destruct (target Σ prog γ n0); [|discriminate]; injection H as <-.
      left; apply (Rel γ n0 f0); auto; intros -> y Hy; rewrite Hl0 in Hy; destruct Hy.
    - destruct (fibers Σ γ n0) as [f0|] eqn:Hn0; [|discriminate].
      destruct (life Σ f0) as [|P acc w| |] eqn:Hl0; try discriminate.
      destruct (may_step K_eq_dec Σ prog γ n0 P w); [|discriminate]; injection H as <-.
      left; destruct (Nat.eq_dec n n0) as [<-|Hne].
      + rewrite Hn in Hn0; injection Hn0 as <-; rewrite Hl0 in Hx.
        exact (load_step_keeps γ n f P acc w x Hx).
      + rewrite (load_step_other_fiber γ n0 f0 P acc w n Hne ltac:(lia)); eauto.
    - destruct (fibers Σ γ n0) as [f0|] eqn:Hn0; [|discriminate].
      destruct (life Σ f0) as [|P acc w| |] eqn:Hl0; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n0 w); [discriminate|]; injection H as <-.
      left; apply (Rel γ n0 f0); auto; intros -> y Hy; rewrite Hl0 in Hy; exact Hy.
    - destruct (fibers Σ γ n0) as [f0|] eqn:Hn0; [|discriminate].
      destruct (life Σ f0) as [| |acc w|] eqn:Hl0; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n0 w); [discriminate|]; injection H as <-.
      left; apply (Rel γ n0 f0); auto; intros -> y Hy; rewrite Hl0 in Hy; exact Hy.
    - destruct (fibers Σ γ n0) as [f0|] eqn:Hn0; [|discriminate].
      destruct (life Σ f0) as [| | |[|u acc] w z] eqn:Hl0; try discriminate.
      destruct (held Σ γ n0 (u :: acc)); [discriminate|].
      destruct (undo_step_shape K_eq_dec Σ γ γ' n0 f0 u acc w z H) as (γ1 & -> & E).
      destruct (Nat.eq_dec n n0) as [<-|Hne].
      + rewrite Hn in Hn0; injection Hn0 as <-; rewrite Hl0 in Hx; destruct Hx as [<-|Hx].
        * right; split; [reflexivity|]; eauto.
        * left; rewrite fibers_set_life, Nat.eqb_refl; eexists; split; [reflexivity|]; cbn; exact Hx.
      + left; apply (Rel γ1 n0 f0); auto; intros Heq; exfalso; congruence.
    - destruct (fibers Σ γ n0) as [f0|] eqn:Hn0; [|discriminate].
      destruct (life Σ f0) as [| | |[|[| |m'] acc] w z]; try discriminate.
      destruct (fibers Σ γ m') as [g|] eqn:Hg; [|discriminate].
      destruct (held Σ γ n0 (USpawn Σ m' :: acc) || disposed Σ g); [discriminate|]; injection H as <-.
      left; unfold set_fiber, with_fibers, fupd; cbn.
      destruct (Nat.eqb_spec n m') as [->|]; [rewrite Hn in Hg; injection Hg as <-; eexists; split; [reflexivity|]; exact Hx|].
      eauto.
    - destruct (fibers Σ γ n0) as [f0|] eqn:Hn0; [|discriminate].
      destruct (life Σ f0) as [| | |[|u acc] w z] eqn:Hl0; try discriminate; injection H as <-.
      left; apply (Rel γ n0 f0); auto; intros -> y Hy; rewrite Hl0 in Hy; destruct Hy.
    - destruct (fibers Σ γ n0) as [f0|] eqn:Hn0; [|discriminate].
      destruct (life Σ f0) eqn:Hl0; try discriminate.
      destruct (disposed Σ f0 && negb (has_child Σ γ n0)); [|discriminate]; injection H as <-.
      cbn; unfold fupd; destruct (Nat.eqb_spec n n0) as [->|].
      + rewrite Hn in Hn0; injection Hn0 as <-; rewrite Hl0 in Hx; destruct Hx.
      + left; eauto.
    - destruct (fibers Σ γ n0) as [f0|] eqn:Hn0; [|discriminate].
      destruct (life Σ f0) as [| |acc w|] eqn:Hl0; try discriminate.
      destruct (nth_error (reacts Σ (prog (comp Σ f0))) i) as [c|]; [|discriminate].
      destruct (disposed Σ f0 || conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      left; rewrite fibers_set_life; destruct (Nat.eqb_spec n n0) as [->|].
      + rewrite Hn in Hn0; injection Hn0 as <-; rewrite Hl0 in Hx.
        eexists; split; [reflexivity|]; cbn; right; exact Hx.
      + cbn; unfold fupd; destruct (Nat.eqb_spec n (next Σ γ)); [lia|]; eauto.
    - fold (step γ (ORestart n0)) in H.
      apply restart_shape in H as (f0 & acc & w & Hn0 & _ & [P Hl0] & ->).
      left; apply (Rel γ n0 f0); auto; intros -> y Hy; destruct Hl0 as [Hl0|Hl0]; rewrite Hl0 in Hy; exact Hy.
  Qed.

  (** ** New operations are held by the fiber that performed them *)
  Lemma oplog_after (γ γ' : State) ℓ t a :
    step γ ℓ = Some γ' -> oplog Σ γ' t = Some a ->
    (oplog Σ γ t = Some a /\ next Σ γ <= next Σ γ') \/
    (t = next Σ γ /\ next Σ γ < next Σ γ' /\ Live γ' t).
  Proof.
    intros H Ht.
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [Calculus.step] in H.
    all: repeat match type of H with context [match ?x with _ => _ end] => destruct x eqn:? end;
      try discriminate.
    all: try (unfold undo_step in H;
              repeat match type of H with context [match ?x with _ => _ end] => destruct x eqn:? end;
              try discriminate).
    all: injection H as <-.
    all: try (left; cbn in Ht |- *; split; [exact Ht | lia]).
    (* the load steps *)
    all: unfold load_step in Ht |- *; match goal with |- context [match ?P with PDone => _ | _ => _ end] => destruct P end;
      cbn zeta in Ht |- *;
      repeat match goal with |- context [match ?y with _ => _ end] => destruct y eqn:? end;
      cbn in Ht |- *; try (left; split; [exact Ht | lia]).
    all: destruct (Nat.eqb_spec t (next Σ γ)) as [->|]; [right | left; split; [exact Ht | lia]].
    all: split; [reflexivity|]; split; [lia|].
    all: eexists _, _, _, _, _; rewrite fibers_set_life, Nat.eqb_refl; split; [reflexivity | cbn; left; reflexivity].
  Qed.

  (** ** Nothing leaks silently *)
  Definition RInv (rs : RState) : Prop :=
    WF K_eq_dec Σ prog (rcore rs) /\
    (forall t a, oplog Σ (rcore rs) t = Some a -> t < next Σ (rcore rs)) /\
    (forall t a, oplog Σ (rcore rs) t = Some a -> IsAcq a = true ->
       Live (rcore rs) t \/ In t (released rs) \/ In t (leaked rs)).

  Theorem rinv_step (rs rs' : RState) ℓ : RInv rs -> rstep rs ℓ = Some rs' -> RInv rs'.
  Proof.
    intros (W & B & Cov) H.
    pose proof (rstep_core rs rs' ℓ H) as Hs.
    assert (Logs : forall t, In t (released rs) \/ In t (leaked rs) ->
                   In t (released rs') \/ In t (leaked rs')).
    { intros t Ht; destruct ℓ as [ℓ0|n0]; cbn [rstep] in H.
      - destruct ℓ0; destruct (step (rcore rs) _); try discriminate; injection H as <-; cbn;
          try (destruct (popped (rcore rs) _)); cbn; tauto.
      - destruct (popped (rcore rs) n0); [|discriminate].
        destruct (step (rcore rs) (LUndo n0)); [|discriminate]; injection H as <-; cbn; tauto. }
    split; [exact (preservation K_eq_dec Σ prog _ _ _ W Hs)|]; split.
    - intros t a Ht.
      destruct (oplog_after _ _ _ t a Hs Ht) as [[Ho Hle]|(-> & Hlt & _)]; [pose proof (B t a Ho); lia | exact Hlt].
    - intros t a Ht Ha.
      destruct (oplog_after _ _ _ t a Hs Ht) as [[Ho _]|(_ & _ & HL)]; [|left; exact HL].
      destruct (Cov t a Ho Ha) as [(n & f & k & p & g & Hn & Hin)|Hlog]; [|right; apply Logs; exact Hlog].
      destruct (item_after _ _ _ n f _ W Hs Hn Hin) as [(f' & Hn' & Hin')|(Hl & acc & w & z & Hlf)].
      + left; exists n, f', k, p, g; auto.
      + right.
        assert (Pop : popped (rcore rs) n = Some t)
          by (unfold popped; rewrite Hn, Hlf, Ho, Ha; reflexivity).
        destruct ℓ as [ℓ0|n0]; cbn [rlabel] in Hl.
        * subst ℓ0; cbn [rstep] in H; destruct (step (rcore rs) (LUndo n)); [|discriminate].
          injection H as <-; cbn; rewrite Pop; left; left; reflexivity.
        * injection Hl as ->; cbn [rstep] in H; rewrite Pop in H.
          destruct (step (rcore rs) (LUndo n)); [|discriminate].
          injection H as <-; cbn; right; left; reflexivity.
  Qed.

  Corollary rinv_reachable (rs : RState) ls : rrun_labels rinit ls = Some rs -> RInv rs.
  Proof.
    assert (G : forall rs0 ls rs, RInv rs0 -> rrun_labels rs0 ls = Some rs -> RInv rs).
    { intros rs0 ls0; revert rs0; induction ls0 as [|ℓ ls0 IH]; cbn; intros rs0 rs1 I0 H.
      - injection H as <-; exact I0.
      - destruct (rstep rs0 ℓ) as [rs0'|] eqn:Hs; [|discriminate].
        exact (IH rs0' rs1 (rinv_step rs0 rs0' ℓ I0 Hs) H). }
    apply G; split; [exact (wf_init K_eq_dec Σ prog)|]; split; intros t a Ht; discriminate.
  Qed.

  (** Once no fiber is installed, every acquire was released or is logged
      as leaked. *)
  Theorem all_unloaded (rs : RState) ls :
    rrun_labels rinit ls = Some rs ->
    (forall n f, fibers Σ (rcore rs) n = Some f -> is_installed Σ (life Σ f) = false) ->
    forall t a, oplog Σ (rcore rs) t = Some a -> IsAcq a = true ->
      In t (released rs) \/ In t (leaked rs).
  Proof.
    intros H Hni t a Ht Ha.
    destruct (rinv_reachable rs ls H) as (_ & _ & Cov).
    destruct (Cov t a Ht Ha) as [(n & f & k & p & g & Hn & Hin)|Hlog]; [|exact Hlog].
    exfalso; pose proof (Hni n f Hn) as Hi.
    destruct (life Σ f); try discriminate; cbn in Hin; exact Hin.
  Qed.
End Resource.
