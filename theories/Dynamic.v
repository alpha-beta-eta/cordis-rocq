(** * Confluence under interleaved orchestration

    Counterpart of part (2) of the paper's Theorem 73: two executions from
    the initial state that take the same orchestration inputs, interleaved
    with lifecycle steps in any way, and end quiet with no failed fiber,
    agree up to renaming ([dynamic_confluence]). Earlier insertions,
    disposals, restarts and resets leave no trace beyond the roots that
    remain.

    - Inputs ([Input]) name roots by insertion index, not by fiber name:
      the name a root draws depends on the schedule ([next] is also bumped
      by lifecycle steps). An execution ([DRun]) records the names its
      insertions drew, in order.
    - Canonical names label a root by its insertion index ([pos]).
    - The proof reduces to [final_agree] (SpawnConf.v): the root ledger
      ([Ledger]) shows that both final states hold, at each index not
      disposed, a root of the inserted component, and nothing else.

    Out of scope, as for [spawn_confluence]: [O-React] (runtime effects),
    and disposing a fiber that is not a root (it breaks [SLInv]). *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering
  Recovery Progress Termination Confluence StateInv Episode StateConf SpawnConf.
Import ListNotations.

Section Dynamic.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).
  Local Notation Fiber := (@Fiber K Σ C).
  Local Notation Label := (@Label C).
  Local Notation S := (St Σ).
  Local Notation fibers := (fibers Σ).
  Local Notation next := (next Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation parent := (Calculus.parent Σ).
  Local Notation disposed := (Calculus.disposed Σ).
  Local Notation acc_of := (acc_of Σ).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation cbody c := (body Σ (prog c)).
  Local Notation cprovs c := (provs Σ (prog c)).

  (** ** Hypotheses, as for [spawn_confluence] *)
  Variable Kb : nat.
  Hypothesis HK : forall c, Bounded Σ Kb (cbody c).
  Variable rank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', Above Σ prog c c' -> rank c < rank c'.
  Hypothesis Hbnd : forall c, rank c <= Rb.
  Hypothesis Total : forall c k, In k (cprovs c) -> AllDoneProv Σ k (cbody c).
  Hypothesis Hwb : forall a t, WellBehaved (Σ := Σ) a t.
  Hypothesis HUI : forall (a : Op Σ) (t : nat) (s1 s2 s1' s2' : S) (g1 g2 : S -> S) (o1 o2 : Out Σ),
    run a t s1 = Some (s1', g1, o1) -> run a t s2 = Some (s2', g2, o2) -> fun_eq (Σ := Σ) g1 g2.
  Hypothesis HTI : forall (a : Op Σ) (t t' : nat) (s : S),
    match run a t s, run a t' s with
    | None, None => True
    | Some (s1, _, o1), Some (s2, _, o2) => @st_eq Σ s1 s2 /\ o1 = o2
    | _, _ => False
    end.
  Hypothesis HRI : forall (k : K) (a b : Op Σ) (ta tb : nat) (g : S -> S), (@CoPair K Σ C prog) k a b -> ta <> tb ->
    yields (Σ := Σ) a ta g ->
    forall x, After ((@CoPair K Σ C prog) k a) a ta x -> shifted_ok (Σ := Σ) g (run b tb x) (run b tb (g x)).
  Hypothesis HCom : forall (k : K) (a b : Op Σ) (ta tb : nat), (@CoPair K Σ C prog) k a b -> ta <> tb ->
    Commute (Σ := Σ) a ta b tb.

  Local Notation PInv := (PInv K_eq_dec Σ prog Kb).
  Local Notation SLInv := (SLInv Σ).

  (** ** Orchestration inputs, by insertion index *)
  Inductive Input : Type :=
  | IIns (c : C)          (* O-Insert c *)
  | IDis (i : nat)        (* O-Dispose the i-th inserted root *)
  | IRestart (i : nat)    (* O-Restart it *)
  | IReset (i : nat).     (* O-Reset it *)

  Definition olabel (rs : list nat) (x : Input) : option Label :=
    match x with
    | IIns c => Some (OInsert c)
    | IDis i => option_map ODispose (nth_error rs i)
    | IRestart i => option_map ORestart (nth_error rs i)
    | IReset i => option_map OReset (nth_error rs i)
    end.

  (** The names insertions drew, oldest first. *)
  Definition radd (rs : list nat) (γ : State) (x : Input) : list nat :=
    match x with IIns _ => rs ++ [next γ] | _ => rs end.

  (** An execution: lifecycle steps anywhere, and the inputs in order. *)
  Inductive DRun : State -> list nat -> list Input -> State -> list nat -> Prop :=
  | dr_nil γ rs : DRun γ rs [] γ rs
  | dr_life γ rs ins ℓ γ1 γ2 rs2 :
      is_lifecycle ℓ -> step γ ℓ = Some γ1 -> DRun γ1 rs ins γ2 rs2 -> DRun γ rs ins γ2 rs2
  | dr_orch γ rs x ins ℓ γ1 γ2 rs2 :
      olabel rs x = Some ℓ -> step γ ℓ = Some γ1 -> DRun γ1 (radd rs γ x) ins γ2 rs2 ->
      DRun γ rs (x :: ins) γ2 rs2.

  Lemma olabel_not_react rs x ℓ : olabel rs x = Some ℓ -> forall n i, ℓ <> OReact n i.
  Proof.
    destruct x as [c|i|i|i]; cbn; [intros [= <-]; discriminate|..];
      destruct (nth_error rs i); cbn; intros E; try discriminate; injection E as <-; discriminate.
  Qed.

  (** The components inserted, in order. *)
  Fixpoint icomps (ins : list Input) : list C :=
    match ins with [] => [] | IIns c :: r => c :: icomps r | _ :: r => icomps r end.

  Lemma icomps_app l1 l2 : icomps (l1 ++ l2) = icomps l1 ++ icomps l2.
  Proof. induction l1 as [|[c|i|i|i] l1 IH]; cbn; [reflexivity | f_equal; exact IH | exact IH ..]. Qed.

  (** ** Root labels: the insertion index *)
  Fixpoint pos (rs : list nat) (n : nat) : nat :=
    match rs with [] => 0 | m :: r => if Nat.eqb n m then 0 else Datatypes.S (pos r n) end.

  Lemma pos_nth rs i n : NoDup rs -> nth_error rs i = Some n -> pos rs n = i.
  Proof.
    revert i; induction rs as [|m rs IH]; intros i N E; [destruct i; discriminate|].
    apply NoDup_cons_iff in N as [Nm N].
    destruct i as [|i]; cbn in E |- *.
    - injection E as ->; rewrite Nat.eqb_refl; reflexivity.
    - destruct (Nat.eqb_spec n m) as [->|]; [exfalso; apply Nm; exact (nth_error_In _ _ E)|].
      f_equal; exact (IH i N E).
  Qed.

  Lemma nth_pos rs n : In n rs -> nth_error rs (pos rs n) = Some n.
  Proof.
    induction rs as [|m rs IH]; intros H; [destruct H|]; cbn.
    destruct (Nat.eqb_spec n m) as [->|Hne]; [reflexivity|].
    destruct H as [->|H]; [congruence | exact (IH H)].
  Qed.

  Lemma pos_inj rs n n' : In n rs -> In n' rs -> pos rs n = pos rs n' -> n = n'.
  Proof.
    intros H H' E; pose proof (nth_pos rs n H) as A; pose proof (nth_pos rs n' H') as B.
    rewrite E in A; congruence.
  Qed.

  (** ** The root ledger

      Index [i] of [rs] holds the name the i-th insertion drew. That name
      is either gone, after a disposal, or a root of the i-th inserted
      component, disposed exactly when a disposal of [i] was taken. *)
  Record Ledger (γ : State) (rs : list nat) (done : list Input) : Prop := {
    lg_len : length rs = length (icomps done);
    lg_nodup : NoDup rs;
    lg_lt : forall n, In n rs -> n < next γ;
    lg_dis : forall i, In (IDis i) done -> i < length rs;
    lg_at : forall i n, nth_error rs i = Some n ->
      (fibers γ n = None /\ In (IDis i) done) \/
      (exists f, fibers γ n = Some f /\ parent f = None /\
         nth_error (icomps done) i = Some (fcomp f) /\ (disposed f = true <-> In (IDis i) done));
    lg_root : forall n f, fibers γ n = Some f -> parent f = None -> In n rs
  }.

  Lemma ledger_init : Ledger (@init K Σ C) [] [].
  Proof.
    split; cbn; try (intros; contradiction); try reflexivity; [constructor | | ].
    - intros [|i] n E; discriminate.
    - intros n f E; discriminate.
  Qed.

  (** No step lowers the counter. *)
  Lemma step_next (γ γ' : State) ℓ : step γ ℓ = Some γ' -> next γ <= next γ'.
  Proof.
    intros H; destruct ℓ; cbn [Calculus.step] in H; unfold load_step, undo_step in H; cbv zeta in H;
      repeat match type of H with context [match ?e with _ => _ end] => destruct e end;
      try discriminate; injection H as <-; cbn; lia.
  Qed.

  Lemma ledger_life (γ γ' : State) rs done ℓ :
    Ledger γ rs done -> PInv γ -> is_lifecycle ℓ -> step γ ℓ = Some γ' -> Ledger γ' rs done.
  Proof.
    intros L P Hl H.
    pose proof (sinv_wf K_eq_dec Σ prog Kb γ (p_s _ _ _ _ _ P)) as W.
    destruct (rk_step K_eq_dec Σ prog Kb γ γ' ℓ P Hl H) as [RK1 RK2].
    pose proof (step_next γ γ' ℓ H) as Hnx.
    split; [exact (lg_len _ _ _ L) | exact (lg_nodup _ _ _ L) | | exact (lg_dis _ _ _ L) | |].
    - intros n Hn; pose proof (lg_lt _ _ _ L n Hn); lia.
    - intros i n Hn.
      pose proof (lg_lt _ _ _ L n (nth_error_In _ _ Hn)) as Hlt.
      destruct (lg_at _ _ _ L i n Hn) as [[N D]|(f & Hf & Pf & Cf & Df)].
      + left; split; [|exact D].
        destruct (fibers γ' n) as [f'|] eqn:E; [|reflexivity].
        destruct (new_fiber K_eq_dec Σ prog γ γ' ℓ n f' W H N E) as [-> _]; lia.
      + destruct (fibers γ' n) as [f'|] eqn:E.
        * right; exists f'.
          destruct (fiber_step K_eq_dec Σ prog γ γ' ℓ n f f' W H Hf E) as (Ec & Ep & _).
          assert (Pf' : parent f' = None) by congruence.
          destruct (RK1 n f' E Pf') as (f0 & H0 & _ & _ & D0).
          rewrite Hf in H0; injection H0 as <-.
          split; [reflexivity|]; split; [exact Pf'|]; split; [rewrite Ec; exact Cf|].
          rewrite <- D0; exact Df.
        * left; split; [reflexivity|]; apply Df.
          destruct (disposed f) eqn:Hd; [reflexivity|].
          destruct (RK2 n f Hf Pf Hd) as (f' & Hf' & _); congruence.
    - intros n f' Hn Hp; destruct (RK1 n f' Hn Hp) as (f & Hf & Pf & _); exact (lg_root _ _ _ L n f Hf Pf).
  Qed.

  (** Rewriting one root's entry, keeping its component and parent. *)
  Lemma ledger_setf (γ : State) rs done x i n f f' :
    Ledger γ rs done -> nth_error rs i = Some n -> fibers γ n = Some f ->
    fcomp f' = fcomp f -> parent f' = parent f ->
    icomps [x] = [] -> (forall j, In (IDis j) [x] -> j = i) ->
    (disposed f' = true <-> disposed f = true \/ In (IDis i) [x]) ->
    Ledger (set_fiber Σ γ n f') rs (done ++ [x]).
  Proof.
    intros L Hn Hf Ec Ep Ex Hx Hd.
    assert (F : forall m, fibers (set_fiber Σ γ n f') m = if Nat.eqb m n then Some f' else fibers γ m)
      by (intros; reflexivity).
    assert (Di : forall j, In (IDis j) (done ++ [x]) <-> In (IDis j) done \/ (j = i /\ In (IDis j) [x])).
    { intros j; rewrite in_app_iff; split; [intros [A|A]; [left; exact A | right; split; [exact (Hx j A) | exact A]]|].
      intros [A|[_ A]]; [left | right]; exact A. }
    assert (Ic : icomps (done ++ [x]) = icomps done) by (rewrite icomps_app, Ex, app_nil_r; reflexivity).
    split; [rewrite Ic; exact (lg_len _ _ _ L) | exact (lg_nodup _ _ _ L) | exact (lg_lt _ _ _ L) | | |].
    - intros j Hj; apply Di in Hj as [Hj|[-> _]]; [exact (lg_dis _ _ _ L j Hj)|].
      apply nth_error_Some; congruence.
    - intros j m Hm; rewrite F, Ic.
      destruct (Nat.eqb_spec m n) as [->|Hne].
      + assert (j = i) as ->.
        { apply (proj1 (NoDup_nth_error rs) (lg_nodup _ _ _ L) j i); [apply nth_error_Some | ]; congruence. }
        destruct (lg_at _ _ _ L i n Hn) as [[N _]|(f0 & Hf0 & Pf0 & Cf0 & Df0)]; [congruence|].
        rewrite Hf in Hf0; injection Hf0 as <-.
        right; exists f'; split; [reflexivity|]; split; [congruence|]; split; [congruence|].
        rewrite Hd, Df0, Di; split; [intros [A|A]; [left; exact A | right; split; [reflexivity | exact A]]|].
        intros [A|[_ A]]; [left | right]; exact A.
      + assert (Hji : j <> i) by (intros ->; congruence).
        destruct (lg_at _ _ _ L j m Hm) as [[N D]|(f0 & Hf0 & Pf0 & Cf0 & Df0)].
        * left; split; [exact N | apply Di; left; exact D].
        * right; exists f0; repeat split; try assumption.
          -- intros A; apply Di; left; apply Df0; exact A.
          -- intros A; apply Df0; apply Di in A as [A|[E _]]; [exact A | contradiction].
    - intros m fm Hm Hp; rewrite F in Hm.
      destruct (Nat.eqb_spec m n) as [->|]; [exact (nth_error_In _ _ Hn)|].
      exact (lg_root _ _ _ L m fm Hm Hp).
  Qed.

  Lemma ledger_orch (γ γ' : State) rs done x ℓ :
    Ledger γ rs done -> PInv γ -> olabel rs x = Some ℓ -> step γ ℓ = Some γ' ->
    Ledger γ' (radd rs γ x) (done ++ [x]).
  Proof.
    intros L P Ho H.
    pose proof (sinv_wf K_eq_dec Σ prog Kb γ (p_s _ _ _ _ _ P)) as W.
    destruct x as [c|i|i|i]; cbn [olabel] in Ho.
    - (* insert *)
      injection Ho as <-; cbn [Calculus.step] in H.
      destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      cbn [radd].
      assert (Ic : icomps (done ++ [IIns c]) = icomps done ++ [c]) by (rewrite icomps_app; reflexivity).
      pose proof (lg_lt _ _ _ L) as Lt.
      assert (Nin : ~ In (next γ) rs) by (intros A; pose proof (Lt _ A); lia).
      set (nf := mkFiber Σ c None false (Inactive Σ None)).
      assert (F : forall m, fibers (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ) (Some nf)))) m =
                            if Nat.eqb m (next γ) then Some nf else fibers γ m) by (intros; reflexivity).
      assert (Di : forall j, In (IDis j) (done ++ [IIns c]) <-> In (IDis j) done).
      { intros j; rewrite in_app_iff; cbn; split; [intros [A|[A|[]]]; [exact A | discriminate] | intros A; left; exact A]. }
      split.
      + rewrite Ic, !length_app, (lg_len _ _ _ L); reflexivity.
      + apply NoDup_app; [exact (lg_nodup _ _ _ L) | constructor; [intros [] | constructor] |].
        intros a A [<-|[]]; exact (Nin A).
      + intros n Hn; cbn; apply in_app_iff in Hn as [Hn|[<-|[]]]; [pose proof (Lt n Hn); lia | lia].
      + intros j Hj; apply Di in Hj; rewrite length_app; pose proof (lg_dis _ _ _ L j Hj); cbn; lia.
      + intros j n Hn; rewrite F, Di, Ic.
        destruct (Nat.lt_ge_cases j (length rs)) as [Hj|Hj].
        * rewrite nth_error_app1 in Hn by exact Hj.
          assert (Hne : n <> next γ) by (intros ->; exact (Nin (nth_error_In _ _ Hn))).
          rewrite (proj2 (Nat.eqb_neq n (next γ)) Hne).
          destruct (lg_at _ _ _ L j n Hn) as [A|(f & Hf & Pf & Cf & Df)]; [left; exact A|].
          right; exists f; repeat split; try assumption;
            [| intros A; apply Di; exact (proj1 Df A) | intros A; apply Df, Di; exact A].
          rewrite nth_error_app1; [exact Cf|]; rewrite <- (lg_len _ _ _ L); exact Hj.
        * rewrite nth_error_app2 in Hn by exact Hj.
          destruct (j - length rs) as [|q] eqn:Eq; cbn in Hn; [|destruct q; discriminate].
          injection Hn as <-; rewrite Nat.eqb_refl.
          right; exists nf; split; [reflexivity|]; split; [reflexivity|]; split.
          -- rewrite nth_error_app2 by (rewrite <- (lg_len _ _ _ L); exact Hj).
             rewrite <- (lg_len _ _ _ L), Eq; reflexivity.
          -- cbn; split; [discriminate | intros A; apply Di in A; pose proof (lg_dis _ _ _ L j A); lia].
      + intros n f Hn Hp; rewrite F in Hn; apply in_app_iff.
        destruct (Nat.eqb_spec n (next γ)) as [->|]; [right; left; reflexivity|].
        left; exact (lg_root _ _ _ L n f Hn Hp).
    - (* dispose *)
      destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
      cbn [Calculus.step] in H; destruct (fibers γ n) as [f|] eqn:Hf; [|discriminate]; injection H as <-.
      apply (ledger_setf γ rs done _ i n f _ L Hn Hf); try reflexivity.
      + intros j [E|[]]; injection E as ->; reflexivity.
      + cbn; split; [intros _; right; left; reflexivity | reflexivity].
    - (* restart *)
      destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
      destruct (restart_shape K_eq_dec Σ prog γ γ' n H) as (f & acc & w & Hf & _ & _ & ->).
      apply (ledger_setf γ rs done _ i n f _ L Hn Hf); try reflexivity.
      + intros j [E|[]]; discriminate.
      + cbn; split; [intros A; left; exact A | intros [A|[E|[]]]; [exact A | discriminate]].
    - (* reset *)
      destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
      cbn [Calculus.step] in H; destruct (fibers γ n) as [f|] eqn:Hf; [|discriminate].
      destruct (life f) as [[z|]| | |]; try discriminate; injection H as <-.
      apply (ledger_setf γ rs done _ i n f _ L Hn Hf); try reflexivity.
      + intros j [E|[]]; discriminate.
      + cbn; split; [intros A; left; exact A | intros [A|[E|[]]]; [exact A | discriminate]].
  Qed.

  (** ** [SLInv] under orchestration *)
  Lemma sl_insert (γ γ' : State) c :
    PInv γ -> SLInv γ -> step γ (OInsert c) = Some γ' -> SLInv γ'.
  Proof.
    intros P SL H; cbn [Calculus.step] in H.
    destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
    pose proof (sinv_wf K_eq_dec Σ prog Kb γ (p_s _ _ _ _ _ P)) as W.
    set (nf := mkFiber Σ c None false (Inactive Σ None)).
    assert (F : forall m, fibers (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ) (Some nf)))) m =
                          if Nat.eqb m (next γ) then Some nf else fibers γ m) by (intros; reflexivity).
    assert (LV : forall m, Live Σ γ m -> Live Σ (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ) (Some nf)))) m).
    { intros m (fm & Hm & Hd); exists fm; split; [|exact Hd]; rewrite F.
      pose proof (wf_names K_eq_dec Σ prog γ W m fm Hm).
      rewrite (proj2 (Nat.eqb_neq m (next γ)) ltac:(lia)); exact Hm. }
    split.
    - intros n fn m Hn Hin; rewrite F in Hn; destruct (Nat.eqb_spec n (next γ)).
      + injection Hn as <-; cbn in Hin; destruct Hin.
      + destruct (sl_live _ _ SL n fn m Hn Hin) as [A|A]; [left; exact A | right; exact (LV m A)].
    - intros n fn Hn; rewrite F in Hn; destruct (Nat.eqb_spec n (next γ));
        [injection Hn as <-; constructor | exact (sl_nodup _ _ SL n fn Hn)].
    - intros m fm q Hm Hq; rewrite F in Hm; destruct (Nat.eqb_spec m (next γ)).
      + injection Hm as <-; discriminate.
      + exact (sl_par _ _ SL m fm q Hm Hq).
  Qed.

  (** Disposing a root: no fiber lists a root among its spawns. *)
  Lemma sl_dispose (γ γ' : State) n f :
    PInv γ -> SLInv γ -> fibers γ n = Some f -> parent f = None ->
    step γ (ODispose n) = Some γ' -> SLInv γ'.
  Proof.
    intros P SL Hf Pf H; cbn [Calculus.step] in H; rewrite Hf in H; injection H as <-.
    pose proof (c0_t K_eq_dec Σ prog Kb γ (s_c _ _ _ _ _ (p_s _ _ _ _ _ P))) as TI.
    pose proof (t_so K_eq_dec Σ prog Kb γ TI) as SO.
    set (f' := mkFiber Σ (fcomp f) (parent f) true (life f)).
    assert (F : forall m, fibers (set_fiber Σ γ n f') m = if Nat.eqb m n then Some f' else fibers γ m)
      by (intros; reflexivity).
    assert (Lf : forall m fm, fibers (set_fiber Σ γ n f') m = Some fm ->
                   exists f0, fibers γ m = Some f0 /\ life fm = life f0 /\ parent fm = parent f0).
    { intros m fm Hm; rewrite F in Hm; destruct (Nat.eqb_spec m n) as [->|].
      - injection Hm as <-; exists f; auto.
      - exists fm; auto. }
    split.
    - intros x fx m Hx Hin; destruct (Lf x fx Hx) as (f0 & H0 & El & _); rewrite El in Hin |- *.
      destruct (sl_live _ _ SL x f0 m H0 Hin) as [A|(fm & Hm & Hd)]; [left; exact A | right].
      destruct (Nat.eqb_spec m n) as [->|Hne].
      + rewrite Hf in Hm; injection Hm as <-.
        pose proof (SO x f0 n f H0 (proj1 (in_spawns Σ _ _) Hin) Hf); congruence.
      + exists fm; rewrite F, (proj2 (Nat.eqb_neq m n) Hne); auto.
    - intros x fx Hx; destruct (Lf x fx Hx) as (f0 & H0 & El & _); rewrite El; exact (sl_nodup _ _ SL x f0 H0).
    - intros m fm q Hm Hq; destruct (Lf m fm Hm) as (f0 & H0 & _ & Ep); rewrite Ep in Hq.
      exact (sl_par _ _ SL m f0 q H0 Hq).
  Qed.

  Lemma sl_restart (γ γ' : State) n :
    SLInv γ -> step γ (ORestart n) = Some γ' -> SLInv γ'.
  Proof.
    intros SL H.
    destruct (restart_shape K_eq_dec Σ prog γ γ' n H) as (f & acc & w & Hf & _ & (P & Hl) & ->).
    apply (sl_relife Σ γ γ n f); [exact SL | reflexivity | exact Hf | |].
    - intros m Hin; right; apply (live_kept Σ γ n f m SL Hf).
      + destruct Hl as [Hl|Hl]; rewrite Hl; exact Hin.
      + intros (a1 & w1 & z1 & E); destruct Hl as [Hl|Hl]; rewrite Hl in E; discriminate.
    - pose proof (sl_nodup _ _ SL n f Hf) as N; destruct Hl as [Hl|Hl]; rewrite Hl in N; exact N.
  Qed.

  Lemma sl_reset (γ γ' : State) n :
    SLInv γ -> step γ (OReset n) = Some γ' -> SLInv γ'.
  Proof.
    intros SL H; cbn [Calculus.step] in H; destruct (fibers γ n) as [f|] eqn:Hf; [|discriminate].
    destruct (life f) as [[z|]| | |]; try discriminate; injection H as <-.
    apply (sl_relife Σ γ γ n f); [exact SL | reflexivity | exact Hf | intros m [] | constructor].
  Qed.

  (** ** Along an execution *)
  Lemma drun_inv (γ γ' : State) rs ins rs' done :
    DRun γ rs ins γ' rs' -> Ledger γ rs done -> PInv γ -> SLInv γ ->
    Ledger γ' rs' (done ++ ins) /\ PInv γ' /\ SLInv γ'.
  Proof.
    intros R; revert done; induction R as [γ rs|γ rs ins ℓ γ1 γ2 rs2 Hl Hs R IH|γ rs x ins ℓ γ1 γ2 rs2 Ho Hs R IH];
      intros done L P SL.
    - rewrite app_nil_r; auto.
    - apply IH; [exact (ledger_life γ γ1 rs done ℓ L P Hl Hs)
                | exact (pinv_step K_eq_dec Σ prog Kb HK rank Hrank Total Hwb HUI HTI HRI HCom γ γ1 ℓ
                           (lifecycle_not_react ℓ Hl) P Hs)
                | exact (sl_step K_eq_dec Σ prog Kb γ γ1 ℓ P SL Hl Hs)].
    - replace (done ++ x :: ins) with ((done ++ [x]) ++ ins) by (rewrite <- app_assoc; reflexivity).
      apply IH; [exact (ledger_orch γ γ1 rs done x ℓ L P Ho Hs)
                | exact (pinv_step K_eq_dec Σ prog Kb HK rank Hrank Total Hwb HUI HTI HRI HCom γ γ1 ℓ
                           (olabel_not_react rs x ℓ Ho) P Hs) |].
      destruct x as [c|i|i|i]; cbn [olabel] in Ho.
      + injection Ho as <-; exact (sl_insert γ γ1 c P SL Hs).
      + destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
        destruct (lg_at _ _ _ L i n Hn) as [[N _]|(f & Hf & Pf & _)].
        * cbn [Calculus.step] in Hs; rewrite N in Hs; discriminate.
        * exact (sl_dispose γ γ1 n f P SL Hf Pf Hs).
      + destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
        exact (sl_restart γ γ1 n SL Hs).
      + destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
        exact (sl_reset γ γ1 n SL Hs).
  Qed.

  (** ** Surviving roots

      An index survives when no disposal of it was taken. Final roots are
      named by their position among the survivors ([slab]), so two runs
      that leave the same survivors in the same order can be compared even
      when their inputs differ. *)
  Definition isdis (i : nat) (x : Input) : bool :=
    match x with IDis j => Nat.eqb i j | _ => false end.

  Definition live_ix (ins : list Input) (i : nat) : bool := negb (existsb (isdis i) ins).

  Lemma live_ix_spec ins i : live_ix ins i = true <-> ~ In (IDis i) ins.
  Proof.
    unfold live_ix; rewrite negb_true_iff; split.
    - intros H A; assert (E : existsb (isdis i) ins = true)
        by (apply existsb_exists; exists (IDis i); split; [exact A | apply Nat.eqb_refl]); congruence.
    - intros H; destruct (existsb (isdis i) ins) eqn:E; [|reflexivity].
      apply existsb_exists in E as ([c|j|j|j] & Hx & Hd); cbn in Hd; try discriminate.
      apply Nat.eqb_eq in Hd as <-; contradiction.
  Qed.

  (** Keep the elements at indices [f] accepts, counting from [k]. *)
  Fixpoint keepi {A} (f : nat -> bool) (l : list A) (k : nat) : list A :=
    match l with
    | [] => []
    | a :: l' => if f k then a :: keepi f l' (Datatypes.S k) else keepi f l' (Datatypes.S k)
    end.

  (** How many indices in [k, k+i) [f] accepts. *)
  Fixpoint cnt (f : nat -> bool) (k i : nat) : nat :=
    match i with
    | 0 => 0
    | Datatypes.S i' => (if f k then 1 else 0) + cnt f (Datatypes.S k) i'
    end.

  Lemma keepi_nth {A} f (l : list A) k i a :
    nth_error l i = Some a -> f (k + i) = true -> nth_error (keepi f l k) (cnt f k i) = Some a.
  Proof.
    revert k i; induction l as [|x l IH]; intros k i E Hf; [destruct i; discriminate|].
    destruct i as [|i]; cbn in E |- *.
    - injection E as ->; rewrite Nat.add_0_r in Hf; rewrite Hf; reflexivity.
    - rewrite Nat.add_succ_r in Hf; change (Datatypes.S (k + i)) with (Datatypes.S k + i) in Hf.
      destruct (f k); cbn; exact (IH _ _ E Hf).
  Qed.

  Lemma keepi_surj {A} f (l : list A) k p a :
    nth_error (keepi f l k) p = Some a ->
    exists i, f (k + i) = true /\ cnt f k i = p /\ nth_error l i = Some a.
  Proof.
    revert k p; induction l as [|x l IH]; intros k p E; cbn in E; [destruct p; discriminate|].
    destruct (f k) eqn:Hf.
    - destruct p as [|p]; cbn in E.
      + injection E as ->; exists 0; rewrite Nat.add_0_r; auto.
      + destruct (IH _ _ E) as (i & Hi & Ci & Ei); exists (Datatypes.S i).
        rewrite Nat.add_succ_r; cbn; rewrite Hf; auto.
    - destruct (IH _ _ E) as (i & Hi & Ci & Ei); exists (Datatypes.S i).
      rewrite Nat.add_succ_r; cbn; rewrite Hf; auto.
  Qed.

  Lemma keepi_in {A} f (l : list A) k a : In a (keepi f l k) -> In a l.
  Proof.
    revert k; induction l as [|x l IH]; intros k H; cbn in H; [destruct H|].
    destruct (f k); [destruct H as [<-|H]; [left; reflexivity | right; exact (IH _ H)] | right; exact (IH _ H)].
  Qed.

  Lemma keepi_nodup {A} f (l : list A) k : NoDup l -> NoDup (keepi f l k).
  Proof.
    revert k; induction l as [|x l IH]; intros k N; cbn; [constructor|].
    apply NoDup_cons_iff in N as [Nx N].
    destruct (f k); [constructor; [intros Hin; exact (Nx (keepi_in _ _ _ _ Hin)) | exact (IH _ N)] | exact (IH _ N)].
  Qed.

  Lemma keepi_all {A} f (l : list A) k : (forall i, f i = true) -> keepi f l k = l.
  Proof.
    intros H; revert k; induction l as [|x l IH]; intros k; cbn; [reflexivity|].
    rewrite H, IH; reflexivity.
  Qed.

  (** The surviving roots' names and components, in insertion order. *)
  Definition sroots (rs : list nat) (ins : list Input) : list nat := keepi (live_ix ins) rs 0.
  Definition scomps (ins : list Input) : list C := keepi (live_ix ins) (icomps ins) 0.

  (** A root is labelled by its position among the survivors. *)
  Definition slab (rs : list nat) (ins : list Input) (n : nat) : nat := pos (sroots rs ins) n.

  (** ** Final roots *)

  (** At a final state every root survives, at the index the ledger gives it. *)
  Lemma final_root (γ : State) rs ins n f :
    Ledger γ rs ins -> settled Σ prog γ -> NoFailed Σ γ ->
    fibers γ n = Some f -> parent f = None ->
    nth_error rs (pos rs n) = Some n /\ live_ix ins (pos rs n) = true /\
    nth_error (icomps ins) (pos rs n) = Some (fcomp f).
  Proof.
    intros L St NF Hn Pn.
    pose proof (nth_pos rs n (lg_root _ _ _ L n f Hn Pn)) as E.
    destruct (settled_shape Σ prog γ n f St NF Hn) as [Hd _].
    destruct (lg_at _ _ _ L _ n E) as [[N _]|(f0 & Hf0 & _ & Cf & Df)]; [congruence|].
    rewrite Hn in Hf0; injection Hf0 as <-.
    split; [exact E|]; split; [|exact Cf].
    apply live_ix_spec; intros A; apply Df in A; congruence.
  Qed.

  Lemma final_slab (γ : State) rs ins n f :
    Ledger γ rs ins -> settled Σ prog γ -> NoFailed Σ γ ->
    fibers γ n = Some f -> parent f = None ->
    nth_error (sroots rs ins) (slab rs ins n) = Some n /\
    slab rs ins n = cnt (live_ix ins) 0 (pos rs n) /\
    nth_error (scomps ins) (slab rs ins n) = Some (fcomp f).
  Proof.
    intros L St NF Hn Pn.
    destruct (final_root γ rs ins n f L St NF Hn Pn) as (E & Lv & Cf).
    pose proof (keepi_nth (live_ix ins) rs 0 _ n E Lv) as En.
    assert (Es : slab rs ins n = cnt (live_ix ins) 0 (pos rs n)).
    { exact (pos_nth _ _ n (keepi_nodup _ _ _ (lg_nodup _ _ _ L)) En). }
    split; [rewrite Es; exact En|]; split; [exact Es|].
    rewrite Es; exact (keepi_nth (live_ix ins) (icomps ins) 0 _ _ Cf Lv).
  Qed.

  Lemma ledger_rootinj (γ : State) rs ins :
    Ledger γ rs ins -> settled Σ prog γ -> NoFailed Σ γ -> RootInj Σ (slab rs ins) γ.
  Proof.
    intros L St NF n n' f f' Hn Pn Hn' Pn' E.
    destruct (final_slab γ rs ins n f L St NF Hn Pn) as (A & _).
    destruct (final_slab γ rs ins n' f' L St NF Hn' Pn') as (B & _).
    rewrite E in A; congruence.
  Qed.

  Lemma ledger_match (γ1 γ2 : State) rs1 rs2 ins1 ins2 :
    Ledger γ1 rs1 ins1 -> Ledger γ2 rs2 ins2 -> scomps ins1 = scomps ins2 ->
    settled Σ prog γ1 -> NoFailed Σ γ1 ->
    RootsMatch Σ (slab rs1 ins1) (slab rs2 ins2) γ1 γ2.
  Proof.
    intros L1 L2 Es St NF n f1 Hn Pn.
    destruct (final_slab γ1 rs1 ins1 n f1 L1 St NF Hn Pn) as (_ & _ & Cs).
    rewrite Es in Cs.
    destruct (keepi_surj _ _ _ _ _ Cs) as (i & Lv & Ci & Ei); cbn in Lv.
    assert (Hi : i < length rs2) by (rewrite (lg_len _ _ _ L2); apply nth_error_Some; congruence).
    destruct (nth_error rs2 i) as [n2|] eqn:E2; [|apply nth_error_None in E2; lia].
    destruct (lg_at _ _ _ L2 i n2 E2) as [[_ D]|(f2 & Hf2 & Pf2 & Cf2 & _)].
    { apply live_ix_spec in Lv; contradiction. }
    exists n2, f2; split; [exact Hf2|]; split; [exact Pf2|]; split.
    - pose proof (keepi_nth (live_ix ins2) rs2 0 i n2 E2 Lv) as En.
      change (slab rs2 ins2 n2) with (pos (keepi (live_ix ins2) rs2 0) n2).
      rewrite (pos_nth _ _ n2 (keepi_nodup _ _ _ (lg_nodup _ _ _ L2)) En); exact Ci.
    - congruence.
  Qed.

  (** ** Confluence under interleaved orchestration

      Two executions from the initial state that end quiet with no failed
      fiber, and whose inputs leave the same surviving components in the
      same order, agree up to renaming; a root is named by its position
      among the survivors. The inputs may differ otherwise, and lifecycle
      steps may be interleaved with them in any way. *)
  Theorem dynamic_agree ins1 ins2 (γ1 γ2 : State) rs1 rs2 :
    DRun (@init K Σ C) [] ins1 γ1 rs1 -> DRun (@init K Σ C) [] ins2 γ2 rs2 ->
    scomps ins1 = scomps ins2 ->
    quiet K_eq_dec Σ prog γ1 -> quiet K_eq_dec Σ prog γ2 -> NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    AgreeL Σ (slab rs1 ins1) (slab rs2 ins2) γ1 γ2.
  Proof.
    intros R1 R2 Es Q1 Q2 NF1 NF2.
    assert (SL0 : SLInv (@init K Σ C)) by (split; intros; discriminate).
    destruct (drun_inv _ _ _ _ _ [] R1 ledger_init (pinv_init K_eq_dec Σ prog Kb) SL0) as (L1 & P1 & S1).
    destruct (drun_inv _ _ _ _ _ [] R2 ledger_init (pinv_init K_eq_dec Σ prog Kb) SL0) as (L2 & P2 & S2).
    cbn [app] in L1, L2.
    pose proof (quiet_final K_eq_dec Σ prog Kb rank Rb Hrank Hbnd γ1 P1 S1 Q1 NF1) as F1.
    pose proof (quiet_final K_eq_dec Σ prog Kb rank Rb Hrank Hbnd γ2 P2 S2 Q2 NF2) as F2.
    pose proof (proj1 (proj2 (proj1 F1))) as St1; pose proof (proj1 (proj2 (proj1 F2))) as St2.
    apply (final_agree K_eq_dec Σ prog Kb rank Rb Hrank Hbnd Hwb HTI HCom); try assumption.
    - exact (ledger_rootinj γ1 rs1 ins1 L1 St1 NF1).
    - exact (ledger_rootinj γ2 rs2 ins2 L2 St2 NF2).
    - exact (ledger_match γ1 γ2 rs1 rs2 ins1 ins2 L1 L2 Es St1 NF1).
    - exact (ledger_match γ2 γ1 rs2 rs1 ins2 ins1 L2 L1 (eq_sym Es) St2 NF2).
  Qed.

  (** The same inputs, in any interleaving (the paper's Theorem 73(2)). *)
  Corollary dynamic_confluence ins (γ1 γ2 : State) rs1 rs2 :
    DRun (@init K Σ C) [] ins γ1 rs1 -> DRun (@init K Σ C) [] ins γ2 rs2 ->
    quiet K_eq_dec Σ prog γ1 -> quiet K_eq_dec Σ prog γ2 -> NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    AgreeL Σ (slab rs1 ins) (slab rs2 ins) γ1 γ2.
  Proof. intros R1 R2; exact (dynamic_agree ins ins γ1 γ2 rs1 rs2 R1 R2 eq_refl). Qed.

  Lemma scomps_static cs : scomps (map IIns cs) = cs.
  Proof.
    unfold scomps; rewrite keepi_all.
    - induction cs as [|c cs IH]; cbn; [reflexivity | f_equal; exact IH].
    - intros i; apply live_ix_spec; intros A; apply in_map_iff in A as (c & E & _); discriminate.
  Qed.

  (** ** Static assembly (the paper's Theorem 73(1))

      Whatever history of insertions, disposals, restarts and resets an
      execution went through, its quiet state agrees with that of an
      execution that only inserts the surviving components, once each, in
      their order of insertion. *)
  Corollary static_assembly ins (γ γs : State) rs rss :
    DRun (@init K Σ C) [] ins γ rs -> DRun (@init K Σ C) [] (map IIns (scomps ins)) γs rss ->
    quiet K_eq_dec Σ prog γ -> quiet K_eq_dec Σ prog γs -> NoFailed Σ γ -> NoFailed Σ γs ->
    AgreeL Σ (slab rs ins) (slab rss (map IIns (scomps ins))) γ γs.
  Proof.
    intros R Rs; exact (dynamic_agree ins _ γ γs rs rss R Rs (eq_sym (scomps_static _))).
  Qed.
End Dynamic.
