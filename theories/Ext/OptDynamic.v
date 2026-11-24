(** * Extension 1: confluence under interleaved orchestration

    Counterpart of [Dynamic.dynamic_agree], [dynamic_confluence] and
    [static_assembly]: executions from the initial state that take
    orchestration inputs interleaved in any way with extended lifecycle
    steps, and end quiet with no failed fiber, agree up to renaming once
    their Inactive fibers' stale presence is normalised, when their inputs
    leave the same surviving base components in the same order.

    Same restriction as [OptSpawn.v]: children declare no optional
    dependency.

    The inputs, the root labels ([slab]) and the list lemmas are the
    core's ([Dynamic.v]). What changes:
    - The root ledger ([XLedger]) records base components: re-choosing a
      root's presence changes its component [(c, S)] but not [c].
    - Its preservation under an extended lifecycle step is proved once
      from four facts about the step ([XFrame]): the counter does not go
      down, new fibers take fresh names, parents stay, and roots stay
      ([OptSpawn.XRootKeep]). Orchestration steps follow the core's proof.
    - The final comparison is [OptSpawn.final_agreeX]. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering
  Recovery Progress Termination Confluence StateInv Episode StateConf SpawnConf Dynamic.
From Cordis Require Import Ext.Optional Ext.OptProgress Ext.OptConfluence Ext.OptState Ext.OptSpawn.
Import ListNotations.

Section OptDynamic.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (C_eq_dec : forall x y : C, {x = y} + {x <> y}).
  Context (xprog : C -> @XComponent K Σ C).

  Local Notation CC := (@Optional.C' K C).
  Local Notation State := (@State K Σ CC).
  Local Notation Fiber := (@Fiber K Σ CC).
  Local Notation Input := (@Input CC).
  Local Notation S := (St Σ).
  Local Notation fibers := (fibers Σ).
  Local Notation next := (Calculus.next Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation fparent := (Calculus.parent Σ).
  Local Notation disposed := (Calculus.disposed Σ).
  Local Notation is_installed := (is_installed Σ).
  Local Notation prog' := (prog' K_eq_dec Σ xprog).
  Local Notation step := (step K_eq_dec Σ prog').
  Local Notation xstep := (xstep K_eq_dec Σ xprog).
  Local Notation recomp := (recomp Σ xprog).
  Local Notation norm := (norm Σ xprog).
  Local Notation xopt c := (xopt Σ (xprog c)).
  Local Notation xprovs c := (xprovs Σ (xprog c)).

  (** ** Hypotheses, as for [xspawn_confluence] *)
  Variable Kb : nat.
  Hypothesis xHK : forall c T, Bounded Σ Kb (xbody Σ (xprog c) T).
  Variable xrank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', XAbove Σ xprog c c' -> xrank c < xrank c'.
  Hypothesis Hbnd : forall c, xrank c <= Rb.
  Hypothesis xTotal : forall c T k, In k (xprovs c) -> AllDoneProv Σ k (xbody Σ (xprog c) T).
  Hypothesis NoOptChild : forall c c', XSpawns Σ xprog c c' -> xopt c' = [].
  Hypothesis Hwb : forall a t, WellBehaved (Σ := Σ) a t.
  Hypothesis HUI : forall (a : Op Σ) (t : nat) (s1 s2 s1' s2' : S) (g1 g2 : S -> S) (o1 o2 : Out Σ),
    run a t s1 = Some (s1', g1, o1) -> run a t s2 = Some (s2', g2, o2) -> fun_eq (Σ := Σ) g1 g2.
  Hypothesis HTI : forall (a : Op Σ) (t t' : nat) (s : S),
    match run a t s, run a t' s with
    | None, None => True
    | Some (s1, _, o1), Some (s2, _, o2) => @st_eq Σ s1 s2 /\ o1 = o2
    | _, _ => False
    end.
  Hypothesis HRI : forall (k : K) (a b : Op Σ) (ta tb : nat) (g : S -> S),
    CoPair Σ prog' k a b -> ta <> tb -> yields (Σ := Σ) a ta g ->
    forall x, After (CoPair Σ prog' k a) a ta x -> shifted_ok (Σ := Σ) g (run b tb x) (run b tb (g x)).
  Hypothesis HCom : forall (k : K) (a b : Op Σ) (ta tb : nat), CoPair Σ prog' k a b -> ta <> tb ->
    Commute (Σ := Σ) a ta b tb.

  Local Notation rank' := (fun x : CC => xrank (fst x)).
  Local Notation HK' := (HK' K_eq_dec Σ xprog Kb xHK).
  Local Notation Total' := (Total' K_eq_dec Σ xprog xTotal).
  Local Notation Hrank2 := (Hrank2 K_eq_dec Σ xprog xrank Hrank).
  Local Notation PInv := (PInv K_eq_dec Σ prog' Kb).
  Local Notation SLInv := (SLInv Σ).
  Local Notation pinv_step :=
    (pinv_step K_eq_dec Σ prog' Kb HK' rank' Hrank2 Total' Hwb HUI HTI HRI HCom).
  Local Notation xstep_inv :=
    (xstep_inv K_eq_dec Σ xprog Kb xHK xrank Hrank xTotal NoOptChild Hwb HUI HTI HRI HCom).

  (** ** Executions *)
  Inductive XDRun : State -> list nat -> list Input -> State -> list nat -> Prop :=
  | xdr_nil γ rs : XDRun γ rs [] γ rs
  | xdr_life γ rs ins n ℓ γ1 γ2 rs2 :
      In ℓ (@lifecycle_labels C n) -> xstep γ ℓ = Some γ1 -> XDRun γ1 rs ins γ2 rs2 ->
      XDRun γ rs ins γ2 rs2
  | xdr_orch γ rs x ins ℓ γ1 γ2 rs2 :
      olabel rs x = Some ℓ -> step γ ℓ = Some γ1 -> XDRun γ1 (radd Σ rs γ x) ins γ2 rs2 ->
      XDRun γ rs (x :: ins) γ2 rs2.

  (** The base components inserted, in order. *)
  Definition xicomps (ins : list Input) : list C := map fst (icomps ins).

  (** ** The root ledger, by base component *)
  Record XLedger (γ : State) (rs : list nat) (done : list Input) : Prop := {
    xg_len : length rs = length (icomps done);
    xg_nodup : NoDup rs;
    xg_lt : forall n, In n rs -> n < next γ;
    xg_dis : forall i, In (IDis i) done -> i < length rs;
    xg_at : forall i n, nth_error rs i = Some n ->
      (fibers γ n = None /\ In (IDis i) done) \/
      (exists f, fibers γ n = Some f /\ fparent f = None /\
         nth_error (xicomps done) i = Some (fst (fcomp f)) /\ (disposed f = true <-> In (IDis i) done));
    xg_root : forall n f, fibers γ n = Some f -> fparent f = None -> In n rs
  }.

  Lemma xledger_init : XLedger (@init K Σ CC) [] [].
  Proof.
    split; cbn; try (intros; contradiction); try reflexivity; [constructor | | ].
    - intros [|i] n E; discriminate.
    - intros n f E; discriminate.
  Qed.

  (** What a lifecycle step may do to fibers. *)
  Definition XFrame (γ γ' : State) : Prop :=
    next γ <= next γ' /\
    (forall n f', fibers γ n = None -> fibers γ' n = Some f' -> next γ <= n) /\
    (forall n f f', fibers γ n = Some f -> fibers γ' n = Some f' -> fparent f' = fparent f) /\
    XRootKeep Σ γ γ'.

  Lemma xledger_frame (γ γ' : State) rs done :
    XLedger γ rs done -> XFrame γ γ' -> XLedger γ' rs done.
  Proof.
    intros L (Hnx & Hnew & Hpar & [RK1 RK2]).
    split; [exact (xg_len _ _ _ L) | exact (xg_nodup _ _ _ L) | | exact (xg_dis _ _ _ L) | |].
    - intros n Hn; pose proof (xg_lt _ _ _ L n Hn); lia.
    - intros i n Hn.
      pose proof (xg_lt _ _ _ L n (nth_error_In _ _ Hn)) as Hlt.
      destruct (xg_at _ _ _ L i n Hn) as [[N D]|(f & Hf & Pf & Cf & Df)].
      + left; split; [|exact D].
        destruct (fibers γ' n) as [f'|] eqn:E; [|reflexivity].
        pose proof (Hnew n f' N E); lia.
      + destruct (fibers γ' n) as [f'|] eqn:E.
        * right; exists f'.
          assert (Pf' : fparent f' = None) by (rewrite (Hpar n f f' Hf E); exact Pf).
          destruct (RK1 n f' E Pf') as (f0 & H0 & _ & C0 & D0).
          rewrite Hf in H0; injection H0 as <-.
          split; [reflexivity|]; split; [exact Pf'|]; split; [rewrite <- C0; exact Cf|].
          rewrite <- D0; exact Df.
        * left; split; [reflexivity|]; apply Df.
          destruct (disposed f) eqn:Hd; [reflexivity|].
          destruct (RK2 n f Hf Pf Hd) as (f' & Hf' & _); congruence.
    - intros n f' Hn Hp; destruct (RK1 n f' Hn Hp) as (f & Hf & Pf & _); exact (xg_root _ _ _ L n f Hf Pf).
  Qed.

  Lemma core_frame (γ γ' : State) ℓ :
    WF K_eq_dec Σ prog' γ -> step γ ℓ = Some γ' ->
    next γ <= next γ' /\
    (forall n f', fibers γ n = None -> fibers γ' n = Some f' -> next γ <= n) /\
    (forall n f f', fibers γ n = Some f -> fibers γ' n = Some f' -> fparent f' = fparent f).
  Proof.
    intros W H; split; [exact (step_next K_eq_dec Σ prog' γ γ' ℓ H)|]; split.
    - intros n f' N E; destruct (new_fiber K_eq_dec Σ prog' γ γ' ℓ n f' W H N E) as [-> _]; lia.
    - intros n f f' Hf Hf'; exact (proj1 (proj2 (fiber_step K_eq_dec Σ prog' γ γ' ℓ n f f' W H Hf Hf'))).
  Qed.

  Lemma xstep_frame (γ γ' : State) n ℓ :
    PInv γ -> SLInv γ -> In ℓ (@lifecycle_labels C n) -> xstep γ ℓ = Some γ' -> XFrame γ γ'.
  Proof.
    intros P SL Hin H.
    destruct (xstep_inv γ γ' n ℓ P SL Hin H) as (_ & _ & RK).
    pose proof (sinv_wf K_eq_dec Σ prog' Kb γ (p_s _ _ _ _ _ P)) as W.
    split; [|split; [|split; [|exact RK]]];
      destruct (xstep_core K_eq_dec Σ xprog γ γ' ℓ H) as [St|[(m & f & _ & Hm & Hl & St)|(m & St)]];
      try (destruct (core_frame γ γ' _ W St) as (A & B & C'); assumption).
    all: assert (Hi : is_installed (life f) = false) by (rewrite Hl; reflexivity).
    all: destruct (fparent f) as [q|] eqn:Hp;
      [ rewrite (recomp_child K_eq_dec Σ xprog Kb NoOptChild γ m f q
                   (pinv_tinv K_eq_dec Σ xprog Kb γ P) Hm Hp) in St;
        destruct (core_frame γ γ' _ W St) as (A & B & C'); assumption
      | pose proof (rf2_recomp_root Σ xprog γ m f Hm Hi Hp) as R2;
        pose proof (rf2_pinv K_eq_dec Σ xprog Kb γ _ P R2) as Pr; rewrite <- recomp_with in Pr;
        destruct (core_frame _ γ' _ (sinv_wf K_eq_dec Σ prog' Kb _ (p_s _ _ _ _ _ Pr)) St) as (A & B & C') ].
    - exact A.
    - intros k f' N E; apply (B k f'); [|exact E].
      rewrite fibers_recomp; destruct (Nat.eqb_spec k m) as [->|]; [congruence | exact N].
    - intros k g g' Hg Hg'.
      destruct (fibers (recomp γ m f) k) as [g0|] eqn:E0.
      + rewrite (C' k g0 g' E0 Hg').
        rewrite fibers_recomp in E0; destruct (Nat.eqb_spec k m) as [->|].
        * injection E0 as <-; rewrite Hm in Hg; injection Hg as <-; reflexivity.
        * congruence.
      + rewrite fibers_recomp in E0; destruct (Nat.eqb_spec k m); [discriminate | congruence].
  Qed.

  (** ** Orchestration steps keep the ledger *)
  Lemma xledger_setf (γ : State) rs done x i n f f' :
    XLedger γ rs done -> nth_error rs i = Some n -> fibers γ n = Some f ->
    fcomp f' = fcomp f -> fparent f' = fparent f ->
    icomps [x] = [] -> (forall j, In (IDis j) [x] -> j = i) ->
    (disposed f' = true <-> disposed f = true \/ In (IDis i) [x]) ->
    XLedger (set_fiber Σ γ n f') rs (done ++ [x]).
  Proof.
    intros L Hn Hf Ec Ep Ex Hx Hd.
    assert (F : forall m, fibers (set_fiber Σ γ n f') m = if Nat.eqb m n then Some f' else fibers γ m)
      by (intros; reflexivity).
    assert (Di : forall j, In (IDis j) (done ++ [x]) <-> In (IDis j) done \/ (j = i /\ In (IDis j) [x])).
    { intros j; rewrite in_app_iff; split; [intros [A|A]; [left; exact A | right; split; [exact (Hx j A) | exact A]]|].
      intros [A|[_ A]]; [left | right]; exact A. }
    assert (Ic : icomps (done ++ [x]) = icomps done) by (rewrite icomps_app, Ex, app_nil_r; reflexivity).
    assert (Ix : xicomps (done ++ [x]) = xicomps done) by (unfold xicomps; rewrite Ic; reflexivity).
    split; [rewrite Ic; exact (xg_len _ _ _ L) | exact (xg_nodup _ _ _ L) | exact (xg_lt _ _ _ L) | | |].
    - intros j Hj; apply Di in Hj as [Hj|[-> _]]; [exact (xg_dis _ _ _ L j Hj)|].
      apply nth_error_Some; congruence.
    - intros j m Hm; rewrite F, Ix.
      destruct (Nat.eqb_spec m n) as [->|Hne].
      + assert (j = i) as ->.
        { apply (proj1 (NoDup_nth_error rs) (xg_nodup _ _ _ L) j i); [apply nth_error_Some | ]; congruence. }
        destruct (xg_at _ _ _ L i n Hn) as [[N _]|(f0 & Hf0 & Pf0 & Cf0 & Df0)]; [congruence|].
        rewrite Hf in Hf0; injection Hf0 as <-.
        right; exists f'; split; [reflexivity|]; split; [congruence|]; split; [rewrite Ec; exact Cf0|].
        rewrite Hd, Df0, Di; split; [intros [A|A]; [left; exact A | right; split; [reflexivity | exact A]]|].
        intros [A|[_ A]]; [left | right]; exact A.
      + assert (Hji : j <> i) by (intros ->; congruence).
        destruct (xg_at _ _ _ L j m Hm) as [[N D]|(f0 & Hf0 & Pf0 & Cf0 & Df0)].
        * left; split; [exact N | apply Di; left; exact D].
        * right; exists f0; repeat split; try assumption.
          -- intros A; apply Di; left; apply Df0; exact A.
          -- intros A; apply Df0; apply Di in A as [A|[E _]]; [exact A | contradiction].
    - intros m fm Hm Hp; rewrite F in Hm.
      destruct (Nat.eqb_spec m n) as [->|]; [exact (nth_error_In _ _ Hn)|].
      exact (xg_root _ _ _ L m fm Hm Hp).
  Qed.

  Lemma xledger_orch (γ γ' : State) rs done x ℓ :
    XLedger γ rs done -> PInv γ -> olabel rs x = Some ℓ -> step γ ℓ = Some γ' ->
    XLedger γ' (radd Σ rs γ x) (done ++ [x]).
  Proof.
    intros L P Ho H.
    destruct x as [c|i|i|i]; cbn [olabel] in Ho.
    - injection Ho as <-; cbn [Calculus.step] in H.
      destruct (conflict K_eq_dec Σ prog' γ c); [discriminate|]; injection H as <-.
      cbn [radd].
      assert (Ic : icomps (done ++ [IIns c]) = icomps done ++ [c]) by (rewrite icomps_app; reflexivity).
      assert (Ix : xicomps (done ++ [IIns c]) = xicomps done ++ [fst c])
        by (unfold xicomps; rewrite Ic, map_app; reflexivity).
      pose proof (xg_lt _ _ _ L) as Lt.
      assert (Nin : ~ In (next γ) rs) by (intros A; pose proof (Lt _ A); lia).
      set (nf := mkFiber Σ c None false (Inactive Σ None)).
      assert (F : forall m, fibers (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ) (Some nf)))) m =
                            if Nat.eqb m (next γ) then Some nf else fibers γ m) by (intros; reflexivity).
      assert (Di : forall j, In (IDis j) (done ++ [IIns c]) <-> In (IDis j) done).
      { intros j; rewrite in_app_iff; cbn; split; [intros [A|[A|[]]]; [exact A | discriminate] | intros A; left; exact A]. }
      assert (Lx : length (xicomps done) = length rs) by (unfold xicomps; rewrite length_map; symmetry; exact (xg_len _ _ _ L)).
      split.
      + rewrite Ic, !length_app, (xg_len _ _ _ L); reflexivity.
      + apply NoDup_app; [exact (xg_nodup _ _ _ L) | constructor; [intros [] | constructor] |].
        intros a A [<-|[]]; exact (Nin A).
      + intros n Hn; cbn; apply in_app_iff in Hn as [Hn|[<-|[]]]; [pose proof (Lt n Hn); lia | lia].
      + intros j Hj; apply Di in Hj; rewrite length_app; pose proof (xg_dis _ _ _ L j Hj); cbn; lia.
      + intros j n Hn; rewrite F, Di, Ix.
        destruct (Nat.lt_ge_cases j (length rs)) as [Hj|Hj].
        * rewrite nth_error_app1 in Hn by exact Hj.
          assert (Hne : n <> next γ) by (intros ->; exact (Nin (nth_error_In _ _ Hn))).
          rewrite (proj2 (Nat.eqb_neq n (next γ)) Hne).
          destruct (xg_at _ _ _ L j n Hn) as [A|(f & Hf & Pf & Cf & Df)]; [left; exact A|].
          right; exists f; repeat split; try assumption;
            [| intros A; apply Di; exact (proj1 Df A) | intros A; apply Df, Di; exact A].
          rewrite nth_error_app1; [exact Cf|]; rewrite Lx; exact Hj.
        * rewrite nth_error_app2 in Hn by exact Hj.
          destruct (j - length rs) as [|q] eqn:Eq; cbn in Hn; [|destruct q; discriminate].
          injection Hn as <-; rewrite Nat.eqb_refl.
          right; exists nf; split; [reflexivity|]; split; [reflexivity|]; split.
          -- rewrite nth_error_app2 by (rewrite Lx; exact Hj).
             rewrite Lx, Eq; reflexivity.
          -- cbn; split; [discriminate | intros A; apply Di in A; pose proof (xg_dis _ _ _ L j A); lia].
      + intros n f Hn Hp; rewrite F in Hn; apply in_app_iff.
        destruct (Nat.eqb_spec n (next γ)) as [->|]; [right; left; reflexivity|].
        left; exact (xg_root _ _ _ L n f Hn Hp).
    - destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
      cbn [Calculus.step] in H; destruct (fibers γ n) as [f|] eqn:Hf; [|discriminate]; injection H as <-.
      apply (xledger_setf γ rs done _ i n f _ L Hn Hf); try reflexivity.
      + intros j [E|[]]; injection E as ->; reflexivity.
      + cbn; split; [intros _; right; left; reflexivity | reflexivity].
    - destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
      destruct (restart_shape K_eq_dec Σ prog' γ γ' n H) as (f & acc & w & Hf & _ & _ & ->).
      apply (xledger_setf γ rs done _ i n f _ L Hn Hf); try reflexivity.
      + intros j [E|[]]; discriminate.
      + cbn; split; [intros A; left; exact A | intros [A|[E|[]]]; [exact A | discriminate]].
    - destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
      cbn [Calculus.step] in H; destruct (fibers γ n) as [f|] eqn:Hf; [|discriminate].
      destruct (life f) as [[z|]| | |]; try discriminate; injection H as <-.
      apply (xledger_setf γ rs done _ i n f _ L Hn Hf); try reflexivity.
      + intros j [E|[]]; discriminate.
      + cbn; split; [intros A; left; exact A | intros [A|[E|[]]]; [exact A | discriminate]].
  Qed.

  (** ** Along an execution *)
  Lemma xdrun_inv (γ γ' : State) rs ins rs' done :
    XDRun γ rs ins γ' rs' -> XLedger γ rs done -> PInv γ -> SLInv γ ->
    XLedger γ' rs' (done ++ ins) /\ PInv γ' /\ SLInv γ'.
  Proof.
    intros R; revert done; induction R as [γ rs|γ rs ins n ℓ γ1 γ2 rs2 Hl Hs R IH|γ rs x ins ℓ γ1 γ2 rs2 Ho Hs R IH];
      intros done L P SL.
    - rewrite app_nil_r; auto.
    - destruct (xstep_inv γ γ1 n ℓ P SL Hl Hs) as (P1 & S1 & _).
      apply IH; [exact (xledger_frame γ γ1 rs done L (xstep_frame γ γ1 n ℓ P SL Hl Hs)) | exact P1 | exact S1].
    - replace (done ++ x :: ins) with ((done ++ [x]) ++ ins) by (rewrite <- app_assoc; reflexivity).
      apply IH; [exact (xledger_orch γ γ1 rs done x ℓ L P Ho Hs)
                | exact (pinv_step γ γ1 ℓ (olabel_not_react rs x ℓ Ho) P Hs) |].
      destruct x as [c|i|i|i]; cbn [olabel] in Ho.
      + injection Ho as <-; exact (sl_insert K_eq_dec Σ prog' Kb γ γ1 c P SL Hs).
      + destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
        destruct (xg_at _ _ _ L i n Hn) as [[N _]|(f & Hf & Pf & _)].
        * cbn [Calculus.step] in Hs; rewrite N in Hs; discriminate.
        * exact (sl_dispose K_eq_dec Σ prog' Kb γ γ1 n f P SL Hf Pf Hs).
      + destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
        exact (sl_restart K_eq_dec Σ prog' γ γ1 n SL Hs).
      + destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
        exact (sl_reset K_eq_dec Σ prog' γ γ1 n SL Hs).
  Qed.

  (** ** Final roots *)
  Lemma xledger_rf (γ : State) F rs done : XLedger γ rs done -> RF Σ γ F -> XLedger (with_fibers Σ γ F) rs done.
  Proof.
    intros L R; apply (xledger_frame γ _ rs done L).
    pose proof R as [R1 R2]; split; [reflexivity|]; split; [|split; [|exact (xrk_rf Σ γ F R)]].
    - intros n f' N E; destruct (R1 n f' E) as (f0 & H0 & _); congruence.
    - intros n f f' Hf Hf'; destruct (R1 n f' Hf') as (f0 & H0 & _ & Ep & _); congruence.
  Qed.

  Definition xscomps (ins : list Input) : list C := map fst (scomps ins).

  Lemma map_nth_error_inv {A B} (g : A -> B) l i y :
    nth_error (map g l) i = Some y -> exists x, nth_error l i = Some x /\ g x = y.
  Proof.
    rewrite nth_error_map; destruct (nth_error l i) as [x|]; cbn; [intros [= <-]; eauto | discriminate].
  Qed.

  Lemma xfinal_slab (γ : State) rs ins n f :
    XLedger γ rs ins -> settled Σ prog' γ -> NoFailed Σ γ ->
    fibers γ n = Some f -> fparent f = None ->
    nth_error (sroots rs ins) (slab rs ins n) = Some n /\
    nth_error (xscomps ins) (slab rs ins n) = Some (fst (fcomp f)).
  Proof.
    intros L St NF Hn Pn.
    pose proof (nth_pos rs n (xg_root _ _ _ L n f Hn Pn)) as E.
    destruct (settled_shape Σ prog' γ n f St NF Hn) as [Hd _].
    destruct (xg_at _ _ _ L _ n E) as [[N _]|(f0 & Hf0 & _ & Cf & Df)]; [congruence|].
    rewrite Hn in Hf0; injection Hf0 as <-.
    assert (Lv : live_ix ins (pos rs n) = true) by (apply live_ix_spec; intros A; apply Df in A; congruence).
    pose proof (keepi_nth (live_ix ins) rs 0 _ n E Lv) as En.
    assert (Es : slab rs ins n = cnt (live_ix ins) 0 (pos rs n)).
    { exact (pos_nth _ _ n (keepi_nodup _ _ _ (xg_nodup _ _ _ L)) En). }
    split; [rewrite Es; exact En|].
    unfold xicomps in Cf; apply map_nth_error_inv in Cf as (c & Cc & Ec); rewrite <- Ec.
    unfold xscomps, scomps; rewrite Es; apply map_nth_error.
    exact (keepi_nth (live_ix ins) (icomps ins) 0 _ _ Cc Lv).
  Qed.

  Lemma xledger_rootinj (γ : State) rs ins :
    XLedger γ rs ins -> settled Σ prog' γ -> NoFailed Σ γ -> RootInj Σ (slab rs ins) γ.
  Proof.
    intros L St NF n n' f f' Hn Pn Hn' Pn' E.
    destruct (xfinal_slab γ rs ins n f L St NF Hn Pn) as (A & _).
    destruct (xfinal_slab γ rs ins n' f' L St NF Hn' Pn') as (B & _).
    rewrite E in A; congruence.
  Qed.

  Lemma xledger_match (γ1 γ2 : State) rs1 rs2 ins1 ins2 :
    XLedger γ1 rs1 ins1 -> XLedger γ2 rs2 ins2 -> xscomps ins1 = xscomps ins2 ->
    settled Σ prog' γ1 -> NoFailed Σ γ1 ->
    RootsMatchX Σ (slab rs1 ins1) (slab rs2 ins2) γ1 γ2.
  Proof.
    intros L1 L2 Es St NF n f1 Hn Pn.
    destruct (xfinal_slab γ1 rs1 ins1 n f1 L1 St NF Hn Pn) as (_ & Cs).
    rewrite Es in Cs; unfold xscomps, scomps in Cs.
    apply map_nth_error_inv in Cs as (c & Cs & Ec).
    destruct (keepi_surj _ _ _ _ _ Cs) as (i & Lv & Ci & Ei); cbn in Lv.
    assert (Hi : i < length rs2) by (rewrite (xg_len _ _ _ L2); apply nth_error_Some; intros N; unfold Optional.C' in *; rewrite Ei in N; discriminate N).
    destruct (nth_error rs2 i) as [n2|] eqn:E2; [|apply nth_error_None in E2; lia].
    destruct (xg_at _ _ _ L2 i n2 E2) as [[_ D]|(f2 & Hf2 & Pf2 & Cf2 & _)].
    { apply live_ix_spec in Lv; contradiction. }
    exists n2, f2; split; [exact Hf2|]; split; [exact Pf2|]; split.
    - pose proof (keepi_nth (live_ix ins2) rs2 0 i n2 E2 Lv) as En.
      change (slab rs2 ins2 n2) with (pos (keepi (live_ix ins2) rs2 0) n2).
      rewrite (pos_nth _ _ n2 (keepi_nodup _ _ _ (xg_nodup _ _ _ L2)) En); exact Ci.
    - unfold xicomps in Cf2; rewrite (map_nth_error fst _ _ Ei) in Cf2; congruence.
  Qed.

  (** ** Confluence under interleaved orchestration *)
  Local Notation FinalS := (FinalS K_eq_dec Σ prog' Kb).

  Theorem xdynamic_agree ins1 ins2 (γ1 γ2 : State) rs1 rs2 :
    XDRun (@init K Σ CC) [] ins1 γ1 rs1 -> XDRun (@init K Σ CC) [] ins2 γ2 rs2 ->
    xscomps ins1 = xscomps ins2 ->
    xquiet K_eq_dec Σ xprog γ1 -> xquiet K_eq_dec Σ xprog γ2 -> NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    AgreeL Σ (slab rs1 ins1) (slab rs2 ins2) (norm γ1) (norm γ2).
  Proof.
    intros R1 R2 Es Q1 Q2 NF1 NF2.
    assert (SL0 : SLInv (@init K Σ CC)) by (split; intros; discriminate).
    pose proof (pinv_init K_eq_dec Σ prog' Kb) as P0.
    destruct (xdrun_inv _ _ _ _ _ [] R1 xledger_init P0 SL0) as (L1 & P1 & S1).
    destruct (xdrun_inv _ _ _ _ _ [] R2 xledger_init P0 SL0) as (L2 & P2 & S2).
    cbn [app] in L1, L2.
    pose proof (final_norm2 K_eq_dec Σ C_eq_dec xprog Kb xrank Rb Hrank Hbnd NoOptChild γ1 P1 S1 Q1 NF1) as F1.
    pose proof (final_norm2 K_eq_dec Σ C_eq_dec xprog Kb xrank Rb Hrank Hbnd NoOptChild γ2 P2 S2 Q2 NF2) as F2.
    pose proof (fresh_norm K_eq_dec Σ C_eq_dec xprog Kb xrank Rb Hrank Hbnd γ1 P1 Q1 NF1) as Fr1.
    pose proof (fresh_norm K_eq_dec Σ C_eq_dec xprog Kb xrank Rb Hrank Hbnd γ2 P2 Q2 NF2) as Fr2.
    pose proof (xledger_rf γ1 _ rs1 ins1 L1 (rf_norm Σ xprog γ1)) as L1'.
    pose proof (xledger_rf γ2 _ rs2 ins2 L2 (rf_norm Σ xprog γ2)) as L2'.
    pose proof (proj1 (proj2 (proj1 F1))) as St1; pose proof (proj1 (proj2 (proj1 F2))) as St2.
    pose proof (proj2 (proj2 (proj1 F1))) as NF1'; pose proof (proj2 (proj2 (proj1 F2))) as NF2'.
    apply (final_agreeX K_eq_dec Σ xprog Kb xrank Rb Hrank Hbnd Hwb HTI HCom); try assumption.
    - exact (xledger_rootinj _ rs1 ins1 L1' St1 NF1').
    - exact (xledger_rootinj _ rs2 ins2 L2' St2 NF2').
    - exact (xledger_match _ _ rs1 rs2 ins1 ins2 L1' L2' Es St1 NF1').
    - exact (xledger_match _ _ rs2 rs1 ins2 ins1 L2' L1' (eq_sym Es) St2 NF2').
  Qed.

  (** The same inputs, in any interleaving. *)
  Corollary xdynamic_confluence ins (γ1 γ2 : State) rs1 rs2 :
    XDRun (@init K Σ CC) [] ins γ1 rs1 -> XDRun (@init K Σ CC) [] ins γ2 rs2 ->
    xquiet K_eq_dec Σ xprog γ1 -> xquiet K_eq_dec Σ xprog γ2 -> NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    AgreeL Σ (slab rs1 ins) (slab rs2 ins) (norm γ1) (norm γ2).
  Proof. intros R1 R2; exact (xdynamic_agree ins ins γ1 γ2 rs1 rs2 R1 R2 eq_refl). Qed.

  (** Static assembly: whatever the history, the quiet state agrees with
      that of an execution that only inserts the surviving components,
      once each, in their order of insertion. *)
  Corollary xstatic_assembly ins (γ γs : State) rs rss :
    XDRun (@init K Σ CC) [] ins γ rs -> XDRun (@init K Σ CC) [] (map IIns (scomps ins)) γs rss ->
    xquiet K_eq_dec Σ xprog γ -> xquiet K_eq_dec Σ xprog γs -> NoFailed Σ γ -> NoFailed Σ γs ->
    AgreeL Σ (slab rs ins) (slab rss (map IIns (scomps ins))) (norm γ) (norm γs).
  Proof.
    intros R Rs; apply (xdynamic_agree ins _ γ γs rs rss R Rs).
    unfold xscomps; rewrite scomps_static; reflexivity.
  Qed.
End OptDynamic.
