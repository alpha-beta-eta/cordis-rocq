(** * Hygienic keys: confluence under interleaved orchestration

    Counterpart of [Dynamic.dynamic_agree], [dynamic_confluence] and
    [static_assembly]: executions from the initial state that take
    orchestration inputs interleaved in any way with extended lifecycle
    steps, and end quiet with no failed fiber, agree up to renaming once
    the stale selections of their Inactive roots are normalised, when their
    inputs leave the same surviving components in the same order; and every
    exported name is resolved alike, with the same ties.

    This rests on roots being scoped by their orchestrator-given instance
    id ([Scoped.xinst]): a root's scope, hence every key in its subtree, is
    the same in both executions, whatever the interleaving.

    The inputs name base components, and an insertion goes through
    [X-Insert] (so an instance id already in use is refused). The input
    lemmas ([slab], [scomps], ...) are the core's ([Dynamic.v]). What
    changes:
    - The root ledger ([KLedger]) records base components, and that a root
      has scope [[Rt (xinst c)]], no private environment and stamp [0].
    - Its preservation under an extended lifecycle step is proved once from
      four facts about the step ([KFrame]), as in [Ext/OptDynamic.v].
    - The final comparison is [ScopedSpawn.final_agreeX]. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering
  Recovery Progress Termination Confluence StateInv Episode StateConf SpawnConf Dynamic.
From CordisKeys Require Import Scoped ScopedSafety ScopedTerm ScopedProgress ScopedConf ScopedSpawn.
Import ListNotations.

Section ScopedDynamic.
  Context {N : Type} (N_eq_dec : forall x y : N, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (xprog : C -> @XComponent N Σ C).

  Local Notation XC := (@XC N C).
  Local Notation Key := (@Key N).
  Local Notation State := (@State Key Σ XC).
  Local Notation Fiber := (@Fiber Key Σ XC).
  Local Notation Input := (@Input C).
  Local Notation S := (St Σ).
  Local Notation fibers := (fibers Σ).
  Local Notation next := (Calculus.next Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation fparent := (Calculus.parent Σ).
  Local Notation disposed := (Calculus.disposed Σ).
  Local Notation is_installed := (is_installed Σ).
  Local Notation kdec := (key_eq_dec N_eq_dec).
  Local Notation prog' := (prog' N_eq_dec Σ xprog).
  Local Notation step := (step kdec Σ prog').
  Local Notation kstep := (kstep N_eq_dec Σ xprog).
  Local Notation recomp := (recomp N_eq_dec Σ xprog).
  Local Notation select := (select N_eq_dec Σ xprog).
  Local Notation SI := (SI N_eq_dec Σ xprog).
  Local Notation kquiet := (kquiet N_eq_dec Σ xprog).
  Local Notation xprovs c := (xprovs Σ xprog c).
  Local Notation xinst c := (xinst Σ (xprog c)).

  (** ** Hypotheses, as for [kspawn_confluence] *)
  Variable Kb : nat.
  Hypothesis kHK : forall c, Termination.Bounded Σ Kb (xbody Σ (xprog c)).
  Variable xrank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', KAbove Σ xprog c c' -> xrank c < xrank c'.
  Hypothesis Hbnd : forall c, xrank c <= Rb.
  Hypothesis kTotal : forall c y, In y (xprovs c) -> AllDoneProv Σ y (xbody Σ (xprog c)).
  Hypothesis kSub : forall c c', KSpawns Σ xprog c c' -> forall y, In y (globals Σ xprog c') -> In y (globals Σ xprog c).
  Hypothesis Hwb : forall a t, WellBehaved (Σ := Σ) a t.
  Hypothesis HUI : forall (a : Op Σ) (t : nat) (s1 s2 s1' s2' : S) (g1 g2 : S -> S) (o1 o2 : Out Σ),
    run a t s1 = Some (s1', g1, o1) -> run a t s2 = Some (s2', g2, o2) -> fun_eq (Σ := Σ) g1 g2.
  Hypothesis HTI : forall (a : Op Σ) (t t' : nat) (s : S),
    match run a t s, run a t' s with
    | None, None => True
    | Some (s1, _, o1), Some (s2, _, o2) => @st_eq Σ s1 s2 /\ o1 = o2
    | _, _ => False
    end.
  Hypothesis HRI : forall (k : Key) (a b : Op Σ) (ta tb : nat) (g : S -> S),
    CoPair Σ prog' k a b -> ta <> tb -> yields (Σ := Σ) a ta g ->
    forall x, After (CoPair Σ prog' k a) a ta x -> shifted_ok (Σ := Σ) g (run b tb x) (run b tb (g x)).
  Hypothesis HCom : forall (k : Key) (a b : Op Σ) (ta tb : nat), CoPair Σ prog' k a b -> ta <> tb ->
    Commute (Σ := Σ) a ta b tb.

  Local Notation rank' := (fun x : XC => xrank (base x)).
  Local Notation HK' := (HK' N_eq_dec Σ xprog Kb kHK).
  Local Notation Total' := (Total' N_eq_dec Σ xprog kTotal).
  Local Notation Hrank2 := (Hrank2 N_eq_dec Σ xprog xrank Hrank).
  Local Notation PInv := (PInv kdec Σ prog' Kb).
  Local Notation SLInv := (SLInv Σ).
  Local Notation pinv_step :=
    (pinv_step kdec Σ prog' Kb HK' rank' Hrank2 Total' Hwb HUI HTI HRI HCom).
  Local Notation kstep_inv :=
    (kstep_inv N_eq_dec Σ xprog Kb kHK xrank Hrank kTotal Hwb HUI HTI HRI HCom).
  Local Notation norm := (norm N_eq_dec Σ xprog).

  (** ** Executions *)
  Definition kradd (rs : list nat) (γ : State) (x : Input) : list nat :=
    match x with IIns _ => rs ++ [next γ] | _ => rs end.

  Inductive KDRun : State -> list nat -> list Input -> State -> list nat -> Prop :=
  | kdr_nil γ rs : KDRun γ rs [] γ rs
  | kdr_life γ rs ins n ℓ γ1 γ2 rs2 :
      In ℓ (@lifecycle_labels C n) -> kstep γ ℓ = Some γ1 -> KDRun γ1 rs ins γ2 rs2 ->
      KDRun γ rs ins γ2 rs2
  | kdr_orch γ rs x ins ℓ γ1 γ2 rs2 :
      olabel rs x = Some ℓ -> kstep γ ℓ = Some γ1 -> KDRun γ1 (kradd rs γ x) ins γ2 rs2 ->
      KDRun γ rs (x :: ins) γ2 rs2.

  (** An orchestration input is a core step of [prog']. *)
  Lemma korch_core (γ γ1 : State) rs x ℓ :
    olabel rs x = Some ℓ -> kstep γ ℓ = Some γ1 -> step γ (klab Σ xprog γ ℓ) = Some γ1.
  Proof.
    intros Ho H; destruct x as [c|i|i|i]; cbn [olabel] in Ho.
    - injection Ho as <-; cbn [Scoped.kstep] in H.
      destruct (taken Σ γ (xinst c)); [discriminate | exact H].
    - destruct (nth_error rs i); cbn in Ho; [|discriminate]; injection Ho as <-; exact H.
    - destruct (nth_error rs i); cbn in Ho; [|discriminate]; injection Ho as <-; exact H.
    - destruct (nth_error rs i); cbn in Ho; [|discriminate]; injection Ho as <-; exact H.
  Qed.

  Lemma klab_not_react rs x ℓ (γ : State) : olabel rs x = Some ℓ -> forall n i, klab Σ xprog γ ℓ <> OReact n i.
  Proof.
    destruct x as [c|i|i|i]; cbn; [intros [= <-]; discriminate|..];
      destruct (nth_error rs i); cbn; intros E; try discriminate; injection E as <-; discriminate.
  Qed.

  (** ** The root ledger *)
  Definition RootShape (f : Fiber) : Prop :=
    scope (fcomp f) = [Rt (xinst (base (fcomp f)))] /\ env (fcomp f) = [] /\ tick (fcomp f) = 0.

  Record KLedger (γ : State) (rs : list nat) (done : list Input) : Prop := {
    kg_len : length rs = length (icomps done);
    kg_nodup : NoDup rs;
    kg_lt : forall n, In n rs -> n < next γ;
    kg_dis : forall i, In (IDis i) done -> i < length rs;
    kg_at : forall i n, nth_error rs i = Some n ->
      (fibers γ n = None /\ In (IDis i) done) \/
      (exists f, fibers γ n = Some f /\ fparent f = None /\
         nth_error (icomps done) i = Some (base (fcomp f)) /\ RootShape f /\
         (disposed f = true <-> In (IDis i) done));
    kg_root : forall n f, fibers γ n = Some f -> fparent f = None -> In n rs
  }.

  Lemma kledger_init : KLedger (@init Key Σ XC) [] [].
  Proof.
    split; cbn; try (intros; contradiction); try reflexivity; [constructor | | ].
    - intros [|i] n E; discriminate.
    - intros n f E; discriminate.
  Qed.

  (** What a lifecycle step may do to fibers. *)
  Definition KFrame (γ γ' : State) : Prop :=
    next γ <= next γ' /\
    (forall n f', fibers γ n = None -> fibers γ' n = Some f' -> next γ <= n) /\
    (forall n f f', fibers γ n = Some f -> fibers γ' n = Some f' -> fparent f' = fparent f) /\
    KRootKeep Σ γ γ'.

  Lemma kledger_frame (γ γ' : State) rs done :
    KLedger γ rs done -> KFrame γ γ' -> KLedger γ' rs done.
  Proof.
    intros L (Hnx & Hnew & Hpar & [RK1 RK2]).
    split; [exact (kg_len _ _ _ L) | exact (kg_nodup _ _ _ L) | | exact (kg_dis _ _ _ L) | |].
    - intros n Hn; pose proof (kg_lt _ _ _ L n Hn); lia.
    - intros i n Hn.
      pose proof (kg_lt _ _ _ L n (nth_error_In _ _ Hn)) as Hlt.
      destruct (kg_at _ _ _ L i n Hn) as [[Nn D]|(f & Hf & Pf & Cf & (Rs & Re & Rt') & Df)].
      + left; split; [|exact D].
        destruct (fibers γ' n) as [f'|] eqn:E; [|reflexivity].
        pose proof (Hnew n f' Nn E); lia.
      + destruct (fibers γ' n) as [f'|] eqn:E.
        * right; exists f'.
          assert (Pf' : fparent f' = None) by (rewrite (Hpar n f f' Hf E); exact Pf).
          destruct (RK1 n f' E Pf') as (f0 & H0 & _ & B0 & S0 & E0 & T0 & D0).
          rewrite Hf in H0; injection H0 as <-.
          split; [reflexivity|]; split; [exact Pf'|]; split; [rewrite <- B0; exact Cf|].
          split; [split; [|split]; congruence|].
          rewrite <- D0; exact Df.
        * left; split; [reflexivity|]; apply Df.
          destruct (disposed f) eqn:Hd; [reflexivity|].
          destruct (RK2 n f Hf Pf Hd) as (f' & Hf' & _); congruence.
    - intros n f' Hn Hp; destruct (RK1 n f' Hn Hp) as (f & Hf & Pf & _); exact (kg_root _ _ _ L n f Hf Pf).
  Qed.

  Lemma core_frame (γ γ' : State) ℓ :
    WF kdec Σ prog' γ -> step γ ℓ = Some γ' ->
    next γ <= next γ' /\
    (forall n f', fibers γ n = None -> fibers γ' n = Some f' -> next γ <= n) /\
    (forall n f f', fibers γ n = Some f -> fibers γ' n = Some f' -> fparent f' = fparent f).
  Proof.
    intros W H; split; [exact (step_next kdec Σ prog' γ γ' ℓ H)|]; split.
    - intros n f' Nn E; destruct (new_fiber kdec Σ prog' γ γ' ℓ n f' W H Nn E) as [-> _]; lia.
    - intros n f f' Hf Hf'; exact (proj1 (proj2 (fiber_step kdec Σ prog' γ γ' ℓ n f f' W H Hf Hf'))).
  Qed.

  Lemma kstep_frame (γ γ' : State) n ℓ :
    PInv γ -> SLInv γ -> SI γ -> In ℓ (@lifecycle_labels C n) -> kstep γ ℓ = Some γ' -> KFrame γ γ'.
  Proof.
    intros P SL I Hin H.
    destruct (kstep_inv γ γ' n ℓ P SL I Hin H) as (_ & _ & _ & RK).
    pose proof (sinv_wf kdec Σ prog' Kb γ (p_s _ _ _ _ _ P)) as W.
    split; [|split; [|split; [|exact RK]]];
      destruct (kstep_core N_eq_dec Σ xprog γ γ' ℓ H)
        as [St|[(m & f & _ & Hm & Hl & _ & Hp & St)|[(m & St)|(m & i & f & E & _)]]];
      try (destruct (core_frame γ γ' _ W St) as (A & B & C'); assumption);
      try (subst ℓ; exfalso; cbn in Hin; intuition discriminate).
    all: assert (Hi : is_installed (life f) = false) by (rewrite Hl; reflexivity).
    all: pose proof (rf2_recomp N_eq_dec Σ xprog γ m f Hm Hi Hp) as R2;
      pose proof (rf2_pinv N_eq_dec Σ xprog Kb γ _ P R2) as Pr; rewrite <- recomp_with in Pr;
      destruct (core_frame _ γ' _ (sinv_wf kdec Σ prog' Kb _ (p_s _ _ _ _ _ Pr)) St) as (A & B & C').
    - exact A.
    - intros k f' Nk E; apply (B k f'); [|exact E].
      unfold Scoped.recomp; rewrite fibers_refiber; destruct (Nat.eqb_spec k m) as [->|]; [congruence | exact Nk].
    - intros k g g' Hg Hg'.
      destruct (fibers (recomp γ m f) k) as [g0|] eqn:E0.
      + rewrite (C' k g0 g' E0 Hg').
        unfold Scoped.recomp in E0; rewrite fibers_refiber in E0; destruct (Nat.eqb_spec k m) as [->|].
        * injection E0 as <-; rewrite Hm in Hg; injection Hg as <-; reflexivity.
        * congruence.
      + unfold Scoped.recomp in E0; rewrite fibers_refiber in E0; destruct (Nat.eqb_spec k m); [discriminate | congruence].
  Qed.

  (** ** Orchestration steps keep the ledger *)
  Lemma kledger_setf (γ : State) rs done x i n f f' :
    KLedger γ rs done -> nth_error rs i = Some n -> fibers γ n = Some f ->
    fcomp f' = fcomp f -> fparent f' = fparent f ->
    icomps [x] = [] -> (forall j, In (IDis j) [x] -> j = i) ->
    (disposed f' = true <-> disposed f = true \/ In (IDis i) [x]) ->
    KLedger (set_fiber Σ γ n f') rs (done ++ [x]).
  Proof.
    intros L Hn Hf Ec Ep Ex Hx Hd.
    assert (F : forall m, fibers (set_fiber Σ γ n f') m = if Nat.eqb m n then Some f' else fibers γ m)
      by (intros; reflexivity).
    assert (Di : forall j, In (IDis j) (done ++ [x]) <-> In (IDis j) done \/ (j = i /\ In (IDis j) [x])).
    { intros j; rewrite in_app_iff; split; [intros [A|A]; [left; exact A | right; split; [exact (Hx j A) | exact A]]|].
      intros [A|[_ A]]; [left | right]; exact A. }
    assert (Ic : icomps (done ++ [x]) = icomps done) by (rewrite icomps_app, Ex, app_nil_r; reflexivity).
    split; [rewrite Ic; exact (kg_len _ _ _ L) | exact (kg_nodup _ _ _ L) | exact (kg_lt _ _ _ L) | | |].
    - intros j Hj; apply Di in Hj as [Hj|[-> _]]; [exact (kg_dis _ _ _ L j Hj)|].
      apply nth_error_Some; congruence.
    - intros j m Hm; rewrite F, Ic.
      destruct (Nat.eqb_spec m n) as [->|Hne].
      + assert (j = i) as ->.
        { apply (proj1 (NoDup_nth_error rs) (kg_nodup _ _ _ L) j i); [apply nth_error_Some | ]; congruence. }
        destruct (kg_at _ _ _ L i n Hn) as [[Nn _]|(f0 & Hf0 & Pf0 & Cf0 & Rf0 & Df0)]; [congruence|].
        rewrite Hf in Hf0; injection Hf0 as <-.
        right; exists f'; split; [reflexivity|]; split; [congruence|]; split; [rewrite Ec; exact Cf0|].
        split; [unfold RootShape; rewrite Ec; exact Rf0|].
        rewrite Hd, Df0, Di; split; [intros [A|A]; [left; exact A | right; split; [reflexivity | exact A]]|].
        intros [A|[_ A]]; [left | right]; exact A.
      + assert (Hji : j <> i) by (intros ->; congruence).
        destruct (kg_at _ _ _ L j m Hm) as [[Nm D]|(f0 & Hf0 & Pf0 & Cf0 & Rf0 & Df0)].
        * left; split; [exact Nm | apply Di; left; exact D].
        * right; exists f0; split; [exact Hf0|]; split; [exact Pf0|]; split; [exact Cf0|].
          split; [exact Rf0|]; split.
          -- intros A; apply Di; left; apply Df0; exact A.
          -- intros A; apply Df0; apply Di in A as [A|[E _]]; [exact A | contradiction].
    - intros m fm Hm Hp; rewrite F in Hm.
      destruct (Nat.eqb_spec m n) as [->|]; [exact (nth_error_In _ _ Hn)|].
      exact (kg_root _ _ _ L m fm Hm Hp).
  Qed.

  Lemma kledger_orch (γ γ' : State) rs done x ℓ :
    KLedger γ rs done -> olabel rs x = Some ℓ -> kstep γ ℓ = Some γ' ->
    KLedger γ' (kradd rs γ x) (done ++ [x]).
  Proof.
    intros L Ho H.
    pose proof (korch_core γ γ' rs x ℓ Ho H) as St.
    destruct x as [c|i|i|i]; cbn [olabel] in Ho.
    - injection Ho as <-; cbn [klab Calculus.step] in St.
      destruct (Calculus.conflict kdec Σ prog' γ _); [discriminate|]; injection St as <-.
      cbn [kradd].
      assert (Ic : icomps (done ++ [IIns c]) = icomps done ++ [c]) by (rewrite icomps_app; reflexivity).
      pose proof (kg_lt _ _ _ L) as Lt.
      assert (Nin : ~ In (next γ) rs) by (intros A; pose proof (Lt _ A); lia).
      set (nf := mkFiber Σ (mkXC c [Rt (xinst c)] [] [] 0) None false (Inactive Σ None)).
      assert (F : forall m, fibers (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ) (Some nf)))) m =
                            if Nat.eqb m (next γ) then Some nf else fibers γ m) by (intros; reflexivity).
      assert (Di : forall j, In (IDis j) (done ++ [IIns c]) <-> In (IDis j) done).
      { intros j; rewrite in_app_iff; cbn; split; [intros [A|[A|[]]]; [exact A | discriminate] | intros A; left; exact A]. }
      assert (Lx : length (icomps done) = length rs) by (symmetry; exact (kg_len _ _ _ L)).
      split.
      + rewrite Ic, !length_app, (kg_len _ _ _ L); reflexivity.
      + apply NoDup_app; [exact (kg_nodup _ _ _ L) | constructor; [intros [] | constructor] |].
        intros a A [<-|[]]; exact (Nin A).
      + intros n Hn; cbn; apply in_app_iff in Hn as [Hn|[<-|[]]]; [pose proof (Lt n Hn); lia | lia].
      + intros j Hj; apply Di in Hj; rewrite length_app; pose proof (kg_dis _ _ _ L j Hj); cbn; lia.
      + intros j n Hn; rewrite F, Di, Ic.
        destruct (Nat.lt_ge_cases j (length rs)) as [Hj|Hj].
        * rewrite nth_error_app1 in Hn by exact Hj.
          assert (Hne : n <> next γ) by (intros ->; exact (Nin (nth_error_In _ _ Hn))).
          rewrite (proj2 (Nat.eqb_neq n (next γ)) Hne).
          destruct (kg_at _ _ _ L j n Hn) as [A|(f & Hf & Pf & Cf & Rf & Df)]; [left; exact A|].
          right; exists f; split; [exact Hf|]; split; [exact Pf|].
          split; [rewrite nth_error_app1; [exact Cf|]; rewrite Lx; exact Hj|].
          split; [exact Rf|].
          split; [intros A; apply Di; exact (proj1 Df A) | intros A; apply Df, Di; exact A].
        * rewrite nth_error_app2 in Hn by exact Hj.
          destruct (j - length rs) as [|q] eqn:Eq; cbn in Hn; [|destruct q; discriminate].
          injection Hn as <-; rewrite Nat.eqb_refl.
          right; exists nf; split; [reflexivity|]; split; [reflexivity|]; split.
          -- rewrite nth_error_app2 by (rewrite Lx; exact Hj).
             rewrite Lx, Eq; reflexivity.
          -- split; [unfold RootShape; cbn; auto|].
             cbn; split; [discriminate | intros A; apply Di in A; pose proof (kg_dis _ _ _ L j A); lia].
      + intros n f Hn Hp; rewrite F in Hn; apply in_app_iff.
        destruct (Nat.eqb_spec n (next γ)) as [->|]; [right; left; reflexivity|].
        left; exact (kg_root _ _ _ L n f Hn Hp).
    - destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
      cbn [klab Calculus.step] in St; destruct (fibers γ n) as [f|] eqn:Hf; [|discriminate]; injection St as <-.
      apply (kledger_setf γ rs done _ i n f _ L Hn Hf); try reflexivity.
      + intros j [E|[]]; injection E as ->; reflexivity.
      + cbn; split; [intros _; right; left; reflexivity | reflexivity].
    - destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
      cbn [klab] in St.
      destruct (restart_shape kdec Σ prog' γ γ' n St) as (f & acc & w & Hf & _ & _ & ->).
      apply (kledger_setf γ rs done _ i n f _ L Hn Hf); try reflexivity.
      + intros j [E|[]]; discriminate.
      + cbn; split; [intros A; left; exact A | intros [A|[E|[]]]; [exact A | discriminate]].
    - destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
      cbn [klab Calculus.step] in St; destruct (fibers γ n) as [f|] eqn:Hf; [|discriminate].
      destruct (life f) as [[z|]| | |]; try discriminate; injection St as <-.
      apply (kledger_setf γ rs done _ i n f _ L Hn Hf); try reflexivity.
      + intros j [E|[]]; discriminate.
      + cbn; split; [intros A; left; exact A | intros [A|[E|[]]]; [exact A | discriminate]].
  Qed.

  (** ** Along an execution *)
  Lemma kdrun_inv (γ γ' : State) rs ins rs' done :
    KDRun γ rs ins γ' rs' -> KLedger γ rs done -> PInv γ -> SLInv γ -> SI γ ->
    KLedger γ' rs' (done ++ ins) /\ PInv γ' /\ SLInv γ' /\ SI γ'.
  Proof.
    intros R; revert done; induction R as [γ rs|γ rs ins n ℓ γ1 γ2 rs2 Hl Hs R IH|γ rs x ins ℓ γ1 γ2 rs2 Ho Hs R IH];
      intros done L P SL I.
    - rewrite app_nil_r; auto.
    - destruct (kstep_inv γ γ1 n ℓ P SL I Hl Hs) as (P1 & S1 & I1 & _).
      apply IH; [exact (kledger_frame γ γ1 rs done L (kstep_frame γ γ1 n ℓ P SL I Hl Hs)) | exact P1 | exact S1 | exact I1].
    - replace (done ++ x :: ins) with ((done ++ [x]) ++ ins) by (rewrite <- app_assoc; reflexivity).
      pose proof (korch_core γ γ1 rs x ℓ Ho Hs) as St.
      pose proof (sinv_wf kdec Σ prog' Kb γ (p_s _ _ _ _ _ P)) as W.
      assert (SL1 : SLInv γ1).
      2: { exact (IH _ (kledger_orch γ γ1 rs done x ℓ L Ho Hs)
                   (pinv_step γ γ1 _ (klab_not_react rs x ℓ γ Ho) P St) SL1
                   (si_kstep N_eq_dec Σ xprog γ γ1 ℓ W I Hs)). }
      destruct x as [c|i|i|i]; cbn [olabel] in Ho.
      + injection Ho as <-; exact (sl_insert kdec Σ prog' Kb γ γ1 _ P SL St).
      + destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
        destruct (kg_at _ _ _ L i n Hn) as [[Nn _]|(f & Hf & Pf & _)].
        * cbn [klab Calculus.step] in St; rewrite Nn in St; discriminate.
        * exact (sl_dispose kdec Σ prog' Kb γ γ1 n f P SL Hf Pf St).
      + destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
        exact (sl_restart kdec Σ prog' γ γ1 n SL St).
      + destruct (nth_error rs i) as [n|] eqn:Hn; cbn in Ho; [|discriminate]; injection Ho as <-.
        exact (sl_reset kdec Σ prog' γ γ1 n SL St).
  Qed.

  (** ** Final roots *)
  Lemma kledger_rf (γ : State) F rs done :
    KLedger γ rs done -> RF Σ γ F -> KLedger (with_fibers Σ γ F) rs done.
  Proof.
    intros L R; apply (kledger_frame γ _ rs done L).
    pose proof R as [R1 R2]; split; [reflexivity|]; split; [|split; [|exact (krk_rf Σ γ F R)]].
    - intros n f' Nn E; destruct (R1 n f' E) as (f0 & H0 & _); congruence.
    - intros n f f' Hf Hf'; destruct (R1 n f' Hf') as (f0 & H0 & _ & Ep & _); congruence.
  Qed.

  Lemma kfinal_slab (γ : State) rs ins n f :
    KLedger γ rs ins -> settled Σ prog' γ -> NoFailed Σ γ ->
    fibers γ n = Some f -> fparent f = None ->
    nth_error (sroots rs ins) (slab rs ins n) = Some n /\
    nth_error (scomps ins) (slab rs ins n) = Some (base (fcomp f)) /\ RootShape f.
  Proof.
    intros L St NF Hn Pn.
    pose proof (nth_pos rs n (kg_root _ _ _ L n f Hn Pn)) as E.
    destruct (settled_shape Σ prog' γ n f St NF Hn) as [Hd _].
    destruct (kg_at _ _ _ L _ n E) as [[Nn _]|(f0 & Hf0 & _ & Cf & Rf & Df)]; [congruence|].
    rewrite Hn in Hf0; injection Hf0 as <-.
    assert (Lv : live_ix ins (pos rs n) = true) by (apply live_ix_spec; intros A; apply Df in A; congruence).
    pose proof (keepi_nth (live_ix ins) rs 0 _ n E Lv) as En.
    assert (Es : slab rs ins n = cnt (live_ix ins) 0 (pos rs n)).
    { exact (pos_nth _ _ n (keepi_nodup _ _ _ (kg_nodup _ _ _ L)) En). }
    split; [rewrite Es; exact En|]; split; [|exact Rf].
    unfold scomps; rewrite Es.
    exact (keepi_nth (live_ix ins) (icomps ins) 0 _ _ Cf Lv).
  Qed.

  Lemma kledger_rootinj (γ : State) rs ins :
    KLedger γ rs ins -> settled Σ prog' γ -> NoFailed Σ γ -> RootInj Σ (slab rs ins) γ.
  Proof.
    intros L St NF n n' f f' Hn Pn Hn' Pn' E.
    destruct (kfinal_slab γ rs ins n f L St NF Hn Pn) as (A & _).
    destruct (kfinal_slab γ rs ins n' f' L St NF Hn' Pn') as (B & _).
    rewrite E in A; congruence.
  Qed.

  Lemma kledger_match (γ1 γ2 : State) rs1 rs2 ins1 ins2 :
    KLedger γ1 rs1 ins1 -> KLedger γ2 rs2 ins2 -> scomps ins1 = scomps ins2 ->
    settled Σ prog' γ1 -> NoFailed Σ γ1 ->
    RootsMatchX Σ (slab rs1 ins1) (slab rs2 ins2) γ1 γ2.
  Proof.
    intros L1 L2 Es St NF n f1 Hn Pn.
    destruct (kfinal_slab γ1 rs1 ins1 n f1 L1 St NF Hn Pn) as (_ & Cs & (Rs1 & Re1 & Rt1)).
    rewrite Es in Cs; unfold scomps in Cs.
    destruct (keepi_surj _ _ _ _ _ Cs) as (i & Lv & Ci & Ei); cbn in Lv.
    assert (Hi : i < length rs2) by (rewrite (kg_len _ _ _ L2); apply nth_error_Some; intros Nn; rewrite Ei in Nn; discriminate Nn).
    destruct (nth_error rs2 i) as [n2|] eqn:E2; [|apply nth_error_None in E2; lia].
    destruct (kg_at _ _ _ L2 i n2 E2) as [[_ D]|(f2 & Hf2 & Pf2 & Cf2 & (Rs2 & Re2 & Rt2) & _)].
    { apply live_ix_spec in Lv; contradiction. }
    assert (Eb : base (fcomp f2) = base (fcomp f1)) by congruence.
    exists n2, f2; split; [exact Hf2|]; split; [exact Pf2|]; split.
    - pose proof (keepi_nth (live_ix ins2) rs2 0 i n2 E2 Lv) as En.
      change (slab rs2 ins2 n2) with (pos (keepi (live_ix ins2) rs2 0) n2).
      rewrite (pos_nth _ _ n2 (keepi_nodup _ _ _ (kg_nodup _ _ _ L2)) En); exact Ci.
    - split; [exact Eb|]; split; [rewrite Rs1, Rs2, Eb; reflexivity|]; split; congruence.
  Qed.

  (** ** Confluence under interleaved orchestration *)
  Theorem kdynamic_agree ins1 ins2 (γ1 γ2 : State) rs1 rs2 :
    KDRun (@init Key Σ XC) [] ins1 γ1 rs1 -> KDRun (@init Key Σ XC) [] ins2 γ2 rs2 ->
    scomps ins1 = scomps ins2 ->
    kquiet γ1 -> kquiet γ2 -> NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    AgreeL Σ (slab rs1 ins1) (slab rs2 ins2) (norm γ1) (norm γ2) /\
    (forall y, select γ1 y = select γ2 y /\ tied N_eq_dec Σ xprog γ1 y = tied N_eq_dec Σ xprog γ2 y).
  Proof.
    intros R1 R2 Es Q1 Q2 NF1 NF2.
    assert (SL0 : SLInv (@init Key Σ XC)) by (split; intros; discriminate).
    pose proof (pinv_init kdec Σ prog' Kb) as P0.
    pose proof (si_init N_eq_dec Σ xprog) as I0.
    destruct (kdrun_inv _ _ _ _ _ [] R1 kledger_init P0 SL0 I0) as (L1 & P1 & S1 & I1).
    destruct (kdrun_inv _ _ _ _ _ [] R2 kledger_init P0 SL0 I0) as (L2 & P2 & S2 & I2).
    cbn [app] in L1, L2.
    pose proof (final_norm2 N_eq_dec Σ xprog Kb xrank Rb Hrank Hbnd kSub γ1 P1 S1 I1 Q1 NF1) as F1.
    pose proof (final_norm2 N_eq_dec Σ xprog Kb xrank Rb Hrank Hbnd kSub γ2 P2 S2 I2 Q2 NF2) as F2.
    pose proof (fresh_norm N_eq_dec Σ xprog Kb xrank Rb Hrank Hbnd kSub γ1 P1 I1 Q1 NF1) as Fr1.
    pose proof (fresh_norm N_eq_dec Σ xprog Kb xrank Rb Hrank Hbnd kSub γ2 P2 I2 Q2 NF2) as Fr2.
    pose proof (si_rf N_eq_dec Σ xprog γ1 _ (t_wf _ _ _ _ _ (pinv_tinv N_eq_dec Σ xprog Kb γ1 P1)) I1 (rf2_norm N_eq_dec Σ xprog γ1)) as N1.
    pose proof (si_rf N_eq_dec Σ xprog γ2 _ (t_wf _ _ _ _ _ (pinv_tinv N_eq_dec Σ xprog Kb γ2 P2)) I2 (rf2_norm N_eq_dec Σ xprog γ2)) as N2.
    pose proof (kledger_rf γ1 _ rs1 ins1 L1 (rf_norm N_eq_dec Σ xprog γ1)) as L1'.
    pose proof (kledger_rf γ2 _ rs2 ins2 L2 (rf_norm N_eq_dec Σ xprog γ2)) as L2'.
    pose proof (proj1 (proj2 (proj1 F1))) as St1; pose proof (proj1 (proj2 (proj1 F2))) as St2.
    pose proof (proj2 (proj2 (proj1 F1))) as NF1'; pose proof (proj2 (proj2 (proj1 F2))) as NF2'.
    pose proof (kledger_rootinj _ rs1 ins1 L1' St1 NF1') as RI1.
    pose proof (kledger_rootinj _ rs2 ins2 L2' St2 NF2') as RI2.
    pose proof (kledger_match _ _ rs1 rs2 ins1 ins2 L1' L2' Es St1 NF1') as RM12.
    pose proof (kledger_match _ _ rs2 rs1 ins2 ins1 L2' L1' (eq_sym Es) St2 NF2') as RM21.
    split.
    - exact (final_agreeX N_eq_dec Σ xprog Kb xrank Rb Hrank Hbnd Hwb HTI HCom _ _ _ _
               F1 F2 N1 N2 Fr1 Fr2 RI1 RI2 RM12 RM21).
    - intros y.
      destruct (corresp_allX N_eq_dec Σ xprog Kb xrank Hrank Hwb _ _ _ _
                  F1 F2 N1 N2 Fr1 Fr2 RI1 RI2 RM12 RM21 (Datatypes.S Rb)) as [C12 C21].
      assert (HE : forall c', In y (xexports Σ (xprog c')) -> xrank c' < Datatypes.S Rb)
        by (intros c' _; pose proof (Hbnd c'); lia).
      destruct (select_corr N_eq_dec Σ xprog Kb xrank _ _ _ _ _ y F1 F2 N1 N2 RI1 RI2 C12 C21 HE)
        as [Es' Et].
      unfold ScopedSpawn.norm in Es', Et.
      rewrite (select_rf N_eq_dec Σ xprog γ1 _ y (rf_norm N_eq_dec Σ xprog γ1)),
              (select_rf N_eq_dec Σ xprog γ2 _ y (rf_norm N_eq_dec Σ xprog γ2)) in Es'.
      rewrite (tied_rf N_eq_dec Σ xprog γ1 _ y (rf_norm N_eq_dec Σ xprog γ1)),
              (tied_rf N_eq_dec Σ xprog γ2 _ y (rf_norm N_eq_dec Σ xprog γ2)) in Et.
      auto.
  Qed.

  (** The same inputs, in any interleaving. *)
  Corollary kdynamic_confluence ins (γ1 γ2 : State) rs1 rs2 :
    KDRun (@init Key Σ XC) [] ins γ1 rs1 -> KDRun (@init Key Σ XC) [] ins γ2 rs2 ->
    kquiet γ1 -> kquiet γ2 -> NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    AgreeL Σ (slab rs1 ins) (slab rs2 ins) (norm γ1) (norm γ2) /\
    (forall y, select γ1 y = select γ2 y /\ tied N_eq_dec Σ xprog γ1 y = tied N_eq_dec Σ xprog γ2 y).
  Proof. intros R1 R2; exact (kdynamic_agree ins ins γ1 γ2 rs1 rs2 R1 R2 eq_refl). Qed.

  (** Static assembly: whatever the history, the quiet state agrees with
      that of an execution that only inserts the surviving components,
      once each, in their order of insertion. *)
  Corollary kstatic_assembly ins (γ γs : State) rs rss :
    KDRun (@init Key Σ XC) [] ins γ rs -> KDRun (@init Key Σ XC) [] (map IIns (scomps ins)) γs rss ->
    kquiet γ -> kquiet γs -> NoFailed Σ γ -> NoFailed Σ γs ->
    AgreeL Σ (slab rs ins) (slab rss (map IIns (scomps ins))) (norm γ) (norm γs) /\
    (forall y, select γ y = select γs y /\ tied N_eq_dec Σ xprog γ y = tied N_eq_dec Σ xprog γs y).
  Proof.
    intros R Rs; apply (kdynamic_agree ins _ γ γs rs rss R Rs).
    rewrite scomps_static; reflexivity.
  Qed.
End ScopedDynamic.
