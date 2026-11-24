(** * Extension 1: termination with optional dependencies

    Counterpart of [Termination.termination]: extended lifecycle steps
    alone cannot go on for ever, from any state satisfying the invariant
    [XTInv], in particular from any state an extended execution reaches
    ([xtermination_reachable]). No restriction on children is needed.

    The core measure cannot be reused as it stands: it reads the core
    target, and a fiber whose optional dependency appeared still has its
    core target, though it must reload. The measure here ([xmu]) has the
    same shape, with two changes:
    - a Loading or Active fiber is "on target" when its presence is still
      current and the core target equals its view ([xtis]);
    - whether a fiber about to finish unloading, or Inactive, would begin
      again is read from the target it would have after re-choosing its
      presence ([bt]).
    As in the core, the state measure is a vector indexed by rank and drops
    lexicographically at every step. What makes this work: a step of [n]
    changes neither the visibility of a key a fiber of rank at most that of
    [n] depends on, required or optional, nor its presence ([vis_stable],
    [present_stable]), because the rank rises along optional edges too.

    The core's [lstep_effects] and [tinv_step] are reused through the table
    [OptProgress.progG], which satisfies the core's [Inv2] where [prog']
    may not (a child's presence may have been re-chosen). *)

From Stdlib Require Import List PeanoNat Bool Lia Wf_nat Compare_dec.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Recovery Progress Termination.
From Cordis Require Import Ext.Optional Ext.OptProgress.
Import ListNotations.

Section OptTermination.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (C_eq_dec : forall x y : C, {x = y} + {x <> y}).
  Context (xprog : C -> @XComponent K Σ C).

  Local Notation CC := (@Optional.C' K C).
  Local Notation State := (@State K Σ CC).
  Local Notation Fiber := (@Fiber K Σ CC).
  Local Notation Life := (@Life K Σ CC).
  Local Notation Undo := (@Undo K Σ).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation next := (Calculus.next Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation fparent := (Calculus.parent Σ).
  Local Notation disposed := (Calculus.disposed Σ).
  Local Notation acc_of := (acc_of Σ).
  Local Notation owner := (owner Σ).
  Local Notation prog' := (prog' K_eq_dec Σ xprog).
  Local Notation step := (step K_eq_dec Σ prog').
  Local Notation xstep := (xstep K_eq_dec Σ xprog).
  Local Notation recomp := (recomp Σ xprog).
  Local Notation present := (present Σ xprog).
  Local Notation fresh := (fresh K_eq_dec Σ xprog).
  Local Notation target := (target Σ prog').
  Local Notation target_is := (target_is K_eq_dec Σ prog').
  Local Notation WF := (WF K_eq_dec Σ prog').
  Local Notation xdeps c := (xdeps Σ (xprog c)).
  Local Notation xopt c := (xopt Σ (xprog c)).
  Local Notation xprovs c := (xprovs Σ (xprog c)).

  (** ** Hypotheses *)
  Variable Kb : nat.
  Hypothesis xHK : forall c T, Bounded Σ Kb (xbody Σ (xprog c) T).
  Variable xrank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', XAbove Σ xprog c c' -> xrank c < xrank c'.
  Hypothesis Hbnd : forall c, xrank c <= Rb.

  Local Notation frank f := (xrank (fst (fcomp f))).
  Local Notation rank' := (fun x : CC => xrank (fst x)).
  Local Notation progG := (progG K_eq_dec Σ C_eq_dec xprog).
  Local Notation Bm := (Bm Kb).
  Local Notation muU := (muU Σ Kb).
  Local Notation dflag := (dflag Σ).
  Local Notation Wt := (Wt Σ).
  Local Notation childflag := (childflag Σ).

  (** ** The invariant *)
  Definition XTInv (γ : State) : Prop :=
    XInv K_eq_dec Σ xprog γ /\ LoadBound Σ Kb γ /\ SpawnOwn Σ γ.

  Lemma xtinv_init : XTInv (@init K Σ CC).
  Proof.
    split; [exact (xinv_init K_eq_dec Σ xprog)|]; split; [intros n f P acc w H; discriminate|].
    intros x f m fm H; discriminate.
  Qed.

  Lemma HrG (γ : State) : XSpawnProv Σ xprog γ ->
    forall x y, Above Σ (progG γ) x y -> rank' x < rank' y.
  Proof. intros XP x y HA; exact (above_G K_eq_dec Σ C_eq_dec xprog xrank Hrank γ x y XP HA). Qed.

  Lemma tg (γ : State) : XTInv γ -> TInv K_eq_dec Σ (progG γ) Kb γ.
  Proof.
    intros [[W P U X] [LB SO]].
    exact (Build_TInv _ _ _ _ _ (wf_G K_eq_dec Σ C_eq_dec xprog γ γ W)
             (prov_G K_eq_dec Σ C_eq_dec xprog γ γ P) (inv2_G K_eq_dec Σ C_eq_dec xprog γ W U) LB SO).
  Qed.

  Lemma bounded_lift_t j (P : @Prog K Σ C) : Bounded Σ j P -> Bounded Σ j (lift Σ P).
  Proof. intros H; induction H; cbn; constructor; auto. Qed.

  Lemma HKG (γ : State) : forall c, Bounded Σ Kb (body Σ (progG γ c)).
  Proof.
    intros x; unfold OptProgress.progG, Optional.prog'; cbn [body].
    apply bounded_lift_t, xHK.
  Qed.

  (** ** What a step of [n] may do *)
  Definition XEffects (γ γ' : State) n (fn : Fiber) : Prop :=
    (forall x fx, x <> n -> fibers γ x = Some fx ->
       fibers γ' x = Some fx \/
       (fibers γ' x = Some (mkFiber Σ (fcomp fx) (fparent fx) true (life fx)) /\
        In (USpawn Σ x) (acc_of (life fn)))) /\
    (forall x fx', fibers γ x = None -> fibers γ' x = Some fx' -> x = next γ /\ frank fn < frank fx') /\
    (forall fn', fibers γ' n = Some fn' -> fcomp fn' = fcomp fn /\ disposed fn' = disposed fn) /\
    (fibers γ' n = None -> disposed fn = true) /\
    BindsOK K_eq_dec Σ prog' γ γ' fn.

  Lemma step_G_lc (γ0 γ γ' : State) ℓ : step γ ℓ = Some γ' ->
    Calculus.step K_eq_dec Σ (progG γ0) γ ℓ = Some γ'.
  Proof. exact (step_G_any K_eq_dec Σ C_eq_dec xprog γ0 γ γ' ℓ). Qed.

  Lemma xeffects_core (γ γ' : State) n ℓ fn :
    XTInv γ -> In ℓ (@lifecycle_labels CC n) -> step γ ℓ = Some γ' -> fibers γ n = Some fn ->
    XEffects γ γ' n fn.
  Proof.
    intros X Hin H Hn.
    pose proof (proj1 X) as [_ _ _ XP].
    destruct (lstep_effects K_eq_dec Σ (progG γ) Kb rank' (HrG γ XP) γ γ' n ℓ fn (tg γ X) Hin
                (step_G_lc γ γ γ' ℓ H) Hn) as (E1 & E2 & E3 & E5 & EB).
    split; [exact E1|]; split; [|split; [exact E3 | split; [exact E5 | exact EB]]].
    intros x fx' Hx Hx'; destruct (E2 x fx' Hx Hx') as [Ex Hs]; split; [exact Ex|].
    exact (HrG γ XP _ _ (or_intror (or_introl Hs))).
  Qed.

  Lemma xeffects_relife (γ : State) n fn (l : Life) :
    fibers γ n = Some fn -> XEffects γ (set_life Σ γ n fn l) n fn.
  Proof.
    intros Hn; split; [|split; [|split; [|split]]].
    - intros x fx Hxn Hx; left; rewrite fibers_set_life.
      destruct (Nat.eqb_spec x n); [contradiction | exact Hx].
    - intros x fx' Hx Hx'; rewrite fibers_set_life in Hx'.
      destruct (Nat.eqb_spec x n) as [->|_]; congruence.
    - intros fn' H; rewrite fibers_set_life, Nat.eqb_refl in H; injection H as <-; auto.
    - rewrite fibers_set_life, Nat.eqb_refl; discriminate.
    - intros k; left; reflexivity.
  Qed.

  (** ** Ranks *)
  Lemma child_rank_x (γ : State) n fn x fx :
    XTInv γ -> fibers γ n = Some fn -> In (USpawn Σ x) (acc_of (life fn)) ->
    fibers γ x = Some fx -> frank fn < frank fx.
  Proof.
    intros [[_ _ _ XP] _] Hn Hin Hx; apply Hrank; right; exact (XP n fn x fx Hn Hin Hx).
  Qed.

  Lemma lower_same_x (γ γ' : State) n fn x fx :
    XTInv γ -> XEffects γ γ' n fn -> fibers γ n = Some fn ->
    x <> n -> fibers γ x = Some fx -> frank fx <= frank fn -> fibers γ' x = Some fx.
  Proof.
    intros I [E1 _] Hn Hxn Hx Hr.
    destruct (E1 x fx Hxn Hx) as [H|[_ Hin]]; [exact H|].
    pose proof (child_rank_x γ n fn x fx I Hn Hin Hx); lia.
  Qed.

  (** Keys a component reads: its required and optional dependencies. *)
  Definition KeyOf (c : C) (k : K) : Prop := In k (xdeps c) \/ In k (xopt c).

  Lemma prov_rank_x (fo : Fiber) c k :
    kmem K_eq_dec k (fprovs Σ prog' fo) = true -> KeyOf c k -> frank fo < xrank c.
  Proof.
    intros Hk Hc; apply Hrank; left; exists k; split; [|exact Hc].
    exact (kmem_In K_eq_dec k _ Hk).
  Qed.

  Lemma vis_stable (γ γ' : State) n fn c k :
    XTInv γ -> XEffects γ γ' n fn -> fibers γ n = Some fn ->
    KeyOf c k -> xrank c <= frank fn -> visible Σ γ' k = visible Σ γ k.
  Proof.
    intros I EF Hn Hk Hr.
    pose proof EF as (_ & _ & _ & _ & EB).
    pose proof (xi_wf _ _ _ _ (proj1 I)) as W.
    assert (Owner : forall b, binds γ k = Some b -> fibers γ' (owner b) = fibers γ (owner b)).
    { intros b Hb.
      destruct (wf_bind K_eq_dec Σ prog' γ W k b Hb) as (fo & Ho & _ & Hko & _).
      pose proof (prov_rank_x fo c k Hko Hk) as Hlt.
      assert (Hon : owner b <> n).
      { intros Heq; rewrite Heq, Hn in Ho; injection Ho as <-; lia. }
      rewrite Ho; exact (lower_same_x γ γ' n fn (owner b) fo I EF Hn Hon Ho ltac:(lia)). }
    destruct (EB k) as [Eq|[(b & b' & Hb & Hb' & Hp & Ho)|Hkm]].
    - unfold visible; rewrite Eq.
      destruct (binds γ k) as [b|] eqn:Hb; [|reflexivity].
      rewrite (Owner b eq_refl); reflexivity.
    - unfold visible; rewrite Hb, Hb', Ho, Hp, (Owner b Hb); reflexivity.
    - pose proof (prov_rank_x fn c k Hkm Hk); lia.
  Qed.

  Lemma present_stable (γ γ' : State) n fn c :
    XTInv γ -> XEffects γ γ' n fn -> fibers γ n = Some fn -> xrank c <= frank fn ->
    present γ' c = present γ c.
  Proof.
    intros I EF Hn Hr; unfold Optional.present; apply filter_ext_in; intros k Hk.
    unfold is_visible; rewrite (vis_stable γ γ' n fn c k I EF Hn (or_intror Hk) Hr); reflexivity.
  Qed.


  Lemma resolve_stable_x (γ γ' : State) n fn c ks :
    XTInv γ -> XEffects γ γ' n fn -> fibers γ n = Some fn -> xrank c <= frank fn ->
    (forall k, In k ks -> KeyOf c k) -> resolve Σ γ' ks = resolve Σ γ ks.
  Proof.
    intros I EF Hn Hr; induction ks as [|k ks IH]; intros Hks; cbn; [reflexivity|].
    rewrite (vis_stable γ γ' n fn c k I EF Hn (Hks k (or_introl eq_refl)) Hr).
    rewrite IH; [reflexivity|]; intros k' Hk'; apply Hks; right; exact Hk'.
  Qed.

  Lemma deps_keyof (x : CC) k : In k (deps Σ (prog' x)) -> KeyOf (fst x) k.
  Proof.
    unfold Optional.prog'; cbn [deps]; intros H; apply in_app_or in H as [H|H]; [left; exact H|].
    right; apply filter_In in H as [_ H].
    unfold kmem, keqb in H; apply existsb_exists in H as (k' & Hk' & E).
    destruct (K_eq_dec k k') as [->|]; [exact Hk' | discriminate].
  Qed.

  (** What re-choosing presence would give as a target. *)
  Definition bt (γ : State) (n : nat) : option (@View K) :=
    match fibers γ n with
    | Some f => if disposed f then None
                else resolve Σ γ (deps Σ (prog' (fst (fcomp f), present γ (fst (fcomp f)))))
    | None => None
    end.

  Lemma bt_recomp (γ : State) n f :
    fibers γ n = Some f -> target (recomp γ n f) n = bt γ n.
  Proof.
    intros Hn; unfold Calculus.target, bt; rewrite fibers_recomp, Nat.eqb_refl, Hn; cbn.
    destruct (disposed f); [reflexivity|].
    apply resolve_ext; intros k; exact (visible_recomp Σ xprog γ n f k Hn).
  Qed.

  (** Stability for a fiber of rank at most that of [n]. *)
  Lemma stable_fiber (γ γ' : State) n fn m fm fm' :
    XTInv γ -> XEffects γ γ' n fn -> fibers γ n = Some fn ->
    fibers γ m = Some fm -> fibers γ' m = Some fm' ->
    fcomp fm' = fcomp fm -> disposed fm' = disposed fm -> frank fm <= frank fn ->
    target γ' m = target γ m /\ bt γ' m = bt γ m /\ fresh γ' fm' = fresh γ fm.
  Proof.
    intros I EF Hn Hm Hm' Hc Hd Hr.
    pose proof (present_stable γ γ' n fn (fst (fcomp fm)) I EF Hn Hr) as Ep.
    split; [|split].
    - unfold Calculus.target; rewrite Hm, Hm', Hd, Hc.
      destruct (disposed fm); [reflexivity|].
      apply (resolve_stable_x γ γ' n fn (fst (fcomp fm))); auto; apply deps_keyof.
    - unfold bt; rewrite Hm, Hm', Hd, Hc, Ep.
      destruct (disposed fm); [reflexivity|].
      apply (resolve_stable_x γ γ' n fn (fst (fcomp fm))); auto; intros k Hk; exact (deps_keyof _ k Hk).
    - unfold Optional.fresh; rewrite Hc, Ep; reflexivity.
  Qed.

  (** ** The measure *)
  Definition xtis (γ : State) (n : nat) (f : Fiber) (w : @View K) : bool :=
    fresh γ f && target_is γ n w.

  Definition xmu (γ : State) (n : nat) (f : Fiber) : nat :=
    match life f with
    | Inactive _ (Some _) => dflag f
    | Inactive _ None => match bt γ n with Some _ => Bm | None => dflag f end
    | Loading _ _ acc w =>
        if xtis γ n f w then 3 * Kb + 10 - length acc
        else muU γ f acc None (bt γ n) + 1
    | Active _ acc w =>
        if xtis γ n f w then 0
        else muU γ f acc None (bt γ n) + 1
    | Unloading _ acc _ z => muU γ f acc z (bt γ n)
    end.

  Lemma own_item_ne_x (γ : State) n fn x :
    XTInv γ -> fibers γ n = Some fn -> In (USpawn Σ x) (acc_of (life fn)) -> x <> n.
  Proof. intros I Hn Hin ->; pose proof (child_rank_x γ n fn n fn I Hn Hin Hn); lia. Qed.

  (** ** The measure of the other fibers of rank at most that of [n] *)
  Lemma mu_other_x (γ γ' : State) n fn m fm :
    XTInv γ -> XEffects γ γ' n fn -> fibers γ n = Some fn ->
    m <> n -> fibers γ m = Some fm -> frank fm <= frank fn ->
    fibers γ' m = Some fm /\ xmu γ' m fm = xmu γ m fm.
  Proof.
    intros I EF Hn Hmn Hm Hr.
    pose proof (lower_same_x γ γ' n fn m fm I EF Hn Hmn Hm Hr) as Hm'.
    split; [exact Hm'|].
    destruct (stable_fiber γ γ' n fn m fm fm I EF Hn Hm Hm' eq_refl eq_refl Hr) as (Ht & Hb & Hf).
    assert (Hfl : forall x, In (USpawn Σ x) (acc_of (life fm)) -> childflag γ' x = childflag γ x).
    { intros x Hx; destruct EF as (E1 & E2 & E3 & E5 & _).
      pose proof (proj2 (proj2 I)) as SO.
      unfold Termination.childflag.
      destruct (fibers γ x) as [fx|] eqn:Hfx.
      - destruct (Nat.eq_dec x n) as [->|Hxn].
        + rewrite Hn in Hfx; injection Hfx as <-.
          destruct (fibers γ' n) as [fn'|] eqn:Hn'.
          * destruct (E3 fn' eq_refl) as [_ ->]; reflexivity.
          * rewrite (E5 eq_refl); reflexivity.
        + destruct (E1 x fx Hxn Hfx) as [->|[_ Hinn]]; [reflexivity|].
          exfalso.
          pose proof (SO m fm x fx Hm Hx Hfx) as P1.
          pose proof (SO n fn x fx Hn Hinn Hfx) as P2.
          congruence.
      - destruct (fibers γ' x) as [fx'|] eqn:Hfx'; [|reflexivity].
        destruct (E2 x fx' Hfx Hfx') as [Hxe _].
        pose proof (wf_spawn_lt K_eq_dec Σ prog' γ (xi_wf _ _ _ _ (proj1 I)) m fm x Hm Hx); lia. }
    unfold xmu, xtis.
    destruct (life fm) as [[e|]|P acc w|acc w|acc w z] eqn:Hl.
    - reflexivity.
    - rewrite Hb; reflexivity.
    - rewrite Hf; unfold target_is; rewrite Ht, Hb; unfold Termination.muU.
      rewrite (Wt_ext Σ γ γ' acc); [reflexivity|].
      intros x Hx; apply Hfl; exact Hx.
    - rewrite Hf; unfold target_is; rewrite Ht, Hb; unfold Termination.muU.
      rewrite (Wt_ext Σ γ γ' acc); [reflexivity|].
      intros x Hx; apply Hfl; exact Hx.
    - rewrite Hb; unfold Termination.muU.
      rewrite (Wt_ext Σ γ γ' acc); [reflexivity|].
      intros x Hx; apply Hfl; exact Hx.
  Qed.

  Lemma bt_fresh (γ : State) n f : fibers γ n = Some f -> fresh γ f = true -> bt γ n = target γ n.
  Proof.
    intros Hn Hf; unfold bt, Calculus.target; rewrite Hn.
    unfold Optional.fresh in Hf.
    destruct (list_eq_dec K_eq_dec (present γ (fst (fcomp f))) (snd (fcomp f))) as [E|]; [|discriminate].
    rewrite E, <- surjective_pairing; reflexivity.
  Qed.

  Lemma xtis_false (γ : State) n f w : target_is γ n w = false -> xtis γ n f w = false.
  Proof. intros H; unfold xtis; rewrite H, andb_false_r; reflexivity. Qed.

  (** ** The measure of [n] drops at a core lifecycle step of [n] *)
  Lemma mu_drop_core (γ γ' : State) n ℓ fn :
    XTInv γ -> In ℓ (@lifecycle_labels CC n) -> step γ ℓ = Some γ' -> fibers γ n = Some fn ->
    ((ℓ = LBegin n \/ ℓ = LStep n) -> fresh γ fn = true) ->
    match fibers γ' n with Some fn' => xmu γ' n fn' | None => 0 end < xmu γ n fn.
  Proof.
    intros I Hin H Hn Hfr.
    pose proof (xeffects_core γ γ' n ℓ fn I Hin H Hn) as EF.
    pose proof EF as (_ & _ & E3 & _ & _).
    assert (Hst : forall fn', fibers γ' n = Some fn' ->
              target γ' n = target γ n /\ bt γ' n = bt γ n /\ fresh γ' fn' = fresh γ fn).
    { intros fn' Hn'; destruct (E3 fn' Hn') as [Hc Hd].
      exact (stable_fiber γ γ' n fn n fn fn' I EF Hn Hn Hn' Hc Hd (le_n _)). }
    assert (Hrl : forall γ1 (l : Life), fibers (set_life Σ γ1 n fn l) n =
                    Some (mkFiber Σ (fcomp fn) (fparent fn) (disposed fn) l))
      by (intros; rewrite fibers_set_life, Nat.eqb_refl; reflexivity).
    pose proof (proj1 (proj2 I)) as LB.
    cbn in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
      pose proof H as H0; cbn [Calculus.step] in H; rewrite Hn in H.
    - (* LBegin *)
      pose proof (Hfr (or_introl eq_refl)) as F.
      destruct (life fn) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (target γ n) as [w|] eqn:Htg; [|discriminate]; injection H as <-.
      rewrite Hrl; destruct (Hst _ (Hrl _ _)) as (Ht & _ & Hf).
      unfold xmu, xtis; cbn [life]; rewrite Hl, (bt_fresh γ n fn Hn F), Htg, Hf, F.
      rewrite (proj2 (target_is_spec K_eq_dec Σ prog' _ n w) ltac:(rewrite Ht; first [exact Htg | reflexivity])); cbn; lia.
    - (* LStep *)
      pose proof (Hfr (or_intror eq_refl)) as F.
      destruct (life fn) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is γ n w) eqn:Hti; [|discriminate]; injection H as <-.
      destruct (LB n fn P acc w Hn Hl) as [Hlen _].
      assert (Hmu : xmu γ n fn = 3 * Kb + 10 - length acc)
        by (unfold xmu, xtis; rewrite Hl, F, Hti; reflexivity).
      rewrite Hmu.
      assert (Goal : forall γ1 (l : Life),
                (target (set_life Σ γ1 n fn l) n = target γ n /\
                 bt (set_life Σ γ1 n fn l) n = bt γ n /\
                 fresh (set_life Σ γ1 n fn l) (mkFiber Σ (fcomp fn) (fparent fn) (disposed fn) l) = fresh γ fn) ->
                (match l with
                 | Active _ acc' w' => acc' = acc /\ w' = w
                 | Unloading _ acc' _ (Some _) => acc' = acc
                 | Loading _ _ acc' w' => length acc' = S (length acc) /\ w' = w
                 | _ => False
                 end) ->
                xmu (set_life Σ γ1 n fn l) n (mkFiber Σ (fcomp fn) (fparent fn) (disposed fn) l)
                < 3 * Kb + 10 - length acc).
      { intros γ1 l (Ht' & _ & Hf') Hshape.
        unfold xmu, xtis; cbn [life].
        destruct l as [z'|P' acc' w'|acc' w'|acc' w' [e|]]; try contradiction.
        - destruct Hshape as [Hla ->].
          rewrite Hf', F; unfold target_is; rewrite Ht'; fold (target_is γ n w); rewrite Hti; cbn; lia.
        - destruct Hshape as [-> ->].
          rewrite Hf', F; unfold target_is; rewrite Ht'; fold (target_is γ n w); rewrite Hti; cbn; lia.
        - subst acc'; unfold Termination.muU, Termination.dflag; cbn.
          pose proof (Wt_le Σ (set_life Σ γ1 n fn (Unloading Σ acc w' (Some e))) acc).
          destruct (disposed fn); lia. }
      Ltac finx Goal Hst Hrl :=
        rewrite Hrl; apply Goal; [apply Hst; apply Hrl | cbn; auto].
      destruct P as [| |k a κ|k s P'|c P'].
      + cbn [load_step] in Hst |- *; finx Goal Hst Hrl.
      + cbn [load_step] in Hst |- *; finx Goal Hst Hrl.
      + rewrite (load_step_op K_eq_dec Σ prog' γ n fn k a κ acc w) in Hst |- *.
        destruct (op_binding K_eq_dec Σ prog' γ n fn k w) as [b|]; [|finx Goal Hst Hrl].
        destruct (run a (next γ) (bst Σ b)) as [[[s' g] o]|]; finx Goal Hst Hrl.
      + cbn [load_step] in Hst |- *.
        destruct (kmem K_eq_dec k (provs Σ (prog' (fcomp fn)))); [|finx Goal Hst Hrl].
        destruct (binds γ k); finx Goal Hst Hrl.
      + cbn [load_step] in Hst |- *.
        destruct (conflict K_eq_dec Σ prog' γ c); finx Goal Hst Hrl.
    - (* LDivert *)
      destruct (life fn) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is γ n w) eqn:Hti; [discriminate|]; injection H as <-.
      rewrite Hrl; destruct (Hst _ (Hrl _ _)) as (_ & Hb & _).
      unfold xmu; cbn [life]; rewrite Hl, (xtis_false γ n fn w Hti), Hb.
      unfold Termination.muU; rewrite (Wt_ext Σ γ _ acc); [unfold Termination.dflag; cbn; lia|].
      intros x Hx; apply childflag_relife; [reflexivity|].
      apply (own_item_ne_x γ n fn x I Hn); rewrite Hl; exact Hx.
    - (* LLeave *)
      destruct (life fn) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (target_is γ n w) eqn:Hti; [discriminate|]; injection H as <-.
      rewrite Hrl; destruct (Hst _ (Hrl _ _)) as (_ & Hb & _).
      unfold xmu; cbn [life]; rewrite Hl, (xtis_false γ n fn w Hti), Hb.
      unfold Termination.muU; rewrite (Wt_ext Σ γ _ acc); [unfold Termination.dflag; cbn; lia|].
      intros x Hx; apply childflag_relife; [reflexivity|].
      apply (own_item_ne_x γ n fn x I Hn); rewrite Hl; exact Hx.
    - (* LUndo *)
      destruct (life fn) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      destruct (undo_step_shape K_eq_dec Σ γ γ' n fn u acc w z H) as (γ1 & -> & E).
      rewrite Hrl; destruct (Hst _ (Hrl _ _)) as (_ & Hb & _).
      unfold xmu; cbn [life]; rewrite Hl, Hb.
      unfold Termination.muU; cbn [Termination.Wt].
      rewrite (Wt_ext Σ γ _ acc); [unfold Termination.dflag; cbn; destruct u; cbn; lia|].
      intros x Hx; apply childflag_relife; [exact E|].
      apply (own_item_ne_x γ n fn x I Hn); rewrite Hl; right; exact Hx.
    - (* LRetireChild *)
      destruct (life fn) as [| | |[|[k p t g|k p|mm] acc] w z] eqn:Hl; try discriminate.
      destruct (fibers γ mm) as [g|] eqn:Hg; [|discriminate].
      unheld H; destruct (disposed g) eqn:Hdg; [discriminate|]; injection H as <-.
      assert (Hmn : mm <> n)
        by (apply (own_item_ne_x γ n fn mm I Hn); rewrite Hl; left; reflexivity).
      assert (Hn' : fibers (set_fiber Σ γ mm (mkFiber Σ (fcomp g) (fparent g) true (life g))) n
                    = Some fn).
      { cbn; unfold fupd; destruct (Nat.eqb_spec n mm); [congruence | exact Hn]. }
      rewrite Hn'; destruct (Hst _ Hn') as (_ & Hb & _).
      unfold xmu; rewrite Hl, Hb.
      unfold Termination.muU; cbn [Termination.Wt Termination.wt].
      assert (Hf : childflag (set_fiber Σ γ mm (mkFiber Σ (fcomp g) (fparent g) true (life g))) mm = 0)
        by (unfold Termination.childflag; cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity).
      assert (Hf0 : childflag γ mm = 1) by (unfold Termination.childflag; rewrite Hg, Hdg; reflexivity).
      assert (Hm : Wt (set_fiber Σ γ mm (mkFiber Σ (fcomp g) (fparent g) true (life g))) acc
                   <= Wt γ acc).
      { apply Wt_mono; intros x _; unfold Termination.childflag; cbn; unfold fupd.
        destruct (Nat.eqb_spec x mm) as [->|_]; [rewrite Hg, Hdg; cbn; lia | apply Nat.le_refl]. }
      rewrite Hf, Hf0; lia.
    - (* LUnloaded *)
      destruct (life fn) as [| | |[|u acc] w z] eqn:Hl; try discriminate; injection H as <-.
      rewrite Hrl; destruct (Hst _ (Hrl _ _)) as (_ & Hb & _).
      unfold xmu; cbn [life]; rewrite Hl, Hb.
      unfold Termination.muU; cbn [Termination.Wt].
      destruct z as [e|]; cbn; [unfold Termination.dflag; cbn; lia|].
      destruct (bt γ n); unfold Termination.dflag; cbn; lia.
    - (* LRemove *)
      destruct (life fn) as [z| | |] eqn:Hl; try discriminate.
      destruct (disposed fn) eqn:Hd; [|discriminate]; cbn in H.
      destruct (negb (has_child Σ γ n)); [|discriminate]; injection H as <-.
      cbn; unfold fupd; rewrite Nat.eqb_refl.
      unfold xmu; rewrite Hl; unfold Termination.dflag; rewrite Hd.
      destruct z; [lia|].
      assert (Hbn : bt γ n = None) by (unfold bt; rewrite Hn, Hd; reflexivity).
      rewrite Hbn; lia.
  Qed.

  (** The measure of [n] drops when it reloads because its presence changed. *)
  Lemma mu_drop_restart (γ : State) n fn acc w (l : Life) :
    XTInv γ -> fibers γ n = Some fn -> fresh γ fn = false ->
    (exists P, life fn = Loading Σ P acc w \/ life fn = Active Σ acc w) ->
    l = Unloading Σ acc w None ->
    xmu (set_life Σ γ n fn l) n (mkFiber Σ (fcomp fn) (fparent fn) (disposed fn) l) < xmu γ n fn.
  Proof.
    intros I Hn F (P & Hl) ->.
    pose proof (xeffects_relife γ n fn (Unloading Σ acc w None) Hn) as EF.
    assert (Hn' : fibers (set_life Σ γ n fn (Unloading Σ acc w None)) n =
                  Some (mkFiber Σ (fcomp fn) (fparent fn) (disposed fn) (Unloading Σ acc w None)))
      by (rewrite fibers_set_life, Nat.eqb_refl; reflexivity).
    destruct (stable_fiber γ _ n fn n fn _ I EF Hn Hn Hn' eq_refl eq_refl (le_n _)) as (_ & Hb & _).
    assert (Hw : Wt (set_life Σ γ n fn (Unloading Σ acc w None)) acc = Wt γ acc).
    { apply Wt_ext; intros x Hx; apply childflag_relife; [reflexivity|].
      apply (own_item_ne_x γ n fn x I Hn); destruct Hl as [Hl|Hl]; rewrite Hl; exact Hx. }
    unfold xmu at 1; cbn [life]; rewrite Hb.
    unfold xmu, xtis; rewrite F; cbn [andb].
    destruct Hl as [Hl|Hl]; rewrite Hl; unfold Termination.muU; rewrite Hw; unfold Termination.dflag; cbn [Calculus.disposed]; destruct (bt γ n); lia.
  Qed.

  (** ** The measure of a state *)
  Definition xcontrib (γ : State) (r m : nat) : nat :=
    match fibers γ m with
    | Some f => if Nat.eqb (frank f) r then xmu γ m f else 0
    | None => 0
    end.

  Definition XPhi (γ : State) (r : nat) : nat := sumf (xcontrib γ r) (names Σ γ).

  Lemma XPhi_ext (γ : State) r M :
    WF γ -> next γ <= M -> XPhi γ r = sumf (xcontrib γ r) (seq 0 M).
  Proof.
    intros W HM; unfold XPhi, names.
    replace M with (next γ + (M - next γ)) by lia.
    rewrite seq_app, sumf_app.
    rewrite (sumf_zero _ (seq (0 + next γ) _)); [lia|].
    intros x Hx; apply in_seq in Hx; unfold xcontrib.
    destruct (fibers γ x) eqn:E; [|reflexivity].
    apply (wf_names K_eq_dec Σ prog' γ W) in E; lia.
  Qed.

  Theorem phi_drop_gen (γ γ' : State) n fn :
    XTInv γ -> WF γ' -> XEffects γ γ' n fn -> fibers γ n = Some fn ->
    match fibers γ' n with Some fn' => xmu γ' n fn' | None => 0 end < xmu γ n fn ->
    lexR Rb (XPhi γ') (XPhi γ).
  Proof.
    intros I W' EF Hn Hd.
    pose proof EF as (E1 & E2 & E3 & E5 & _).
    set (r0 := frank fn).
    assert (P1 : forall r, r <= r0 -> forall m,
              xcontrib γ' r m <= xcontrib γ r m /\
              (m <> n \/ r < r0 -> xcontrib γ' r m = xcontrib γ r m)).
    { intros r Hr m; unfold xcontrib.
      destruct (Nat.eq_dec m n) as [->|Hmn].
      - rewrite Hn.
        destruct (fibers γ' n) as [fn'|] eqn:Hn'.
        + destruct (E3 fn' eq_refl) as [Hc _]; rewrite Hc.
          destruct (Nat.eqb_spec (frank fn) r) as [Er|Er].
          * split; [lia|]; intros [Cx|Cx]; [contradiction | subst r0; lia].
          * split; [lia | intros; reflexivity].
        + destruct (Nat.eqb_spec (frank fn) r) as [Er|Er].
          * split; [lia|]; intros [Cx|Cx]; [contradiction | subst r0; lia].
          * split; [lia | intros; reflexivity].
      - destruct (fibers γ m) as [fm|] eqn:Hm.
        + destruct (Compare_dec.le_lt_dec (frank fm) r0) as [Hle|Hgt].
          * destruct (mu_other_x γ γ' n fn m fm I EF Hn Hmn Hm Hle) as [Hm' Hmu].
            rewrite Hm', Hmu; split; [lia | auto].
          * destruct (E1 m fm Hmn Hm) as [Hm'|[Hm' _]]; rewrite Hm'; cbn [Calculus.comp];
              (destruct (Nat.eqb_spec (frank fm) r); [subst r0; lia | split; [lia | auto]]).
        + destruct (fibers γ' m) as [fm'|] eqn:Hm'; [|split; [lia | auto]].
          destruct (E2 m fm' Hm Hm') as [_ Hlt].
          destruct (Nat.eqb_spec (frank fm') r); [subst r0; lia | split; [lia | auto]]. }
    assert (P2 : xcontrib γ' r0 n < xcontrib γ r0 n).
    { unfold xcontrib; rewrite Hn; subst r0; rewrite Nat.eqb_refl.
      destruct (fibers γ' n) as [fn'|] eqn:Hn'; [|exact Hd].
      destruct (E3 fn' eq_refl) as [Hc _]; rewrite Hc, Nat.eqb_refl; exact Hd. }
    set (M := next γ + next γ').
    pose proof (xi_wf _ _ _ _ (proj1 I)) as W.
    exists r0; split; [apply Hbnd|]; split.
    - intros i Hi.
      rewrite (XPhi_ext γ' i M W') by lia; rewrite (XPhi_ext γ i M W) by lia.
      apply sumf_eq; intros m _; apply (proj2 (P1 i ltac:(lia) m)); right; exact Hi.
    - rewrite (XPhi_ext γ' r0 M W') by lia; rewrite (XPhi_ext γ r0 M W) by lia.
      apply (sumf_lt _ _ _ n); [intros m _; exact (proj1 (P1 r0 (le_n _) m)) | | exact P2].
      apply in_seq; pose proof (wf_names K_eq_dec Σ prog' γ W n fn Hn); lia.
  Qed.

  (** ** The invariant along extended steps *)
  Lemma xtinv_recomp (γ : State) n f :
    XTInv γ -> fibers γ n = Some f -> is_installed Σ (life f) = false -> XTInv (recomp γ n f).
  Proof.
    intros [XI [LB SO]] Hn Hi; split; [exact (xinv_recomp K_eq_dec Σ xprog γ n f XI Hn Hi)|].
    assert (Hb : forall m fm, fibers (recomp γ n f) m = Some fm ->
                 exists fm0, fibers γ m = Some fm0 /\ life fm = life fm0 /\ fparent fm = fparent fm0).
    { intros m fm H; rewrite fibers_recomp in H.
      destruct (Nat.eqb_spec m n) as [->|]; [injection H as <-; exists f; auto | exists fm; auto]. }
    split.
    - intros m fm P acc w H Hl; destruct (Hb m fm H) as (fm0 & H0 & El & _).
      rewrite El in Hl; exact (LB m fm0 P acc w H0 Hl).
    - intros x fx m fm Hx Hu Hm.
      destruct (Hb x fx Hx) as (fx0 & Hx0 & Elx & _), (Hb m fm Hm) as (fm0 & Hm0 & _ & Ep).
      rewrite Elx in Hu; rewrite Ep; exact (SO x fx0 m fm0 Hx0 Hu Hm0).
  Qed.

  Lemma xtinv_core (γ γ' : State) ℓ : XTInv γ -> step γ ℓ = Some γ' -> LoadBound Σ Kb γ' /\ SpawnOwn Σ γ'.
  Proof.
    intros X H.
    pose proof (tinv_step K_eq_dec Σ (progG γ) Kb (HKG γ) γ γ' ℓ (tg γ X) (step_G_lc γ γ γ' ℓ H)) as T.
    split; [exact (t_lb _ _ _ _ _ T) | exact (t_so _ _ _ _ _ T)].
  Qed.

  Theorem xtinv_step (γ γ' : State) ℓ : XTInv γ -> xstep γ ℓ = Some γ' -> XTInv γ'.
  Proof.
    intros X H; split; [exact (xinv_step K_eq_dec Σ C_eq_dec xprog γ γ' ℓ (proj1 X) H)|].
    destruct (xstep_core K_eq_dec Σ xprog γ γ' ℓ H) as [St|[(m & f & _ & Hm & Hl & St)|(m & St)]].
    - exact (xtinv_core γ γ' _ X St).
    - assert (Hi : is_installed Σ (life f) = false) by (rewrite Hl; reflexivity).
      exact (xtinv_core _ γ' _ (xtinv_recomp γ m f X Hm Hi) St).
    - exact (xtinv_core γ γ' _ X St).
  Qed.

  (** ** Re-choosing an Inactive fiber's presence leaves the measure *)
  Lemma xphi_recomp (γ : State) n f :
    XTInv γ -> fibers γ n = Some f -> life f = Inactive Σ None ->
    forall r, XPhi (recomp γ n f) r = XPhi γ r.
  Proof.
    intros I Hn Hl r.
    assert (Hv : forall k, visible Σ (recomp γ n f) k = visible Σ γ k)
      by (intros k; exact (visible_recomp Σ xprog γ n f k Hn)).
    assert (Hp : forall c, present (recomp γ n f) c = present γ c)
      by (intros c; unfold Optional.present; apply filter_ext; intros k; unfold is_visible; rewrite Hv; reflexivity).
    assert (Hr : forall ks, resolve Σ (recomp γ n f) ks = resolve Σ γ ks)
      by (intros ks; apply resolve_ext; exact Hv).
    assert (Hcf : forall x, childflag (recomp γ n f) x = childflag γ x).
    { intros x; unfold Termination.childflag; rewrite fibers_recomp.
      destruct (Nat.eqb_spec x n) as [->|]; [rewrite Hn; reflexivity | reflexivity]. }
    assert (Hwt : forall l, Wt (recomp γ n f) l = Wt γ l)
      by (intros l; apply Wt_ext; intros x _; apply Hcf).
    unfold XPhi; change (names Σ (recomp γ n f)) with (names Σ γ).
    apply sumf_eq; intros m _; unfold xcontrib; rewrite fibers_recomp.
    destruct (Nat.eqb_spec m n) as [->|Hmn].
    - rewrite Hn; cbn [Calculus.comp fst].
      destruct (Nat.eqb (frank f) r); [|reflexivity].
      unfold xmu; cbn [life]; rewrite Hl.
      unfold bt; rewrite fibers_recomp, Nat.eqb_refl, Hn; cbn; rewrite Hp, Hr; reflexivity.
    - destruct (fibers γ m) as [fm|] eqn:Hm; [|reflexivity].
      destruct (Nat.eqb (frank fm) r); [|reflexivity].
      assert (Ebt : bt (recomp γ n f) m = bt γ m)
        by (unfold bt; rewrite fibers_recomp, (proj2 (Nat.eqb_neq m n) Hmn), Hm, Hp, Hr; reflexivity).
      assert (Etg : target (recomp γ n f) m = target γ m)
        by (unfold Calculus.target; rewrite fibers_recomp, (proj2 (Nat.eqb_neq m n) Hmn), Hm, Hr; reflexivity).
      assert (Efr : fresh (recomp γ n f) fm = fresh γ fm) by (unfold Optional.fresh; rewrite Hp; reflexivity).
      unfold xmu, xtis, target_is, Termination.muU; rewrite Ebt, Etg, Efr; destruct (life fm); rewrite ?Hwt; reflexivity.
  Qed.

  Lemma lexR_ext R (v1 v2 v : nat -> nat) : (forall r, v2 r = v r) -> lexR R v1 v2 -> lexR R v1 v.
  Proof.
    intros E (r & Hr & Heq & Hlt); exists r; split; [exact Hr|]; split.
    - intros i Hi; rewrite <- E; apply Heq; exact Hi.
    - rewrite <- E; exact Hlt.
  Qed.

  Lemma xlab_lc n (ℓ : @Calculus.Label C) :
    In ℓ (@lifecycle_labels C n) -> In (@xlab K C ℓ) (@lifecycle_labels CC n).
  Proof.
    cbn; intros Hin; destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn; tauto.
  Qed.

  (** ** Every extended lifecycle step decreases the measure *)
  Theorem xphi_drop (γ γ' : State) n ℓ :
    XTInv γ -> In ℓ (@lifecycle_labels C n) -> xstep γ ℓ = Some γ' -> lexR Rb (XPhi γ') (XPhi γ).
  Proof.
    intros I Hin H.
    pose proof (xi_wf _ _ _ _ (proj1 (xtinv_step γ γ' ℓ I H))) as W'.
    destruct (fibers γ n) as [fn|] eqn:Hn.
    2: { exfalso.
         assert (Hs : forall (ℓ0 : @Calculus.Label CC), In ℓ0 (@lifecycle_labels CC n) -> step γ ℓ0 = None)
           by (intros ℓ0 Hin0; exact (step_absent K_eq_dec Σ prog' γ n ℓ0 Hn Hin0)).
         cbn in Hin; destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]];
           cbn [Optional.xstep] in H; rewrite ?Hn in H; try discriminate H;
           cbn [xlab] in H; rewrite Hs in H by (cbn; tauto); discriminate H. }
    (* a core lifecycle step of [n] from [γ] *)
    assert (Core : forall ℓ', In ℓ' (@lifecycle_labels CC n) -> step γ ℓ' = Some γ' ->
              ((ℓ' = LBegin n \/ ℓ' = LStep n) -> fresh γ fn = true) ->
              lexR Rb (XPhi γ') (XPhi γ)).
    { intros ℓ' Hin' St Fr.
      exact (phi_drop_gen γ γ' n fn I W' (xeffects_core γ γ' n ℓ' fn I Hin' St Hn) Hn
               (mu_drop_core γ γ' n ℓ' fn I Hin' St Hn Fr)). }
    pose proof (xlab_lc n ℓ Hin) as Hin'.
    cbn in Hin; destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
    - (* X-Begin: re-choose presence, then the core L-Begin *)
      cbn [Optional.xstep] in H; rewrite Hn in H.
      destruct (life fn) as [[z|]| | |] eqn:Hl; try discriminate.
      set (γr := recomp γ n fn) in H.
      set (fr := mkFiber Σ (fst (fcomp fn), present γ (fst (fcomp fn))) (fparent fn) (disposed fn) (life fn)).
      assert (Hnr : fibers γr n = Some fr) by (unfold γr; rewrite fibers_recomp, Nat.eqb_refl; reflexivity).
      assert (Ir : XTInv γr) by (apply xtinv_recomp; auto; rewrite Hl; reflexivity).
      assert (Fr : fresh γr fr = true).
      { unfold Optional.fresh, fr; cbn [Calculus.comp fst snd].
        assert (Ep : present γr (fst (fcomp fn)) = present γ (fst (fcomp fn))).
        { unfold Optional.present; apply filter_ext; intros k; unfold is_visible.
          unfold γr; rewrite (visible_recomp Σ xprog γ n fn k Hn); reflexivity. }
        rewrite Ep; destruct (list_eq_dec K_eq_dec _ _) as [_|N]; [reflexivity | contradiction N; reflexivity]. }
      assert (Hin0 : In (@LBegin CC n) (@lifecycle_labels CC n)) by (cbn; tauto).
      pose proof (phi_drop_gen γr γ' n fr Ir W' (xeffects_core γr γ' n _ fr Ir Hin0 H Hnr) Hnr
                    (mu_drop_core γr γ' n _ fr Ir Hin0 H Hnr (fun _ => Fr))) as D.
      apply (lexR_ext Rb _ (XPhi γr)); [|exact D].
      intros r; unfold γr; exact (xphi_recomp γ n fn I Hn Hl r).
    - (* X-Step *)
      cbn [Optional.xstep] in H; rewrite Hn in H.
      destruct (fresh γ fn) eqn:F; [|discriminate].
      exact (Core _ Hin' H (fun _ => eq_refl)).
    - (* X-Divert *)
      cbn [Optional.xstep] in H; rewrite Hn in H.
      destruct (fresh γ fn) eqn:F; [exact (Core _ Hin' H (fun E => ltac:(destruct E; discriminate)))|].
      destruct (life fn) as [|P acc w| |] eqn:Hl; try discriminate; injection H as <-.
      apply (phi_drop_gen γ _ n fn I W' (xeffects_relife γ n fn _ Hn) Hn).
      rewrite fibers_set_life, Nat.eqb_refl.
      exact (mu_drop_restart γ n fn acc w _ I Hn F (ex_intro _ P (or_introl Hl)) eq_refl).
    - (* X-Leave *)
      cbn [Optional.xstep] in H; rewrite Hn in H.
      destruct (fresh γ fn) eqn:F; [exact (Core _ Hin' H (fun E => ltac:(destruct E; discriminate)))|].
      destruct (life fn) as [| |acc w|] eqn:Hl; try discriminate; injection H as <-.
      apply (phi_drop_gen γ _ n fn I W' (xeffects_relife γ n fn _ Hn) Hn).
      rewrite fibers_set_life, Nat.eqb_refl.
      exact (mu_drop_restart γ n fn acc w _ I Hn F (ex_intro _ PDone (or_intror Hl)) eq_refl).
    - exact (Core _ Hin' H (fun E => ltac:(destruct E; discriminate))).
    - exact (Core _ Hin' H (fun E => ltac:(destruct E; discriminate))).
    - exact (Core _ Hin' H (fun E => ltac:(destruct E; discriminate))).
    - exact (Core _ Hin' H (fun E => ltac:(destruct E; discriminate))).
  Qed.

  (** ** Termination *)
  Definition XLStepRel (γ' γ : State) : Prop :=
    XTInv γ /\ exists n ℓ, In ℓ (@lifecycle_labels C n) /\ xstep γ ℓ = Some γ'.

  (** Extended lifecycle steps alone always terminate. *)
  Theorem xtermination (γ : State) : XTInv γ -> Acc XLStepRel γ.
  Proof.
    assert (G : forall v, Acc (lexR Rb) v ->
                forall γ, XTInv γ -> (forall r, XPhi γ r = v r) -> Acc XLStepRel γ).
    { intros v Hacc; induction Hacc as [v _ IH]; intros γ0 I E.
      constructor; intros γ1 [I0 (n & ℓ & Hin & H)].
      pose proof (xphi_drop γ0 γ1 n ℓ I0 Hin H) as D.
      apply (IH (XPhi γ1)); [| exact (xtinv_step γ0 γ1 ℓ I0 H) | intros; reflexivity].
      exact (lexR_ext Rb _ _ _ E D). }
    intros I; exact (G (XPhi γ) (lexR_wf Rb _) γ I (fun _ => eq_refl)).
  Qed.

  (** There is no infinite sequence of extended lifecycle steps. *)
  Corollary xno_infinite_run (γ : State) :
    XTInv γ ->
    ~ exists g : nat -> State, g 0 = γ /\
        forall i, exists n ℓ, In ℓ (@lifecycle_labels C n) /\ xstep (g i) ℓ = Some (g (S i)).
  Proof.
    intros I (g & G0 & Gs).
    assert (Inv : forall i, XTInv (g i)).
    { induction i as [|i IH]; [rewrite G0; exact I|].
      destruct (Gs i) as (n & ℓ & _ & H); exact (xtinv_step _ _ ℓ IH H). }
    assert (A : forall x, Acc XLStepRel x -> forall i, g i = x -> False).
    { intros x Hx; induction Hx as [x _ IHx]; intros i Ei.
      refine (IHx (g (S i)) _ (S i) eq_refl).
      rewrite <- Ei; split; [exact (Inv i) | exact (Gs i)]. }
    exact (A γ (xtermination γ I) 0 G0).
  Qed.

  (** From the initial state, after any extended execution (orchestration,
      reactions and lifecycle steps in any order). *)
  Corollary xtermination_reachable (γ : State) :
    XReachable K_eq_dec Σ xprog γ -> Acc XLStepRel γ.
  Proof.
    intros [ls H]; apply xtermination.
    assert (G : forall γ0, XTInv γ0 -> xrun K_eq_dec Σ xprog γ0 ls = Some γ -> XTInv γ).
    { clear H; induction ls as [|ℓ ls IH]; cbn; intros γ0 I0 H0.
      - injection H0 as <-; exact I0.
      - destruct (xstep γ0 ℓ) as [γ1|] eqn:Hs; [|discriminate].
        exact (IH γ1 (xtinv_step γ0 γ1 ℓ I0 Hs) H0). }
    exact (G _ xtinv_init H).
  Qed.
End OptTermination.
