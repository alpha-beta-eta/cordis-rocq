(** * Extension 3: liveness with handler families

    Termination and no-deadlock for executions with payload-indexed
    reactions ([Intersect.v]). The core theorems ask [Inv2]: a child's
    component is one its parent's component may create. A reaction child
    is an instance [h e] of a handler family, which no finite handler list
    names. They are applied to a table that lists, as the handlers of each
    component, the instance at hand (for a reaction step) and the
    components of the children present now ([tbl]); the base-level
    invariant [ISpawnProv] (a child is spawned by its parent's program or
    is an instance of one of its handler families) carries over from step
    to step. The rank must rise along provision, spawn, and every handler
    instance ([IAbove]). *)

From Stdlib Require Import List PeanoNat Bool Lia Wf_nat.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Recovery Progress Termination.
From Cordis Require Import Ext.Intersect.
Import ListNotations.

Section IntersectLive.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (C_eq_dec : forall x y : C, {x = y} + {x <> y}).
  Context {E : Type}.
  Context (iprog : C -> @IComponent K Σ C E).

  Local Notation State := (@State K Σ C).
  Local Notation Fiber := (@Fiber K Σ C).
  Local Notation fibers := (fibers Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation acc_of := (acc_of Σ).
  Local Notation progE := (progE Σ iprog).
  Local Notation progN := (progE None).
  Local Notation istep := (istep K_eq_dec Σ iprog).

  (** ** Hypotheses *)
  Definition ISpawns (c c' : C) : Prop :=
    SpawnIn Σ c' (ibody Σ (iprog c)) \/ exists h e, In h (ireacts Σ (iprog c)) /\ c' = h e.

  Definition IAbove (c c' : C) : Prop :=
    (exists k, In k (iprovs Σ (iprog c)) /\ In k (ideps Σ (iprog c'))) \/ ISpawns c c'.

  Variable Kb : nat.
  Hypothesis HK : forall c, Bounded Σ Kb (ibody Σ (iprog c)).
  Variable rank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', IAbove c c' -> rank c < rank c'.
  Hypothesis Hbnd : forall c, rank c <= Rb.

  (** ** The table for a state *)
  Definition spawned_comps (γ : State) (acc : list (@Undo K Σ)) : list C :=
    flat_map (fun u => match u with
                       | USpawn _ m => match fibers γ m with Some g => [fcomp g] | None => [] end
                       | _ => []
                       end) acc.

  Definition kids (γ : State) (c : C) : list C :=
    flat_map (fun q => match fibers γ q with
                       | Some f => if C_eq_dec (fcomp f) c then spawned_comps γ (acc_of (life f)) else []
                       | None => []
                       end) (names Σ γ).

  Definition tbl (γ : State) (x : option E) (c : C) : @Component K Σ C :=
    mkComponent (deps Σ (progE x c)) (provs Σ (progE x c)) (body Σ (progE x c))
                (reacts Σ (progE x c) ++ kids γ c).

  Definition ISpawnProv (γ : State) : Prop :=
    forall x f m fm, fibers γ x = Some f -> In (USpawn Σ m) (acc_of (life f)) ->
                     fibers γ m = Some fm -> ISpawns (fcomp f) (fcomp fm).

  Lemma spawns_tbl (γ0 : State) x c c' : ISpawnProv γ0 -> Spawns Σ (tbl γ0 x) c c' -> ISpawns c c'.
  Proof.
    intros XP [Hs|Hr]; [left; exact Hs|].
    unfold tbl in Hr; cbn [reacts] in Hr; apply in_app_or in Hr as [Hr|Hr].
    - right; destruct x as [e|]; cbn in Hr; [|contradiction].
      apply in_map_iff in Hr as (h & <- & Hh); exists h, e; auto.
    - unfold kids in Hr; apply in_flat_map in Hr as (q & _ & Hr).
      destruct (fibers γ0 q) as [f|] eqn:Hq; [|contradiction].
      destruct (C_eq_dec (fcomp f) c) as [<-|]; [|contradiction].
      unfold spawned_comps in Hr; apply in_flat_map in Hr as (u & Hu & Hr).
      destruct u as [| |m]; try contradiction.
      destruct (fibers γ0 m) as [g|] eqn:Hm; [|contradiction].
      destruct Hr as [<-|[]]; exact (XP q f m g Hq Hu Hm).
  Qed.

  Lemma above_tbl (γ0 : State) x c c' : ISpawnProv γ0 -> Above Σ (tbl γ0 x) c c' -> rank c < rank c'.
  Proof.
    intros XP [(k & Hp & Hd)|Hs]; apply Hrank; [left; exists k; split; [exact Hp | exact Hd]|].
    right; exact (spawns_tbl γ0 x c c' XP Hs).
  Qed.

  Lemma inv2_tbl (γ : State) x : WF K_eq_dec Σ progN γ -> PidUnique Σ γ -> Inv2 Σ (tbl γ x) γ.
  Proof.
    intros W U; split; [exact U|].
    intros q f m fm Hq Hu Hm; right.
    unfold tbl; cbn [reacts]; apply in_or_app; right.
    unfold kids; apply in_flat_map; exists q; split; [exact (in_names K_eq_dec Σ progN γ q f W Hq)|].
    rewrite Hq; destruct (C_eq_dec (fcomp f) (fcomp f)) as [_|N]; [|contradiction N; reflexivity].
    unfold spawned_comps; apply in_flat_map; exists (USpawn Σ m); split; [exact Hu|].
    rewrite Hm; left; reflexivity.
  Qed.

  Lemma wf_tbl (γ0 : State) x (γ : State) :
    WF K_eq_dec Σ progN γ -> WF K_eq_dec Σ (tbl γ0 x) γ.
  Proof. intros W; destruct W; split; assumption. Qed.

  Lemma wf_untbl (γ0 : State) x (γ : State) :
    WF K_eq_dec Σ (tbl γ0 x) γ -> WF K_eq_dec Σ progN γ.
  Proof. intros W; destruct W; split; assumption. Qed.

  Lemma prov_tbl (γ0 : State) x (γ : State) : Prov Σ progN γ -> Prov Σ (tbl γ0 x) γ.
  Proof. intros [P T]; split; assumption. Qed.

  Lemma prov_untbl (γ0 : State) x (γ : State) : Prov Σ (tbl γ0 x) γ -> Prov Σ progN γ.
  Proof. intros [P T]; split; assumption. Qed.

  Lemma HK_tbl (γ0 : State) x : forall c, Bounded Σ Kb (body Σ (tbl γ0 x c)).
  Proof. intros c; exact (HK c). Qed.

  (** Steps under [progN] or an instantiated table are steps under [tbl]. *)
  Lemma core_tbl (γ0 γ γ' : State) ℓ :
    step K_eq_dec Σ progN γ ℓ = Some γ' -> step K_eq_dec Σ (tbl γ0 None) γ ℓ = Some γ'.
  Proof.
    intros H; destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; try exact H.
    exfalso; cbn [Calculus.step] in H.
    destruct (fibers γ n) as [f|]; [|discriminate H].
    destruct (life f); try discriminate H.
    destruct i; cbn in H; discriminate H.
  Qed.

  Lemma react_tbl (γ0 γ γ' : State) n i e :
    step K_eq_dec Σ (progE (Some e)) γ (OReact n i) = Some γ' ->
    step K_eq_dec Σ (tbl γ0 (Some e)) γ (OReact n i) = Some γ'.
  Proof.
    cbn [Calculus.step]; intros H.
    destruct (fibers γ n) as [f|]; [|discriminate H].
    destruct (life f) as [| |acc w|]; try discriminate H.
    destruct (nth_error (reacts Σ (progE (Some e) (fcomp f))) i) as [c|] eqn:Ec; [|discriminate H].
    assert (E' : nth_error (reacts Σ (tbl γ0 (Some e) (fcomp f))) i = Some c).
    { unfold tbl; cbn [reacts]; rewrite nth_error_app1; [exact Ec|].
      apply nth_error_Some; rewrite Ec; intros D; discriminate D. }
    rewrite E'; exact H.
  Qed.

  (** ** The invariant *)
  Record IInv (γ : State) : Prop := {
    ii_wf : WF K_eq_dec Σ progN γ;
    ii_prov : Prov Σ progN γ;
    ii_pid : PidUnique Σ γ;
    ii_spawn : ISpawnProv γ;
    ii_lb : LoadBound Σ Kb γ;
    ii_so : SpawnOwn Σ γ
  }.

  Lemma iinv_init : IInv (@init K Σ C).
  Proof.
    split; [exact (wf_init K_eq_dec Σ progN) | exact (prov_init Σ progN) | ..]; cbn; intros; discriminate.
  Qed.

  Lemma tinv_tbl (γ : State) x : IInv γ -> TInv K_eq_dec Σ (tbl γ x) Kb γ.
  Proof.
    intros [W P U X LB SO].
    exact (Build_TInv _ _ _ _ _ (wf_tbl γ x γ W) (prov_tbl γ x γ P) (inv2_tbl γ x W U) LB SO).
  Qed.

  (** A step under [tbl γ x] keeps the invariant. *)
  Lemma iinv_tbl_step (γ γ' : State) x ℓ :
    IInv γ -> step K_eq_dec Σ (tbl γ x) γ ℓ = Some γ' -> IInv γ'.
  Proof.
    intros I H; pose proof (proj2 (conj I I)) as [_ _ _ X _ _].
    destruct (tinv_step K_eq_dec Σ (tbl γ x) Kb (HK_tbl γ x) γ γ' ℓ (tinv_tbl γ x I) H)
      as [W' P' [U' Sp'] LB' SO'].
    split; [exact (wf_untbl γ x γ' W') | exact (prov_untbl γ x γ' P') | exact U' | | exact LB' | exact SO'].
    intros q f m fm Hq Hu Hm; exact (spawns_tbl γ x _ _ X (Sp' q f m fm Hq Hu Hm)).
  Qed.

  Theorem iinv_step (γ γ' : State) ℓ : IInv γ -> istep γ ℓ = Some γ' -> IInv γ'.
  Proof.
    intros I; destruct ℓ as [ℓ|n i e]; cbn [Intersect.istep]; intros H.
    - exact (iinv_tbl_step γ γ' None ℓ I (core_tbl γ γ γ' ℓ H)).
    - exact (iinv_tbl_step γ γ' (Some e) _ I (react_tbl γ γ γ' n i e H)).
  Qed.

  Theorem iinv_reachable (γ : State) : IReachable K_eq_dec Σ iprog γ -> IInv γ.
  Proof. apply irun_inv; [exact iinv_init | exact iinv_step]. Qed.

  (** ** Termination *)
  Definition ILStepRel (γ' γ : State) : Prop :=
    IInv γ /\ exists n ℓ, In ℓ (@lifecycle_labels C n) /\ step K_eq_dec Σ progN γ ℓ = Some γ'.

  Lemma acc_transfer (T : C -> @Component K Σ C) :
    (forall γ γ' ℓ, (exists n, In ℓ (@lifecycle_labels C n)) ->
       step K_eq_dec Σ progN γ ℓ = Some γ' -> step K_eq_dec Σ T γ ℓ = Some γ') ->
    (forall c, Bounded Σ Kb (body Σ (T c))) ->
    forall γ, Acc (LStepRel K_eq_dec Σ T Kb) γ -> TInv K_eq_dec Σ T Kb γ -> IInv γ -> Acc ILStepRel γ.
  Proof.
    intros Hst HKT γ A; induction A as [γ _ IH]; intros T0 I0.
    constructor; intros γ1 [_ (n & ℓ & Hin & H)].
    pose proof (Hst γ γ1 ℓ (ex_intro _ n Hin) H) as HT.
    apply IH; [split; [exact T0 | exists n, ℓ; auto] | exact (tinv_step K_eq_dec Σ T Kb HKT γ γ1 ℓ T0 HT) |].
    exact (iinv_step γ γ1 (ICore ℓ) I0 H).
  Qed.

  Theorem itermination (γ : State) : IInv γ -> Acc ILStepRel γ.
  Proof.
    intros I.
    pose proof (tinv_tbl γ None I) as T.
    pose proof (termination K_eq_dec Σ (tbl γ None) Kb (HK_tbl γ None) rank Rb
                  (fun c c' HA => above_tbl γ None c c' (ii_spawn _ I) HA) Hbnd γ T) as A.
    apply (acc_transfer (tbl γ None)); auto.
    intros γ1 γ1' ℓ _ H; exact (core_tbl γ γ1 γ1' ℓ H).
  Qed.

  Corollary itermination_reachable (γ : State) : IReachable K_eq_dec Σ iprog γ -> Acc ILStepRel γ.
  Proof. intros R; exact (itermination γ (iinv_reachable γ R)). Qed.

  (** ** No deadlock *)
  Theorem iquiet_settled (γ : State) :
    IInv γ -> quiet K_eq_dec Σ progN γ -> settled Σ progN γ.
  Proof.
    intros I Q.
    assert (Hwf : well_founded (fun c' c => Above Σ (tbl γ None) c c')).
    { apply (well_founded_lt_compat C (fun c => Rb - rank c)).
      intros c' c HA; pose proof (above_tbl γ None c c' (ii_spawn _ I) HA); pose proof (Hbnd c'); lia. }
    assert (Q' : quiet K_eq_dec Σ (tbl γ None) γ).
    { intros n ℓ Hin; pose proof (Q n ℓ Hin) as Qn.
      destruct ℓ; try exact Qn; cbn in Hin; intuition discriminate. }
    exact (quiet_settled K_eq_dec Σ (tbl γ None) Hwf γ (wf_tbl γ None γ (ii_wf _ I))
             (inv2_tbl γ None (ii_wf _ I) (ii_pid _ I)) Q').
  Qed.
End IntersectLive.
