(** * Telling external failures apart (errors/DESIGN.md, section 5.2; principle P4)

    [Async.unfold] turns a refused read into the core's [PFail], so in the
    core state an external failure and a program's own [EFail] carry the
    same mark [EUser]. The distinction is recovered on the extended
    program, as a property of the ideal trace:

    - [ETr]: ideal traces of the extended program; a successful read is a
      step ([XRead]) that changes nothing else;
    - [etr_det], [efail_unique]: traces are determined, so an ideal trace
      has at most one failure point;
    - [etr_tr], [tr_etr]: erasing reads, extended traces are the core's
      ideal traces of the unfolded table [Async.prog'];
    - [kinds_cover], [kinds_exclusive]: a component fails ideally in the
      unfolded table iff its extended trace stops at a refused read, at a
      program failure, or at an operation failure, and exactly one of
      these;
    - [kind_ext]: the kind depends only on [ρ] at the declared keys.

    With [FailCrux.quiet_failed_ideal] for the unfolded table, every failed
    fiber of a quiet state has exactly one kind, the same in every run with
    the same inputs. A runtime can report it.

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service ServiceSeq Calculus Preservation Ordering Progress
  Recovery Termination Confluence StateInv Episode.
From CordisErr Require Import Async IdealFail.
Import ListNotations.

Section AsyncKind.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type}.
  Context (E R : Type).
  Variable xprog : C -> @XComponent K Σ C E R.
  Variable world : C -> E -> option R.
  Hypothesis Hwb : forall a t, WellBehaved (Σ := Σ) a t.

  Local Notation EProg := (@EProg K Σ C E R).
  Local Notation P' := (prog' Σ E R xprog world).
  Local Notation S := (St Σ).
  Local Notation Ev := (@Ev K Σ C).
  Local Notation Tr := (Tr K_eq_dec Σ P').
  Local Notation resolveI := (resolveI K_eq_dec Σ P').
  Local Notation ownIt := (ownIt K_eq_dec Σ).
  Local Notation unf c := (unfold Σ E R (world c)).
  Local Notation xb c := (xbody Σ E R (xprog c)).
  Local Notation cdeps c := (deps Σ (P' c)).

  (** ** Extended ideal traces *)
  Inductive XEv : Type := XE (ev : Ev) | XRead.

  Fixpoint erase (xs : list XEv) : list Ev :=
    match xs with
    | [] => []
    | XE ev :: xs' => ev :: erase xs'
    | XRead :: xs' => erase xs'
    end.

  Inductive ETr (c : C) (ρ : K -> option S) : list XEv -> EProg -> Prop :=
  | etr_nil : ETr c ρ [] (xb c)
  | etr_op xs k a κ s0 s1 s' g o :
      ETr c ρ xs (EOp Σ E R k a κ) -> resolveI c ρ (erase xs) k = Some s0 ->
      Replay (ownIt k (erase xs)) s0 s1 ->
      run a 0 s1 = Some (s', g, o) -> ETr c ρ (XE (TOp Σ k a) :: xs) (κ o)
  | etr_prov xs k s P :
      ETr c ρ xs (EProvide Σ E R k s P) -> ETr c ρ (XE (TProv Σ k s) :: xs) P
  | etr_spawn xs c' P :
      ETr c ρ xs (ESpawn Σ E R c' P) -> ETr c ρ (XE (TSpawn Σ c') :: xs) P
  | etr_read xs e κ r :
      ETr c ρ xs (EExt Σ E R e κ) -> world c e = Some r -> ETr c ρ (XRead :: xs) (κ r).

  Lemma etr_det c ρ xs1 xs2 P1 P2 :
    ETr c ρ xs1 P1 -> ETr c ρ xs2 P2 -> length xs1 = length xs2 -> xs1 = xs2 /\ P1 = P2.
  Proof.
    intros H1; revert xs2 P2.
    induction H1 as [|xs k a κ s0 s1 s' g o T1 IH R1 Rp1 X1|xs k s P T1 IH|xs c' P T1 IH|xs e κ r T1 IH W1];
      intros xs2 P2 H2 L.
    - destruct xs2; [|discriminate]; inversion H2; auto.
    - destruct xs2 as [|x xs2]; [discriminate|]; cbn in L; injection L as L.
      inversion H2 as [|xs' k' a' κ' s0' s1' s'' g' o' T2 R2 Rp2 X2|xs' k' s'' P' T2|xs' c'' P' T2|xs' e' κ' r' T2 W2];
        subst; destruct (IH _ _ T2 L) as [<- E2]; try discriminate.
      injection E2 as <- <- <-.
      rewrite R1 in R2; injection R2 as <-.
      pose proof (replay_det _ _ _ _ Rp1 Rp2) as E12.
      pose proof (wb_respects _ _ (Hwb a 0) s1 s1' E12) as Hres; rewrite X1, X2 in Hres; cbn in Hres.
      destruct Hres as (_ & _ & <-); auto.
    - destruct xs2 as [|x xs2]; [discriminate|]; cbn in L; injection L as L.
      inversion H2 as [|xs' k' a' κ' s0' s1' s'' g' o' T2 R2 Rp2 X2|xs' k' s'' P' T2|xs' c'' P' T2|xs' e' κ' r' T2 W2];
        subst; destruct (IH _ _ T2 L) as [<- E2]; try discriminate.
      injection E2 as <- <- <-; auto.
    - destruct xs2 as [|x xs2]; [discriminate|]; cbn in L; injection L as L.
      inversion H2 as [|xs' k' a' κ' s0' s1' s'' g' o' T2 R2 Rp2 X2|xs' k' s'' P' T2|xs' c'' P' T2|xs' e' κ' r' T2 W2];
        subst; destruct (IH _ _ T2 L) as [<- E2]; try discriminate.
      injection E2 as <- <-; auto.
    - destruct xs2 as [|x xs2]; [discriminate|]; cbn in L; injection L as L.
      inversion H2 as [|xs' k' a' κ' s0' s1' s'' g' o' T2 R2 Rp2 X2|xs' k' s'' P' T2|xs' c'' P' T2|xs' e' κ' r' T2 W2];
        subst; destruct (IH _ _ T2 L) as [<- E2]; try discriminate.
      injection E2 as <- <-; rewrite W1 in W2; injection W2 as <-; auto.
  Qed.

  Lemma etr_drop c ρ pre l P : ETr c ρ (pre ++ l) P -> exists P', ETr c ρ l P'.
  Proof.
    revert P; induction pre as [|x pre IH]; intros P H; [exists P; exact H|].
    cbn in H; inversion H; subst; eapply IH; eassumption.
  Qed.

  (** ** Failure points *)
  Definition EFailPt (c : C) (ρ : K -> option S) (xs : list XEv) (P : EProg) : Prop :=
    match P with
    | EFail _ _ _ => True
    | EExt _ _ _ e _ => world c e = None
    | EOp _ _ _ k a _ =>
        resolveI c ρ (erase xs) k = None \/
        exists s0 s1, resolveI c ρ (erase xs) k = Some s0 /\ Replay (ownIt k (erase xs)) s0 s1 /\
                      run a 0 s1 = None
    | _ => False
    end.

  Lemma efail_no_step c ρ xs P x Q :
    ETr c ρ xs P -> EFailPt c ρ xs P -> ETr c ρ (x :: xs) Q -> False.
  Proof.
    intros T F T2.
    inversion T2 as [|xs' k a κ s0 s1 s' g o T3 R3 Rp3 X3|xs' k s P' T3|xs' c' P' T3|xs' e κ r T3 W3]; subst;
      destruct (etr_det c ρ xs xs P _ T T3 eq_refl) as [_ ->]; cbn in F; try contradiction.
    - destruct F as [F|(s0' & s1' & F & Rp & X)]; [congruence|].
      rewrite R3 in F; injection F as <-.
      pose proof (replay_det _ _ _ _ Rp Rp3) as Es.
      pose proof (wb_respects _ _ (Hwb a 0) s1' s1 Es) as Hres; rewrite X, X3 in Hres; exact Hres.
    - congruence.
  Qed.

  Lemma efail_unique c ρ xs1 xs2 P1 P2 :
    ETr c ρ xs1 P1 -> EFailPt c ρ xs1 P1 -> ETr c ρ xs2 P2 -> EFailPt c ρ xs2 P2 ->
    xs1 = xs2 /\ P1 = P2.
  Proof.
    assert (G : forall ys1 ys2 Q1 Q2, ETr c ρ ys1 Q1 -> EFailPt c ρ ys1 Q1 -> ETr c ρ ys2 Q2 ->
                length ys1 <= length ys2 -> ys1 = ys2 /\ Q1 = Q2).
    { intros ys1 ys2 Q1 Q2 T1 F1 T2 Hle.
      destruct (Nat.eq_dec (length ys1) (length ys2)) as [Heq|Hne].
      - exact (etr_det c ρ ys1 ys2 Q1 Q2 T1 T2 Heq).
      - exfalso.
        set (d := length ys2 - Datatypes.S (length ys1)).
        assert (Hsk : length (skipn d ys2) = Datatypes.S (length ys1))
          by (rewrite length_skipn; unfold d; lia).
        rewrite <- (firstn_skipn d ys2) in T2.
        destruct (skipn d ys2) as [|x r] eqn:Es; [discriminate|]; cbn in Hsk; injection Hsk as Hsk.
        destruct (etr_drop c ρ _ _ _ T2) as (Q & T3).
        assert (T4 : exists P', ETr c ρ r P') by (inversion T3; subst; eauto).
        destruct T4 as (P' & T4).
        destruct (etr_det c ρ r ys1 P' Q1 T4 T1 Hsk) as [-> _].
        exact (efail_no_step c ρ ys1 Q1 x Q T1 F1 T3). }
    intros T1 F1 T2 F2.
    destruct (Nat.le_ge_cases (length xs1) (length xs2)) as [Hle|Hge].
    - exact (G xs1 xs2 P1 P2 T1 F1 T2 Hle).
    - destruct (G xs2 xs1 P2 P1 T2 F2 T1 Hge) as [-> ->]; auto.
  Qed.

  (** ** Extended traces are core traces, reads erased *)
  Lemma etr_tr c ρ xs P : ETr c ρ xs P -> Tr c ρ (erase xs) (unf c P).
  Proof.
    induction 1 as [|xs k a κ s0 s1 s' g o T IH HR Rp X|xs k s P T IH|xs c' P T IH|xs e κ r T IH W]; cbn.
    - constructor.
    - exact (tr_op K_eq_dec Σ P' c ρ (erase xs) k a (fun o => unf c (κ o)) s0 s1 s' g o IH HR Rp X).
    - apply tr_prov; exact IH.
    - apply tr_spawn; exact IH.
    - cbn in IH; rewrite W in IH; exact IH.
  Qed.

  (** Following successful reads. *)
  Lemma follow c ρ xs P :
    ETr c ρ xs P ->
    exists xs' P', ETr c ρ xs' P' /\ erase xs' = erase xs /\ unf c P' = unf c P /\
      (forall e κ r, P' = EExt Σ E R e κ -> world c e <> Some r).
  Proof.
    revert xs; induction P as [| |k a κ IH|k s P IH|c' P IH|e κ IH]; intros xs T.
    1-5: exists xs; eexists; split; [exact T|]; split; [reflexivity|]; split; [reflexivity|];
      intros e0 κ0 r0 Hq; discriminate.
    destruct (world c e) as [r|] eqn:W.
    - destruct (IH r (XRead :: xs) (etr_read c ρ xs e κ r T W)) as (xs' & P' & T' & Er & Eu & Hn).
      exists xs', P'; split; [exact T'|]; split; [exact Er|]; split; [|exact Hn].
      rewrite Eu; cbn; rewrite W; reflexivity.
    - exists xs, (EExt Σ E R e κ); split; [exact T|]; split; [reflexivity|]; split; [reflexivity|].
      intros e0 κ0 r0 Hq; injection Hq as -> _; congruence.
  Qed.

  Lemma tr_etr c ρ evs Q :
    Tr c ρ evs Q -> exists xs P, ETr c ρ xs P /\ erase xs = evs /\ unf c P = Q.
  Proof.
    induction 1 as [|evs k a κ s0 s1 s' g o T IH HR Rp X|evs k s P T IH|evs c' P T IH].
    - exists [], (xb c); split; [constructor|]; split; reflexivity.
    - destruct IH as (xs & P & T1 & Er & Eu).
      destruct (follow c ρ xs P T1) as (xs' & P' & T2 & Er' & Eu' & Hn).
      rewrite <- Eu' in Eu.
      destruct P' as [| |k' a' κ'|k' s2 P''|c' P''|e κ']; cbn in Eu; try discriminate.
      + injection Eu as -> -> Eκ.
        exists (XE (TOp Σ k a) :: xs'), (κ' o); split.
        * eapply etr_op; [exact T2 | rewrite Er', Er; exact HR | rewrite Er', Er; exact Rp | exact X].
        * split; [cbn; rewrite Er', Er; reflexivity|].
          change (unf c (κ' o)) with ((fun o => unf c (κ' o)) o); rewrite Eκ; reflexivity.
      + destruct (world c e) as [r|] eqn:W; [exfalso; exact (Hn e κ' r eq_refl W) | discriminate].
    - destruct IH as (xs & P0 & T1 & Er & Eu).
      destruct (follow c ρ xs P0 T1) as (xs' & P' & T2 & Er' & Eu' & Hn).
      rewrite <- Eu' in Eu.
      destruct P' as [| |k' a' κ'|k' s2 P''|c' P''|e κ']; cbn in Eu; try discriminate.
      + injection Eu as -> -> EP.
        exists (XE (TProv Σ k s) :: xs'), P''; split; [apply etr_prov; exact T2|].
        split; [cbn; rewrite Er', Er; reflexivity | exact EP].
      + destruct (world c e) as [r|] eqn:W; [exfalso; exact (Hn e κ' r eq_refl W) | discriminate].
    - destruct IH as (xs & P0 & T1 & Er & Eu).
      destruct (follow c ρ xs P0 T1) as (xs' & P' & T2 & Er' & Eu' & Hn).
      rewrite <- Eu' in Eu.
      destruct P' as [| |k' a' κ'|k' s2 P''|c'' P''|e κ']; cbn in Eu; try discriminate.
      + injection Eu as -> EP.
        exists (XE (TSpawn Σ c') :: xs'), P''; split; [apply etr_spawn; exact T2|].
        split; [cbn; rewrite Er', Er; reflexivity | exact EP].
      + destruct (world c e) as [r|] eqn:W; [exfalso; exact (Hn e κ' r eq_refl W) | discriminate].
  Qed.

  (** ** The kinds of failure *)
  Definition ExtFails c ρ : Prop := exists xs e κ, ETr c ρ xs (EExt Σ E R e κ) /\ world c e = None.
  Definition ProgFails c ρ : Prop := exists xs, ETr c ρ xs (EFail Σ E R).
  Definition OpFails c ρ : Prop :=
    exists xs k a κ, ETr c ρ xs (EOp Σ E R k a κ) /\ EFailPt c ρ xs (EOp Σ E R k a κ).

  Local Notation IdealFails := (IdealFails K_eq_dec Σ P').

  Theorem kinds_cover c ρ : IdealFails c ρ <-> ExtFails c ρ \/ ProgFails c ρ \/ OpFails c ρ.
  Proof.
    split.
    - intros (evs & Q & T & F).
      destruct (tr_etr c ρ evs Q T) as (xs & P & T1 & Er & Eu).
      destruct (follow c ρ xs P T1) as (xs' & P' & T2 & Er' & Eu' & Hn).
      rewrite <- Eu' in Eu; subst Q.
      destruct P' as [| |k a κ|k s P''|c' P''|e κ]; cbn in F; try contradiction.
      + right; left; exists xs'; exact T2.
      + right; right; exists xs', k, a, κ; split; [exact T2|]; cbn.
        rewrite Er', Er; exact F.
      + destruct (world c e) as [r|] eqn:W; [exfalso; exact (Hn e κ r eq_refl W)|].
        left; exists xs', e, κ; auto.
    - intros [(xs & e & κ & T & W)|[(xs & T)|(xs & k & a & κ & T & F)]].
      + exists (erase xs), PFail; split; [|exact Logic.I].
        pose proof (etr_tr c ρ xs _ T) as T'; cbn in T'; rewrite W in T'; exact T'.
      + exists (erase xs), PFail; split; [exact (etr_tr c ρ xs _ T) | exact Logic.I].
      + exists (erase xs), (unf c (EOp Σ E R k a κ)); split; [exact (etr_tr c ρ xs _ T)|]; cbn; exact F.
  Qed.

  Theorem kinds_exclusive c ρ :
    (ExtFails c ρ -> ~ ProgFails c ρ /\ ~ OpFails c ρ) /\ (ProgFails c ρ -> ~ OpFails c ρ).
  Proof.
    split; [intros (xs & e & κ & T & W); split|].
    - intros (xs' & T'); destruct (efail_unique c ρ xs xs' _ _ T W T' Logic.I) as [_ Eq]; discriminate.
    - intros (xs' & k & a & κ' & T' & F'); destruct (efail_unique c ρ xs xs' _ _ T W T' F') as [_ Eq]; discriminate.
    - intros (xs & T) (xs' & k & a & κ' & T' & F').
      destruct (efail_unique c ρ xs xs' _ _ T Logic.I T' F') as [_ Eq]; discriminate.
  Qed.

  (** ** The kind depends only on the declared keys of [ρ] *)
  Lemma etr_ext c ρ1 ρ2 xs P :
    (forall k, In k (cdeps c) -> ρ1 k = ρ2 k) -> ETr c ρ1 xs P -> ETr c ρ2 xs P.
  Proof.
    intros Eρ H; induction H as [|xs k a κ s0 s1 s' g o T IH HR Rp X|xs k s P T IH|xs c' P T IH|xs e κ r T IH W].
    - constructor.
    - eapply etr_op; [exact IH | | exact Rp | exact X].
      rewrite <- (resolveI_ext K_eq_dec Σ P' c ρ1 ρ2 (erase xs) k Eρ); exact HR.
    - apply etr_prov; exact IH.
    - apply etr_spawn; exact IH.
    - eapply etr_read; [exact IH | exact W].
  Qed.

  Theorem kind_ext c ρ1 ρ2 :
    (forall k, In k (cdeps c) -> ρ1 k = ρ2 k) ->
    (ExtFails c ρ1 <-> ExtFails c ρ2) /\ (ProgFails c ρ1 <-> ProgFails c ρ2) /\ (OpFails c ρ1 <-> OpFails c ρ2).
  Proof.
    intros Eρ.
    assert (Eρ' : forall k, In k (cdeps c) -> ρ2 k = ρ1 k) by (intros k Hk; symmetry; exact (Eρ k Hk)).
    assert (FP : forall ρa ρb xs k a κ, (forall k, In k (cdeps c) -> ρa k = ρb k) ->
                 EFailPt c ρa xs (EOp Σ E R k a κ) -> EFailPt c ρb xs (EOp Σ E R k a κ)).
    { intros ρa ρb xs k a κ Ea F; cbn in *.
      rewrite <- (resolveI_ext K_eq_dec Σ P' c ρa ρb (erase xs) k Ea); exact F. }
    split; [|split]; split.
    - intros (xs & e & κ & T & W); exists xs, e, κ; split; [exact (etr_ext c ρ1 ρ2 xs _ Eρ T) | exact W].
    - intros (xs & e & κ & T & W); exists xs, e, κ; split; [exact (etr_ext c ρ2 ρ1 xs _ Eρ' T) | exact W].
    - intros (xs & T); exists xs; exact (etr_ext c ρ1 ρ2 xs _ Eρ T).
    - intros (xs & T); exists xs; exact (etr_ext c ρ2 ρ1 xs _ Eρ' T).
    - intros (xs & k & a & κ & T & F); exists xs, k, a, κ;
        split; [exact (etr_ext c ρ1 ρ2 xs _ Eρ T) | exact (FP ρ1 ρ2 xs k a κ Eρ F)].
    - intros (xs & k & a & κ & T & F); exists xs, k, a, κ;
        split; [exact (etr_ext c ρ2 ρ1 xs _ Eρ' T) | exact (FP ρ2 ρ1 xs k a κ Eρ' F)].
  Qed.
End AsyncKind.
