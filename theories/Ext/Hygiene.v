(** * Hygiene: the host tags every contribution (docs/CONTRIB.md, stage E6d)

    Components are written with contributions and reads whose tag they do
    not choose. The host fills it in: [hprog] rewrites the startup program
    of component [c] so that every contribution carries tag [c] and every
    read reads as [c] ([retag]), the way a hygienic expander marks the
    names a macro introduces. No other change: dependencies, provisions,
    spawned children and handlers are those of the base table, and a
    spawned child is tagged by its own component when it starts.

    What tagging buys over E6b:

    - Reading one's own private names at startup. E6b excluded every read
      beside a contribution. A private name read by [c] resolves among
      [c]'s contributions only ([resolve_private_local]), so a read by [c]
      commutes with a contribution under any other tag. The relation
      [hyg_meet] admits that pair, and [hyg_hyps] shows the confluence
      hypotheses still hold.
    - Coverage from the shape of the programs alone ([hyg_covers]): reads
      at startup are of private names, and a component that reads runs in
      one fiber at a time (it provides a key). Then two fibers that meet
      at a contribution key are two different components, or they only
      contribute.
    - Distinct entries for recovery ([hyg_covers_rev]): contributions of
      two components carry two tags, so they differ. Two fibers of one
      component may still contribute the same entry; recovery therefore
      asks a contributing component to run in one fiber at a time. This is
      the limit recorded as open question 6 in docs/CONTRIB.md.

    The corollaries ([hyg_confluence], [hyg_static], [hyg_recovery]) are
    the summary theorem read through [resolve], as in E6b, for the tagged
    table. Nothing in the core imports this file. *)

From Stdlib Require Import RelationClasses List PeanoNat Bool Permutation.
From Cordis Require Import Prelude Service ServiceSeq Calculus Recovery Compose
  Confluence SpawnConf Dynamic Summary Listeners Contrib ContribConf.
Import ListNotations.

Section Hygiene.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context {C : Type} (C_eq_dec : forall x y : C, {x = y} + {x <> y}).
  Context (Name V : Type).
  Context (name_eq_dec : forall x y : Name, {x = y} + {x <> y}).
  Context (v_eq_dec : forall x y : V, {x = y} + {x <> y}).
  Context (public : Name -> bool) (prio : V -> nat).

  (** Tags are components. *)
  Local Notation CS := (Contrib C Name V C_eq_dec name_eq_dec v_eq_dec public prio).
  Local Notation Entry := (Entry C Name V).
  Local Notation etag := (etag C Name V).
  Local Notation teqb := (teqb C C_eq_dec).
  Local Notation edec := (entry_eq_dec C Name V C_eq_dec name_eq_dec v_eq_dec).
  Local Notation rf := (remove_first Entry edec).
  Local Notation resolve := (resolve C Name V C_eq_dec name_eq_dec v_eq_dec public prio).
  Local Notation Prog := (@Prog K CS C).

  (** ** Retagging *)
  Definition tagop (c : C) (a : Op CS) : Op CS :=
    match a with
    | Contribute (_, x, v) => Contribute (c, x, v)
    | Read _ x => Read c x
    end.

  Fixpoint retag (c : C) (P : Prog) : Prog :=
    match P with
    | PDone => PDone
    | PFail => PFail
    | POp k a κ => POp k (tagop c a) (fun o => retag c (κ o))
    | PProvide k s Q => PProvide k s (retag c Q)
    | PSpawn c' Q => PSpawn c' (retag c Q)
    end.

  Context (uprog : C -> @Component K CS C).

  Definition hprog (c : C) : @Component K CS C :=
    mkComponent (deps CS (uprog c)) (provs CS (uprog c))
                (retag c (body CS (uprog c))) (reacts CS (uprog c)).

  Lemma opat_retag c k a P :
    OpAt CS k a (retag c P) -> exists a0, OpAt CS k a0 P /\ a = tagop c a0.
  Proof.
    induction P as [| |k' b κ IH|k' s Q IH|c' Q IH]; cbn; intros H; inversion H; subst.
    - exists b; split; [constructor | reflexivity].
    - destruct (IH o H1) as (a0 & Ha0 & ->); exists a0; split; [apply at_cont with (o := o); exact Ha0 | reflexivity].
    - destruct (IH H1) as (a0 & Ha0 & ->); exists a0; split; [apply at_prov; exact Ha0 | reflexivity].
    - destruct (IH H1) as (a0 & Ha0 & ->); exists a0; split; [apply at_spawn; exact Ha0 | reflexivity].
  Qed.

  Definition tag_of (a : Op CS) : C :=
    match a with Contribute e => etag e | Read q _ => q end.

  (** Every operation in [c]'s tagged program carries tag [c]. *)
  Corollary hprog_tagged c k a :
    OpAt CS k a (body CS (hprog c)) -> tag_of a = c /\ exists a0, OpAt CS k a0 (body CS (uprog c)) /\ a = tagop c a0.
  Proof.
    intros H; destruct (opat_retag c k a _ H) as (a0 & Ha0 & ->).
    split; [destruct a0 as [[[t x] v]|q x]; reflexivity | exists a0; split; [exact Ha0 | reflexivity]].
  Qed.

  (** ** Reads of one's own private names *)
  Definition hyg_meet (a b : Op CS) : Prop :=
    match a, b with
    | Contribute _, Contribute _ | Read _ _, Read _ _ => True
    | Contribute e, Read q x | Read q x, Contribute e => public x = false /\ etag e <> q
    end.

  Definition hyg_rev (a b : Op CS) : Prop :=
    match a, b with
    | Contribute e, Contribute e' => e <> e'
    | Read _ _, Read _ _ => True
    | Contribute e, Read q x | Read q x, Contribute e => public x = false /\ etag e <> q
    end.

  Lemma teqb_false t q : t <> q -> teqb t q = false.
  Proof. intros H; unfold Contrib.teqb; destruct (C_eq_dec t q); [contradiction | reflexivity]. Qed.

  Lemma filter_rf e q s :
    teqb (etag e) q = false ->
    filter (fun e' => teqb (etag e') q) (rf e s) = filter (fun e' => teqb (etag e') q) s.
  Proof.
    intros He; induction s as [|y s IH]; cbn; [reflexivity|].
    destruct (edec y e) as [->|_]; cbn; [rewrite He; reflexivity|].
    destruct (teqb (etag y) q); [f_equal|]; exact IH.
  Qed.

  (** A contribution under another tag does not move a private read. *)
  Lemma read_other_cons e s q x :
    public x = false -> etag e <> q -> resolve (e :: s) q x = resolve s q x.
  Proof.
    intros Hp Hne.
    rewrite (resolve_private_local _ _ _ _ _ _ _ _ (e :: s) q x Hp),
            (resolve_private_local _ _ _ _ _ _ _ _ s q x Hp).
    cbn; rewrite (teqb_false _ _ Hne); reflexivity.
  Qed.

  Lemma read_other_rf e s q x :
    public x = false -> etag e <> q -> resolve (rf e s) q x = resolve s q x.
  Proof.
    intros Hp Hne.
    rewrite (resolve_private_local _ _ _ _ _ _ _ _ (rf e s) q x Hp),
            (resolve_private_local _ _ _ _ _ _ _ _ s q x Hp),
            (filter_rf e q s (teqb_false _ _ Hne)); reflexivity.
  Qed.

  Local Notation inv_c := (inv_of_contribute C Name V C_eq_dec name_eq_dec v_eq_dec public prio).
  Local Notation inv_r := (inv_of_read C Name V C_eq_dec name_eq_dec v_eq_dec public prio).
  Local Notation after_in := (ContribConf.after_in C Name V C_eq_dec name_eq_dec v_eq_dec public prio).
  Local Notation rf_skip := (ContribConf.rf_skip C Name V C_eq_dec name_eq_dec v_eq_dec).
  Local Notation rf_comm := (ContribConf.rf_comm C Name V C_eq_dec name_eq_dec v_eq_dec).

  Lemma hyg_revert_after : RevAfter CS hyg_meet.
  Proof.
    intros a b ta tb g Hab _ Hy x Hx.
    destruct a as [e|q y].
    - rewrite (inv_c e ta g Hy).
      destruct b as [e'|q y]; cbn.
      + pose proof (after_in _ e ta x Hx) as Hin.
        split; [symmetry; exact (rf_cons_in _ edec e e' x Hin) | split; [intros z; reflexivity | reflexivity]].
      + destruct Hab as [Hp Hne].
        split; [reflexivity | split; [intros z; reflexivity | rewrite (read_other_rf e x q y Hp Hne); reflexivity]].
    - rewrite (inv_r q y ta g Hy).
      destruct b as [e'|q' y']; cbn; (split; [reflexivity | split; [intros z; reflexivity | reflexivity]]).
  Qed.

  Lemma hyg_com : ComG CS hyg_meet.
  Proof.
    intros a b ta tb Hab _ s.
    destruct a as [e|q x], b as [e'|q' x']; cbn in Hab |- *.
    - split; [apply perm_swap | split; reflexivity].
    - destruct Hab as [Hp Hne]; split; [reflexivity | split; [reflexivity | rewrite (read_other_cons e s q' x' Hp Hne); reflexivity]].
    - destruct Hab as [Hp Hne]; split; [reflexivity | split; [rewrite (read_other_cons e' s q x Hp Hne); reflexivity | reflexivity]].
    - split; [reflexivity | split; reflexivity].
  Qed.

  Theorem hyg_hyps : ConfHyps CS hyg_meet.
  Proof.
    split.
    - exact (contrib_well_behaved C Name V C_eq_dec name_eq_dec v_eq_dec public prio).
    - exact (contrib_inverse_uniform C Name V C_eq_dec name_eq_dec v_eq_dec public prio).
    - exact (contrib_token_irrelevant C Name V C_eq_dec name_eq_dec v_eq_dec public prio).
    - exact hyg_revert_after.
    - exact hyg_com.
  Qed.

  Lemma hyg_revert_indep a b ta tb : hyg_rev a b -> RevertIndep (Σ := CS) a ta b tb.
  Proof.
    intros Hab g Hy.
    destruct a as [e|q y].
    - rewrite (inv_c e ta g Hy).
      destruct b as [e'|q y]; cbn in Hab.
      + split.
        * intros x; cbn [run Contrib crun shifted].
          rewrite (rf_skip e' e x (fun E => Hab (eq_sym E))).
          split; [reflexivity | split; [intros z; reflexivity | reflexivity]].
        * intros h x Hh; rewrite (inv_c e' tb h Hh); cbn; rewrite rf_comm; reflexivity.
      + destruct Hab as [Hp Hne]; split.
        * intros x; cbn.
          split; [reflexivity | split; [intros z; reflexivity | rewrite (read_other_rf e x q y Hp Hne); reflexivity]].
        * intros h x Hh; rewrite (inv_r q y tb h Hh); reflexivity.
    - rewrite (inv_r q y ta g Hy); split.
      + intros x; destruct b as [e'|q' y']; cbn;
          (split; [reflexivity | split; [intros z; reflexivity | reflexivity]]).
      + intros h x _; reflexivity.
  Qed.

  Theorem hyg_revertible : Revertible CS hyg_rev.
  Proof.
    split.
    - exact (contrib_well_behaved C Name V C_eq_dec name_eq_dec v_eq_dec public prio).
    - intros a b ta tb Hab _; exact (hyg_revert_indep a b ta tb Hab).
  Qed.

  (** ** Coverage from the shape of the programs *)

  (** Startup reads are of private names, by a component that runs in one
      fiber at a time. *)
  Definition ReadsOwn : Prop :=
    forall c k q x, OpAt CS k (Read q x) (body CS (uprog c)) ->
      public x = false /\ provs CS (uprog c) <> [].

  (** A component that contributes runs in one fiber at a time. *)
  Definition ContribSingle : Prop :=
    forall c k e, OpAt CS k (Contribute e) (body CS (uprog c)) -> provs CS (uprog c) <> [].

  Lemma read_shape c k q x :
    ReadsOwn -> OpAt CS k (Read q x) (body CS (hprog c)) ->
    q = c /\ public x = false /\ provs CS (uprog c) <> [].
  Proof.
    intros RO H; destruct (hprog_tagged c k _ H) as [Hq (a0 & Ha0 & E)].
    destruct a0 as [[[t y] v]|q0 y]; cbn in E; [discriminate|].
    injection E as -> ->; split; [reflexivity|].
    exact (RO c k q0 y Ha0).
  Qed.

  Theorem hyg_covers : ReadsOwn -> Covers CS hprog hyg_meet.
  Proof.
    intros RO k a b (c & c' & Ha & Hb & Hp).
    destruct a as [e|q x], b as [e'|q' x']; cbn; try exact I.
    - destruct (read_shape c' k q' x' RO Hb) as (-> & Hpub & Hprov).
      pose proof (proj1 (hprog_tagged c k _ Ha)) as Ht; cbn in Ht.
      split; [exact Hpub|]; rewrite Ht; intros ->; exact (Hprov (Hp eq_refl)).
    - destruct (read_shape c k q x RO Ha) as (-> & Hpub & Hprov).
      pose proof (proj1 (hprog_tagged c' k _ Hb)) as Ht; cbn in Ht.
      split; [exact Hpub|]; rewrite Ht; intros E; exact (Hprov (Hp (eq_sym E))).
  Qed.

  Theorem hyg_covers_rev : ReadsOwn -> ContribSingle -> Covers CS hprog hyg_rev.
  Proof.
    intros RO CSg k a b Hcp.
    pose proof (hyg_covers RO k a b Hcp) as Hm.
    destruct Hcp as (c & c' & Ha & Hb & Hp).
    destruct a as [e|q x], b as [e'|q' x']; cbn in Hm |- *; try exact Hm.
    intros ->.
    destruct (hprog_tagged c k _ Ha) as [Ht (a0 & Ha0 & Ea0)].
    destruct (hprog_tagged c' k _ Hb) as [Ht' _]; cbn in Ht, Ht'.
    assert (c = c') by congruence; subst c'.
    destruct a0 as [e0|q0 y0]; [|cbn in Ea0; discriminate].
    exact (CSg c k e0 Ha0 (Hp (eq_sym Ht))).
  Qed.

  (** ** The summary theorem for the tagged table *)
  Local Notation agree_resolve :=
    (agree_resolve C Name V C_eq_dec name_eq_dec v_eq_dec public prio).

  Theorem hyg_confluence Kb rank Rb ins (γ1 γ2 : @State K CS C) rs1 rs2 :
    ReadsOwn -> Obligations CS hprog Kb rank Rb -> TotalProv CS hprog ->
    DRun K_eq_dec CS hprog (@init K CS C) [] ins γ1 rs1 ->
    DRun K_eq_dec CS hprog (@init K CS C) [] ins γ2 rs2 ->
    quiet K_eq_dec CS hprog γ1 -> quiet K_eq_dec CS hprog γ2 -> NoFailed CS γ1 -> NoFailed CS γ2 ->
    forall k b1 b2, binds CS γ1 k = Some b1 -> binds CS γ2 k = Some b2 ->
      forall q x, resolve (bst CS b1) q x = resolve (bst CS b2) q x.
  Proof.
    intros RO HO HT R1 R2 Q1 Q2 N1 N2.
    exact (agree_resolve _ _ γ1 γ2
             (summary_confluence K_eq_dec CS hprog hyg_meet Kb rank Rb ins γ1 γ2 rs1 rs2
                hyg_hyps (hyg_covers RO) HO HT R1 R2 Q1 Q2 N1 N2)).
  Qed.

  Theorem hyg_static Kb rank Rb ins (γ γs : @State K CS C) rs rss :
    ReadsOwn -> Obligations CS hprog Kb rank Rb -> TotalProv CS hprog ->
    DRun K_eq_dec CS hprog (@init K CS C) [] ins γ rs ->
    DRun K_eq_dec CS hprog (@init K CS C) [] (map IIns (scomps ins)) γs rss ->
    quiet K_eq_dec CS hprog γ -> quiet K_eq_dec CS hprog γs -> NoFailed CS γ -> NoFailed CS γs ->
    forall k b bs, binds CS γ k = Some b -> binds CS γs k = Some bs ->
      forall q x, resolve (bst CS b) q x = resolve (bst CS bs) q x.
  Proof.
    intros RO HO HT R1 R2 Q1 Q2 N1 N2.
    exact (agree_resolve _ _ γ γs
             (summary_static K_eq_dec CS hprog hyg_meet Kb rank Rb ins γ γs rs rss
                hyg_hyps (hyg_covers RO) HO HT R1 R2 Q1 Q2 N1 N2)).
  Qed.

  Theorem hyg_recovery n ls (γ : @State K CS C) σ :
    ReadsOwn -> ContribSingle ->
    shadow_run K_eq_dec CS hprog n (@init K CS C) ls (fun _ => None) = Some (γ, σ) ->
    match fibers CS γ n with Some f => is_installed CS (life CS f) = false | None => True end ->
    forall k, match binds CS γ k, σ k with
              | Some b, Some s => forall q x, resolve (bst CS b) q x = resolve s q x
              | None, None => True
              | _, _ => False
              end.
  Proof.
    intros RO CSg HS Hn k.
    pose proof (summary_recovery K_eq_dec CS hprog hyg_rev n ls γ σ
                  hyg_revertible (hyg_covers_rev RO CSg) HS Hn k) as H.
    destruct (binds CS γ k), (σ k); try exact H.
    intros q x; apply resolve_perm; exact H.
  Qed.
End Hygiene.
