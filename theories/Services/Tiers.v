(** * The two tiers of the service specification, on three services

    The summary theorem ([Summary.v]) asks of a service, relative to a
    relation [G] on operations, one of two tiers: revertible
    ([Revertible]) or confluent ([ConfHyps]). Neither implies the other.

    1. Registry ([Registry.v]). With [reg_tier] (registrations of distinct
       names, a registration and a lookup of distinct names, any two
       lookups) it meets both tiers: [registry_revertible],
       [registry_confluent]. Two registrations of one name are not
       revert-independent ([Registry.register_same_not_indep]).
    2. Listener registration ([Listeners.v]). Relating every pair, it is
       confluent ([listeners_hyps]) but not revertible
       ([listeners_not_revertible]). Relating registrations of distinct
       callbacks, it meets both tiers: [listeners_revertible],
       [listeners_confluent].
    3. A variable store, where setting x to v is undone by restoring x's
       old value. Relating operations on distinct variables it is
       revertible ([store_revertible]); its inverse depends on the state,
       so it is confluent for no relation ([store_not_confluent]). *)

From Stdlib Require Import RelationClasses List Permutation.
From Cordis Require Import Prelude Service ServiceSeq Compose Summary.
From Cordis Require Registry RegistryConf Listeners.
Import ListNotations.

(** ** Generic facts *)

(** The confluent tier only gets easier as [G] shrinks. *)
Lemma confhyps_mono (Σ : Service) (G1 G2 : Op Σ -> Op Σ -> Prop) :
  (forall a b, G1 a b -> G2 a b) -> ConfHyps Σ G2 -> ConfHyps Σ G1.
Proof.
  intros Hsub H; split.
  - exact (ch_wb _ _ H).
  - exact (ch_ui _ _ H).
  - exact (ch_ti _ _ H).
  - intros a b ta tb g Gab Ht Hy x Hx.
    exact (ch_ri _ _ H a b ta tb g (Hsub a b Gab) Ht Hy x
             (after_mono _ _ (fun b' => Hsub a b') a ta x Hx)).
  - intros a b ta tb Gab Ht; exact (ch_com _ _ H a b ta tb (Hsub a b Gab) Ht).
Qed.

(** ** 1. The registry *)
Section RegistryTiers.
  Context (Name V : Type).
  Context (name_eq_dec : forall x y : Name, {x = y} + {x <> y}).

  Local Notation Reg := (Registry.Registry Name V name_eq_dec).
  Local Notation Register := (Registry.Register Name V).
  Local Notation Lookup := (Registry.Lookup Name V).

  Definition reg_tier (a b : Registry.ROp Name V) : Prop :=
    match a, b with
    | Registry.Register _ _ x _, Registry.Register _ _ y _ => x <> y
    | Registry.Register _ _ x _, Registry.Lookup _ _ y => x <> y
    | Registry.Lookup _ _ x, Registry.Register _ _ y _ => x <> y
    | Registry.Lookup _ _ _, Registry.Lookup _ _ _ => True
    end.

  Lemma lookup_yields x t g : yields (Σ := Reg) (Lookup x) t g -> g = fun s => s.
  Proof. intros (s & s' & o & H); cbn in H; injection H as _ <- _; reflexivity. Qed.

  (** A lookup comes first: its inverse is the identity. *)
  Lemma lookup_revert_indep x b t1 t2 : RevertIndep (Σ := Reg) (Lookup x) t1 b t2.
  Proof.
    intros g Hg; apply lookup_yields in Hg; subst g; split.
    - intros s; destruct (@run Reg b t2 s) as [[[s1 h] o]|]; cbn; [|exact I].
      split; [intros z; reflexivity | split; [intros y z; reflexivity | reflexivity]].
    - intros h s _ z; reflexivity.
  Qed.

  Theorem registry_revertible : Revertible Reg reg_tier.
  Proof.
    split; [exact (Registry.registry_well_behaved Name V name_eq_dec)|].
    intros [x v|x] [y w|y] ta tb G _; cbn in G.
    - exact (Registry.register_revert_indep Name V name_eq_dec x v y w ta tb G).
    - exact (Registry.register_lookup_indep Name V name_eq_dec x v y ta tb G).
    - apply lookup_revert_indep.
    - apply lookup_revert_indep.
  Qed.

  Theorem registry_confluent : ConfHyps Reg reg_tier.
  Proof.
    apply (confhyps_mono Reg _ (RegistryConf.reg_meet Name V)).
    - intros [x v|x] [y w|y]; cbn; auto.
    - exact (RegistryConf.registry_hyps Name V name_eq_dec).
  Qed.
End RegistryTiers.

(** ** 2. Listener registration *)
Section ListenerTiers.
  Context (Cb : Type).
  Context (cb_eq_dec : forall x y : Cb, {x = y} + {x <> y}).

  Local Notation L := (Listeners.Listeners Cb cb_eq_dec).
  Local Notation rf := (Listeners.remove_first Cb cb_eq_dec).
  Local Notation cb_of := (Listeners.cb_of Cb).

  Lemma l_yields a t g : yields (Σ := L) a t g -> g = rf (cb_of a).
  Proof. intros (s & s' & o & H); destruct a; cbn in H; injection H as _ <- _; reflexivity. Qed.

  (** Relating every pair, listener registration is not revertible: two
      fibers register the same callback, absent from the list. *)
  Theorem listeners_not_revertible (c : Cb) :
    ~ Revertible L (fun _ _ => True).
  Proof.
    intros [_ HRI].
    assert (Hy : yields (Σ := L) (Listeners.LOn Cb c) 0 (rf c)).
    { exists [], [c], tt; reflexivity. }
    destruct (HRI (Listeners.LOn Cb c) (Listeners.LOn Cb c) 0 1 I ltac:(discriminate) _ Hy)
      as [H _].
    specialize (H []); cbn in H.
    destruct H as [P _]; revert P; cbn.
    destruct (cb_eq_dec c c) as [_|Hc]; [|contradiction].
    intros P; exact (Permutation_nil_cons (Permutation_sym P)).
  Qed.

  Lemma rf_app_other ca cb x : ca <> cb -> rf ca (x ++ [cb]) = rf ca x ++ [cb].
  Proof.
    intros Hne; induction x as [|y x IH]; cbn.
    - destruct (cb_eq_dec cb ca); [congruence | reflexivity].
    - destruct (cb_eq_dec y ca); [reflexivity | cbn; f_equal; exact IH].
  Qed.

  Lemma rf_cons_other ca cb x : ca <> cb -> rf ca (cb :: x) = cb :: rf ca x.
  Proof. intros Hne; cbn; destruct (cb_eq_dec cb ca); [congruence | reflexivity]. Qed.

  Lemma rf_comm ca cb x : ca <> cb -> rf ca (rf cb x) = rf cb (rf ca x).
  Proof.
    intros Hne; induction x as [|y x IH]; cbn; [reflexivity|].
    repeat (cbn; match goal with |- context [cb_eq_dec ?u ?v] =>
                   destruct (cb_eq_dec u v); try congruence end).
  Qed.

  Definition cb_tier (a b : Listeners.LOp Cb) : Prop := cb_of a <> cb_of b.

  Theorem listeners_revertible : Revertible L cb_tier.
  Proof.
    split; [exact (Listeners.listeners_well_behaved Cb cb_eq_dec)|].
    intros a b ta tb Hne _ g Hg; apply l_yields in Hg; subst g; unfold cb_tier in Hne; split.
    - intros x; destruct b as [cb|cb]; cbn in Hne |- *;
        (split; [|split; [intros y; reflexivity | reflexivity]]).
      + rewrite (rf_app_other _ _ x Hne); reflexivity.
      + destruct (cb_eq_dec cb (cb_of a)); [congruence | reflexivity].
    - intros h x Hh; apply l_yields in Hh; subst h; cbn.
      rewrite (rf_comm _ _ x Hne); reflexivity.
  Qed.

  Theorem listeners_confluent : ConfHyps L cb_tier.
  Proof.
    apply (confhyps_mono L _ (fun _ _ => True)); [auto|].
    exact (Listeners.listeners_hyps Cb cb_eq_dec).
  Qed.
End ListenerTiers.

(** ** 3. A variable store *)
Section StoreTiers.
  Context (Var Val : Type).
  Context (var_eq_dec : forall x y : Var, {x = y} + {x <> y}).

  Definition VSt : Type := Var -> Val.
  Definition veq (s1 s2 : VSt) : Prop := forall x, s1 x = s2 x.

  #[local] Instance veq_equiv : Equivalence veq.
  Proof.
    split.
    - intros s x; reflexivity.
    - intros s1 s2 H x; symmetry; apply H.
    - intros s1 s2 s3 H1 H2 x; rewrite H1; apply H2.
  Qed.

  Inductive VOp : Type := SetVar (x : Var) (v : Val).

  Definition vupd (s : VSt) (x : Var) (v : Val) : VSt :=
    fun y => if var_eq_dec y x then v else s y.

  (** Setting x to v; the inverse restores x's old value. *)
  Definition vrun (a : VOp) (_ : Tok) (s : VSt) : option (VSt * (VSt -> VSt) * unit) :=
    match a with SetVar x v => Some (vupd s x v, fun s' => vupd s' x (s x), tt) end.

  Definition VStore : Service := {|
    St := VSt; st_eq := veq; st_eq_equiv := veq_equiv;
    Op := VOp; Out := unit; run := vrun
  |}.

  Definition var_of (a : VOp) : Var := match a with SetVar x _ => x end.
  Definition var_tier (a b : VOp) : Prop := var_of a <> var_of b.

  Lemma v_yields x v t g : yields (Σ := VStore) (SetVar x v) t g ->
    exists u, g = fun s' => vupd s' x u.
  Proof. intros (s & s' & o & H); cbn in H; injection H as _ <- _; eexists; reflexivity. Qed.

  Theorem store_well_behaved a t : WellBehaved (Σ := VStore) a t.
  Proof.
    destruct a as [x v]; split.
    - intros s s' g o; cbn; intros [= <- <- _] y; unfold vupd.
      destruct (var_eq_dec y x) as [->|]; reflexivity.
    - intros s1 s2 E; cbn.
      split; [|split; [|reflexivity]].
      + intros y; unfold vupd; destruct (var_eq_dec y x); [reflexivity | apply E].
      + intros s' y; unfold vupd; destruct (var_eq_dec y x); [apply E | reflexivity].
    - intros s s' g o; cbn; intros [= _ <- _] s1 s2 E y; unfold vupd.
      destruct (var_eq_dec y x); [reflexivity | apply E].
  Qed.

  Theorem store_revertible : Revertible VStore var_tier.
  Proof.
    split; [exact store_well_behaved|].
    intros [x v] [y w] ta tb Hne _ g Hg; unfold var_tier in Hne; cbn in Hne.
    destruct (v_yields x v ta g Hg) as [u ->]; split.
    - intros s; cbn; split; [|split; [|reflexivity]].
      + intros z; unfold vupd.
        repeat (match goal with |- context [var_eq_dec ?u ?v] => destruct (var_eq_dec u v) end); congruence.
      + intros s' z; unfold vupd.
        repeat (match goal with |- context [var_eq_dec ?u ?v] => destruct (var_eq_dec u v) end); congruence.
    - intros h s Hh; destruct (v_yields y w tb h Hh) as [u' ->]; intros z; cbn; unfold vupd.
      repeat (match goal with |- context [var_eq_dec ?u ?v] => destruct (var_eq_dec u v) end); congruence.
  Qed.

  (** The inverse depends on the state, so the confluent tier fails for
      every relation. *)
  Theorem store_not_confluent (x : Var) (v0 v1 : Val) :
    v0 <> v1 -> forall G, ~ ConfHyps VStore G.
  Proof.
    intros Hv G H.
    pose proof (ch_ui _ _ H (SetVar x v0) 0 (fun _ => v0) (fun _ => v1)
                  _ _ _ _ tt tt eq_refl eq_refl) as E.
    specialize (E (fun _ => v0) x); cbn in E; unfold vupd in E.
    destruct (var_eq_dec x x); [exact (Hv E) | contradiction].
  Qed.
End StoreTiers.
