(** * Derived forms (DESIGN.md, items d and n)

    Two Cordis features need no rule of their own.

    - Isolation ([ctx.isolate(name, label)], item n). A key is a service
      name with a scope label; a context's scope gives each name its label.
      An isolated subtree is a component table whose keys carry another
      label, so isolation is a transformation of the table ([scoped]), and
      every theorem stated for an arbitrary table applies to it. This file
      shows that the transformation keeps each component-level hypothesis
      those theorems ask for: bounded programs, total provision, the rank
      order, and independence (in the form [CoPairAny], see below).

    - The availability check ([provide(name, value, check)], item d).
      Evaluated when the value is provided, it is a test the program can
      make itself, since the program knows the value it provides:
      [provide_checked]. *)

From Stdlib Require Import List.
From Cordis Require Import Prelude Service Calculus Recovery Progress Termination Confluence.
Import ListNotations.

(** ** Isolation *)
Section Isolate.
  Context (Σ : Service) {N L C : Type}.

  (** A scope labels each name. *)
  Definition Scope : Type := N -> L.
  Definition key (ι : Scope) (n : N) : N * L := (n, ι n).

  (** [enter c ι]: the scope a spawned [c] runs in, under a parent in scope
      [ι]. A plain spawn keeps [ι]; [ctx.isolate(name, l).plugin(c)] changes
      the label of [name] to [l]. *)
  Variable enter : C -> Scope -> Scope.
  Variable prog : C -> @Component N Σ C.

  Fixpoint ren (ι : Scope) (P : @Prog N Σ C) : @Prog (N * L) Σ (Scope * C) :=
    match P with
    | PDone => PDone
    | PFail => PFail
    | POp k a κ => POp (key ι k) a (fun o => ren ι (κ o))
    | PProvide k s Q => PProvide (key ι k) s (ren ι Q)
    | PSpawn c Q => PSpawn (enter c ι, c) (ren ι Q)
    end.

  (** The table of components in scopes. *)
  Definition scoped (x : Scope * C) : @Component (N * L) Σ (Scope * C) :=
    mkComponent (map (key (fst x)) (deps Σ (prog (snd x))))
                (map (key (fst x)) (provs Σ (prog (snd x))))
                (ren (fst x) (body Σ (prog (snd x))))
                (map (fun c' => (enter c' (fst x), c')) (reacts Σ (prog (snd x)))).

  Lemma key_inj ι ι' n n' : key ι n = key ι' n' -> n = n'.
  Proof. unfold key; intros [= E _]; exact E. Qed.

  (** Scopes that label a name differently keep its keys apart. *)
  Lemma key_sep ι ι' n : ι n <> ι' n -> key ι n <> key ι' n.
  Proof. unfold key; intros H [= E]; exact (H E). Qed.

  Lemma ren_bounded ι j P : Bounded Σ j P -> Bounded Σ j (ren ι P).
  Proof. intros H; induction H; cbn; constructor; auto. Qed.

  Lemma ren_total ι k P : AllDoneProv Σ k P -> AllDoneProv Σ (key ι k) (ren ι P).
  Proof.
    intros H; induction H; cbn.
    - apply adp_fail.
    - apply adp_op; auto.
    - apply adp_here.
    - apply adp_prov; auto.
    - apply adp_spawn; auto.
  Qed.

  Lemma ren_spawn ι x P : SpawnIn Σ x (ren ι P) -> SpawnIn Σ (snd x) P.
  Proof.
    induction P as [| |k a κ IH|k s Q IH|c Q IH]; cbn; intros H; inversion H; subst.
    - eapply spi_op; eauto.
    - apply spi_prov; auto.
    - apply spi_here.
    - apply spi_spawn; auto.
  Qed.

  Lemma ren_opat ι k a P : OpAt Σ k a (ren ι P) -> exists n, k = key ι n /\ OpAt Σ n a P.
  Proof.
    induction P as [| |k' b κ IH|k' s Q IH|c Q IH]; cbn; intros H; inversion H; subst.
    - exists k'; split; [reflexivity | apply at_here].
    - match goal with Hx : OpAt _ _ _ (ren _ (κ ?o)) |- _ =>
        destruct (IH o Hx) as (n & -> & Hn); exists n; split; [reflexivity | eapply at_cont; eauto] end.
    - match goal with Hx : OpAt _ _ _ (ren _ Q) |- _ =>
        destruct (IH Hx) as (n & -> & Hn); exists n; split; [reflexivity | apply at_prov; auto] end.
    - match goal with Hx : OpAt _ _ _ (ren _ Q) |- _ =>
        destruct (IH Hx) as (n & -> & Hn); exists n; split; [reflexivity | apply at_spawn; auto] end.
  Qed.

  (** *** The hypotheses carry over *)
  Theorem scoped_bounded Kb :
    (forall c, Bounded Σ Kb (body Σ (prog c))) -> forall x, Bounded Σ Kb (body Σ (scoped x)).
  Proof. intros H x; apply ren_bounded, H. Qed.

  Theorem scoped_total :
    (forall c k, In k (provs Σ (prog c)) -> AllDoneProv Σ k (body Σ (prog c))) ->
    forall x k, In k (provs Σ (scoped x)) -> AllDoneProv Σ k (body Σ (scoped x)).
  Proof.
    intros H x k Hk; cbn in Hk |- *; apply in_map_iff in Hk as (n & <- & Hn).
    apply ren_total, H, Hn.
  Qed.

  Theorem scoped_above x y : Above Σ scoped x y -> Above Σ prog (snd x) (snd y).
  Proof.
    intros [(k & Hp & Hd)|[Hs|Hr]]; cbn in *.
    - apply in_map_iff in Hp as (n & <- & Hn); apply in_map_iff in Hd as (n' & E & Hn').
      apply key_inj in E; subst n'; left; exists n; auto.
    - right; left; exact (ren_spawn _ _ _ Hs).
    - right; right; apply in_map_iff in Hr as (c' & <- & Hc); exact Hc.
  Qed.

  (** A rank for the base table ranks the scoped table. *)
  Corollary scoped_rank (rank : C -> nat) :
    (forall c c', Above Σ prog c c' -> rank c < rank c') ->
    forall x y, Above Σ scoped x y -> rank (snd x) < rank (snd y).
  Proof. intros H x y A; apply H, scoped_above, A. Qed.

  Theorem scoped_nospawn :
    (forall c c', ~ SpawnIn Σ c' (body Σ (prog c))) ->
    forall x y, ~ SpawnIn Σ y (body Σ (scoped x)).
  Proof. intros H x y Hs; exact (H _ _ (ren_spawn _ _ _ Hs)). Qed.

  (** Two operations at one name, by any two components. Isolation lets one
      component run in several scopes at once, so [CoPair]'s exemption for a
      component that provides a key does not carry over: two copies of it
      may each operate on their own provision, which is a key of their own
      only when their scopes label the name differently. *)
  Definition CoPairAny (n : N) (a b : Op Σ) : Prop :=
    exists c c', OpAt Σ n a (body Σ (prog c)) /\ OpAt Σ n b (body Σ (prog c')).

  Theorem scoped_copair k a b : CoPair Σ scoped k a b -> CoPairAny (fst k) a b.
  Proof.
    intros (x & y & Ha & Hb & _); cbn in Ha, Hb.
    apply ren_opat in Ha as (n & -> & Ha); apply ren_opat in Hb as (n' & E & Hb).
    apply key_inj in E; subst n'; exists (snd x), (snd y); auto.
  Qed.

  Corollary scoped_ind :
    (forall n a b ta tb, CoPairAny n a b -> ta <> tb -> RevertIndep (Σ := Σ) a ta b tb) ->
    forall k a b ta tb, CoPair Σ scoped k a b -> ta <> tb -> RevertIndep (Σ := Σ) a ta b tb.
  Proof. intros H k a b ta tb Hc; apply (H (fst k)), scoped_copair, Hc. Qed.
End Isolate.

(** ** The availability check *)
Section Check.
  Context {K : Type} (Σ : Service) {C : Type}.

  (** Provide [s] at [k] when [chk s] holds; otherwise go on without it.
      Cordis consults the check whenever dependents are notified, against
      the current value; see DESIGN.md, item d. *)
  Definition provide_checked (chk : St Σ -> bool) (k : K) (s : St Σ) (P : @Prog K Σ C)
    : @Prog K Σ C :=
    if chk s then PProvide k s P else P.

  Lemma bounded_succ j (P : @Prog K Σ C) : Bounded Σ j P -> Bounded Σ (S j) P.
  Proof. intros H; induction H; constructor; auto. Qed.

  Lemma checked_bounded chk k s j P :
    Bounded Σ j P -> Bounded Σ (S j) (provide_checked chk k s P).
  Proof.
    intros H; unfold provide_checked; destruct (chk s);
      [constructor; exact H | apply bounded_succ, H].
  Qed.

  (** Total provision holds on the path where the check passes; where it
      fails, [P] must provide [k] or fail. *)
  Lemma checked_total chk k s P :
    (chk s = false -> AllDoneProv Σ k P) -> AllDoneProv Σ k (provide_checked chk k s P).
  Proof.
    unfold provide_checked; destruct (chk s); intros H; [apply adp_here | apply H; reflexivity].
  Qed.
End Check.
