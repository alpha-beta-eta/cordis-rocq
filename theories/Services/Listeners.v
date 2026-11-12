(** * Listener registration, up to order

    Cordis' event bus as the startup phase sees it: plugins register
    callbacks ([ctx.on] appends, [Prepend] puts the hook first), and a
    registration's inverse is Cordis' [unregister] today: remove the first
    hook whose callback is [cb] (events.ts, [hooks.findIndex(hook =>
    hook.callback === callback)]).

    States are lists of callbacks, related by [Permutation]: two lists of
    hooks are equivalent when they register the same callbacks, in any order.

    - Under this equivalence, unregistering by callback is an exact inverse
      ([listeners_well_behaved]). Removing a different hook with the same
      callback only changes the order, which ≃ ignores. So the defect in
      [EventBus.on_by_callback_not_witnessed] is a defect of order alone.
    - Dispatch is left out: its result is the ordered list of callbacks,
      which no order-blind equivalence respects. A startup program that
      reads dispatch results is outside this model, and with it, outside
      the confluence theorem; [EventBus.on_not_commute] shows why.
    - [listeners_confluence]: the confluence theorem holds for this
      service, so two schedules leave every event key with the same
      multiset of listeners. *)

From Stdlib Require Import RelationClasses List PeanoNat Permutation.
From Cordis Require Import Prelude Service ServiceSeq Calculus Termination Progress Confluence StateInv Episode StateConf SpawnConf Compose.
Import ListNotations.

Section Listeners.
  Context (Cb : Type).
  Context (cb_eq_dec : forall x y : Cb, {x = y} + {x <> y}).

  Inductive LOp : Type := LOn (cb : Cb) | LPrepend (cb : Cb).

  Definition cb_of (a : LOp) : Cb := match a with LOn cb | LPrepend cb => cb end.

  Fixpoint remove_first (cb : Cb) (s : list Cb) : list Cb :=
    match s with
    | [] => []
    | x :: s' => if cb_eq_dec x cb then s' else x :: remove_first cb s'
    end.

  Definition lrun (a : LOp) (t : Tok) (s : list Cb) : option (list Cb * (list Cb -> list Cb) * unit) :=
    match a with
    | LOn cb => Some (s ++ [cb], remove_first cb, tt)
    | LPrepend cb => Some (cb :: s, remove_first cb, tt)
    end.

  Definition Listeners : Service := {|
    St := list Cb; st_eq := @Permutation Cb; st_eq_equiv := Permutation_Equivalence Cb;
    Op := LOp; Out := unit; run := lrun
  |}.

  (** ** Removing the first occurrence *)
  Lemma rf_perm cb s : In cb s -> Permutation s (cb :: remove_first cb s).
  Proof.
    induction s as [|x s IH]; cbn; [intros []|].
    destruct (cb_eq_dec x cb) as [->|Hne]; [reflexivity|].
    intros [E|Hin]; [congruence|].
    transitivity (x :: cb :: remove_first cb s); [apply perm_skip, IH, Hin | apply perm_swap].
  Qed.

  Lemma rf_head cb s : remove_first cb (cb :: s) = s.
  Proof. cbn; destruct (cb_eq_dec cb cb); [reflexivity | contradiction]. Qed.

  Lemma rf_notin cb s : ~ In cb s -> remove_first cb s = s.
  Proof.
    induction s as [|x s IH]; cbn; [reflexivity|]; intros H.
    destruct (cb_eq_dec x cb) as [->|_]; [exfalso; apply H; left; reflexivity|].
    f_equal; apply IH; intros Hin; apply H; right; exact Hin.
  Qed.

  Lemma rf_respects cb s1 s2 :
    Permutation s1 s2 -> Permutation (remove_first cb s1) (remove_first cb s2).
  Proof.
    intros P.
    destruct (in_dec cb_eq_dec cb s1) as [H1|H1].
    - pose proof (Permutation_in _ P H1) as H2.
      apply (Permutation_cons_inv (a := cb)).
      transitivity s1; [symmetry; exact (rf_perm cb s1 H1)|].
      transitivity s2; [exact P | exact (rf_perm cb s2 H2)].
    - assert (H2 : ~ In cb s2) by (intros H; apply H1; exact (Permutation_in _ (Permutation_sym P) H)).
      rewrite (rf_notin cb s1 H1), (rf_notin cb s2 H2); exact P.
  Qed.

  Lemma rf_app_in cb x l : In cb x -> remove_first cb (x ++ l) = remove_first cb x ++ l.
  Proof.
    induction x as [|y x IH]; cbn; [intros []|].
    destruct (cb_eq_dec y cb) as [->|Hne]; [reflexivity|].
    intros [E|Hin]; [congruence | cbn; f_equal; exact (IH Hin)].
  Qed.

  Lemma rf_cons_in cb c x : In cb x -> Permutation (remove_first cb (c :: x)) (c :: remove_first cb x).
  Proof.
    intros Hin; cbn; destruct (cb_eq_dec c cb) as [->|_]; [exact (rf_perm cb x Hin) | reflexivity].
  Qed.

  (** ** The service hypotheses *)
  Theorem listeners_well_behaved a t : WellBehaved (Σ := Listeners) a t.
  Proof.
    split.
    - intros s s' g o; destruct a as [cb|cb]; cbn; intros [= <- <- _].
      + transitivity (remove_first cb (cb :: s)).
        * apply rf_respects; symmetry; apply Permutation_cons_append.
        * rewrite rf_head; reflexivity.
      + rewrite rf_head; reflexivity.
    - intros s1 s2 P; destruct a as [cb|cb]; cbn.
      + split; [apply Permutation_app_tail; exact P | split; [intros x; reflexivity | reflexivity]].
      + split; [apply perm_skip; exact P | split; [intros x; reflexivity | reflexivity]].
    - intros s s' g o; destruct a as [cb|cb]; cbn; intros [= _ <- _] x y P; exact (rf_respects cb x y P).
  Qed.

  Lemma listeners_inverse_uniform (a : LOp) (t : nat) (s1 s2 s1' s2' : list Cb)
      (g1 g2 : list Cb -> list Cb) (o1 o2 : unit) :
    @run Listeners a t s1 = Some (s1', g1, o1) -> @run Listeners a t s2 = Some (s2', g2, o2) ->
    fun_eq (Σ := Listeners) g1 g2.
  Proof. destruct a; cbn; intros [= _ <- _] [= _ <- _] x; reflexivity. Qed.

  Lemma listeners_token_irrelevant (a : LOp) (t t' : nat) (s : list Cb) :
    match @run Listeners a t s, @run Listeners a t' s with
    | None, None => True
    | Some (s1, _, o1), Some (s2, _, o2) => @st_eq Listeners s1 s2 /\ o1 = o2
    | _, _ => False
    end.
  Proof. destruct a; cbn; split; reflexivity. Qed.

  Lemma listeners_commute a ta b tb : Commute (Σ := Listeners) a ta b tb.
  Proof.
    intros s; destruct a as [x|x], b as [y|y]; cbn; (split; [|split; reflexivity]).
    - rewrite <- !app_assoc; apply Permutation_app_head; apply perm_swap.
    - reflexivity.
    - reflexivity.
    - apply perm_swap.
  Qed.

  (** Registrations only add hooks: after [a], its callback stays. *)
  Lemma after_in (Good : LOp -> Prop) a ta x : After (Σ := Listeners) Good a ta x -> In (cb_of a) x.
  Proof.
    intros H; induction H as [x x' g o Hr|w b tb w' h o Hw IH Gb Ht Hr].
    - destruct a as [cb|cb]; cbn in Hr; injection Hr as <- _ _; cbn;
        [apply in_or_app; right; left; reflexivity | left; reflexivity].
    - destruct b as [cb|cb]; cbn in Hr; injection Hr as <- _ _;
        [apply in_or_app; left; exact IH | right; exact IH].
  Qed.

  Lemma listeners_revert_after (Good : LOp -> Prop) a b ta tb g :
    yields (Σ := Listeners) a ta g ->
    forall x, After (Σ := Listeners) Good a ta x ->
      shifted (Σ := Listeners) g (@run Listeners b tb x) (@run Listeners b tb (g x)).
  Proof.
    intros (z & z' & oz & Hz) x Hx.
    assert (Eg : g = remove_first (cb_of a)) by (destruct a; cbn in Hz; injection Hz as _ <- _; reflexivity).
    subst g; pose proof (after_in Good a ta x Hx) as Hin.
    destruct b as [cb|cb]; cbn; (split; [|split; [intros y; reflexivity | reflexivity]]).
    - rewrite (rf_app_in _ x [cb] Hin); reflexivity.
    - symmetry; exact (rf_cons_in _ cb x Hin).
  Qed.

  Theorem listeners_hyps : ConfHyps Listeners (fun _ _ => True).
  Proof.
    split.
    - exact listeners_well_behaved.
    - exact listeners_inverse_uniform.
    - exact listeners_token_irrelevant.
    - intros a b ta tb g _ _ Hy x Hx.
      exact (shifted_ok_of _ _ _ (listeners_revert_after _ a b ta tb g Hy x Hx)).
    - intros a b ta tb _ _; exact (listeners_commute a ta b tb).
  Qed.

  (** ** Confluence for listener registration *)
  Section Conf.
    Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
    Context {C : Type} (prog : C -> @Component K Listeners C).
    Variable Kb : nat.
    Hypothesis HK : forall c, Bounded Listeners Kb (body Listeners (prog c)).
    Variable rank : C -> nat.
    Variable Rb : nat.
    Hypothesis Hrank : forall c c', Above Listeners prog c c' -> rank c < rank c'.
    Hypothesis Hbnd : forall c, rank c <= Rb.
    Hypothesis Total : forall c k, In k (provs Listeners (prog c)) ->
      AllDoneProv Listeners k (body Listeners (prog c)).

    (** Two schedules that end quiet with no failure leave each key with the
        same callbacks, as a multiset. The rest of [spawn_confluence]
        (canonical names, components, activity, owners) holds as well. *)
    Theorem listeners_confluence (γ0 γ1 γ2 : State Listeners) :
      PInv K_eq_dec Listeners prog Kb γ0 -> SLInv Listeners γ0 ->
      LRun K_eq_dec Listeners prog γ0 γ1 -> LRun K_eq_dec Listeners prog γ0 γ2 ->
      quiet K_eq_dec Listeners prog γ1 -> quiet K_eq_dec Listeners prog γ2 ->
      NoFailed Listeners γ1 -> NoFailed Listeners γ2 ->
      forall k b1 b2, binds Listeners γ1 k = Some b1 -> binds Listeners γ2 k = Some b2 ->
        Permutation (bst Listeners b1) (bst Listeners b2).
    Proof.
      intros P0 S0 R1 R2 Q1 Q2 NF1 NF2.
      exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
        (spawn_confluence K_eq_dec Listeners prog Kb HK rank Rb Hrank Hbnd Total
           listeners_well_behaved listeners_inverse_uniform listeners_token_irrelevant
           (fun k a b ta tb g _ _ Hy x Hx => shifted_ok_of _ _ _ (listeners_revert_after _ a b ta tb g Hy x Hx))
           (fun k a b ta tb _ _ => listeners_commute a ta b tb)
           γ0 γ1 γ2 P0 S0 R1 R2 Q1 Q2 NF1 NF2))))))))).
    Qed.
  End Conf.
End Listeners.
