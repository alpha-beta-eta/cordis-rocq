(** * An ordered event bus (e.g. [ctx.on])

    The state is the ordered list of hooks; a hook is a callback tagged with
    the token the runtime handed to its registration, which gives it an
    identity. States are compared by equality: the order is observable,
    since dispatch ([Emit]) returns the callbacks in order.

    - [On cb] appends a hook, [Prepend cb] prepends one (Cordis' [push] and
      [unshift]); each fails if its token is already in use, and its inverse
      removes the hook carrying that token.
    - [Emit] reads the callbacks in order.
    - [OnByCallback cb] appends like [On], but its inverse removes the first
      hook whose callback is [cb], which is how Cordis' [unregister] works
      today (events.ts, [hooks.findIndex(hook => hook.callback === callback)]). *)

From Stdlib Require Import RelationClasses List PeanoNat Bool.
From Cordis Require Import Prelude Service.
Import ListNotations.

Section EventBus.
  Context (Cb : Type).
  Context (cb_eq_dec : forall x y : Cb, {x = y} + {x <> y}).

  Definition Hook : Type := (Tok * Cb)%type.
  Definition ESt : Type := list Hook.

  Inductive EOp : Type :=
  | On (cb : Cb)
  | Prepend (cb : Cb)
  | Emit
  | OnByCallback (cb : Cb).

  Definition mem (t : Tok) (s : ESt) : bool := existsb (fun h => Nat.eqb (fst h) t) s.

  Definition remove_tok (t : Tok) (s : ESt) : ESt :=
    filter (fun h => negb (Nat.eqb (fst h) t)) s.

  Fixpoint remove_first_cb (cb : Cb) (s : ESt) : ESt :=
    match s with
    | [] => []
    | h :: s' => if cb_eq_dec (snd h) cb then s' else h :: remove_first_cb cb s'
    end.

  Definition erun (a : EOp) (t : Tok) (s : ESt)
    : option (ESt * (ESt -> ESt) * list Cb) :=
    match a with
    | On cb => if mem t s then None else Some (s ++ [(t, cb)], remove_tok t, [])
    | Prepend cb => if mem t s then None else Some ((t, cb) :: s, remove_tok t, [])
    | Emit => Some (s, id, map snd s)
    | OnByCallback cb =>
        if mem t s then None else Some (s ++ [(t, cb)], remove_first_cb cb, [])
    end.

  Definition EventBus : Service := {|
    St := ESt; st_eq := eq; st_eq_equiv := eq_equivalence;
    Op := EOp; Out := list Cb; run := erun
  |}.

  (** ** List lemmas *)
  Lemma filter_comm {A : Type} (f g : A -> bool) (l : list A) :
    filter f (filter g l) = filter g (filter f l).
  Proof.
    induction l as [|x l IH]; cbn; [reflexivity|].
    destruct (g x) eqn:Eg, (f x) eqn:Ef; cbn.
    all: rewrite ?Ef, ?Eg.
    all: now rewrite IH.
  Qed.

  Lemma remove_tok_fresh t s : mem t s = false -> remove_tok t s = s.
  Proof.
    induction s as [|[t' c] s IH]; cbn; [reflexivity|].
    intros H; apply orb_false_iff in H as [H1 H2].
    rewrite H1; cbn; f_equal; apply IH, H2.
  Qed.

  Lemma remove_tok_app t s1 s2 :
    remove_tok t (s1 ++ s2) = remove_tok t s1 ++ remove_tok t s2.
  Proof. apply filter_app. Qed.

  Lemma remove_tok_comm t1 t2 s :
    remove_tok t1 (remove_tok t2 s) = remove_tok t2 (remove_tok t1 s).
  Proof.
    unfold remove_tok; apply filter_comm.
  Qed.

  Lemma mem_remove_other t1 t2 s :
    t1 <> t2 -> mem t2 (remove_tok t1 s) = mem t2 s.
  Proof.
    intros Hne; unfold mem, remove_tok.
    induction s as [|h s IH]; cbn; [reflexivity|].
    destruct (fst h =? t1) eqn:E1; cbn.
    - apply Nat.eqb_eq in E1; rewrite E1, (proj2 (Nat.eqb_neq t1 t2) Hne).
      exact IH.
    - now rewrite IH.
  Qed.

  Lemma remove_tok_single_other t1 t2 c :
    t1 <> t2 -> remove_tok t1 [(t2, c)] = [(t2, c)].
  Proof.
    intros Hne; cbn.
    rewrite (proj2 (Nat.eqb_neq t2 t1)) by congruence; reflexivity.
  Qed.

  (** ** Registrations and dispatch are well behaved ... *)
  Definition proper_op (a : EOp) : Prop :=
    match a with OnByCallback _ => False | _ => True end.

  Lemma res_eq_refl (r : option (ESt * (ESt -> ESt) * list Cb)) :
    res_eq (Σ := EventBus) r r.
  Proof.
    destruct r as [[[s g] o]|]; cbn; [|exact I].
    split; [reflexivity | split; [intros x; reflexivity | reflexivity]].
  Qed.

  Theorem eventbus_well_behaved a t :
    proper_op a -> WellBehaved (Σ := EventBus) a t.
  Proof.
    intros Ha; split.
    - intros s s' g o; destruct a as [cb | cb | | cb]; cbn; try contradiction.
      + destruct (mem t s) eqn:E; [discriminate|].
        intros [= <- <- _].
        rewrite remove_tok_app, remove_tok_fresh by exact E; cbn.
        rewrite Nat.eqb_refl; cbn; apply app_nil_r.
      + destruct (mem t s) eqn:E; [discriminate|].
        intros [= <- <- _]; cbn.
        rewrite Nat.eqb_refl; cbn; apply remove_tok_fresh, E.
      + intros [= <- <- _]; reflexivity.
    - intros s1 s2 H; cbn in H; subst s2; apply res_eq_refl.
    - intros s s' g o _ x y H; cbn in H |- *; subst y; reflexivity.
  Qed.

  (** The inverse a registration yields is removing its own token. *)
  Definition is_reg (a : EOp) : Prop :=
    match a with On _ | Prepend _ => True | _ => False end.

  Lemma reg_yields a t g :
    is_reg a -> yields (Σ := EventBus) a t g -> g = remove_tok t.
  Proof.
    intros Ha (s & s' & o & H); destruct a; cbn in Ha, H; try contradiction;
      destruct (mem t s); try discriminate; injection H as _ <- _; reflexivity.
  Qed.

  (** ** ... registrations with distinct tokens are revert-independent ... *)
  Theorem reg_revert_indep a t1 b t2 :
    is_reg a -> is_reg b -> t1 <> t2 ->
    RevertIndep (Σ := EventBus) a t1 b t2.
  Proof.
    intros Ha Hb Hne g Hg; apply (reg_yields a t1 g Ha) in Hg; subst g; split.
    - intros x; destruct b as [cb | cb | | cb]; cbn in Hb |- *; try contradiction;
        rewrite (mem_remove_other t1 t2 x Hne);
        destruct (mem t2 x); cbn; try exact I;
        (split; [| split; [intros y; reflexivity | reflexivity]]).
      + rewrite remove_tok_app, remove_tok_single_other by exact Hne; reflexivity.
      + rewrite (proj2 (Nat.eqb_neq t2 t1)) by congruence; reflexivity.
    - intros h x Hh; apply (reg_yields b t2 h Hb) in Hh; subst h.
      apply remove_tok_comm.
  Qed.

  (** ** ... but they do not commute: the order of hooks differs. *)
  Theorem on_not_commute cb1 cb2 t1 t2 :
    t1 <> t2 -> ~ Commute (Σ := EventBus) (On cb1) t1 (On cb2) t2.
  Proof.
    intros Hne H; specialize (H []); unfold seq2 in H; cbn in H.
    rewrite (proj2 (Nat.eqb_neq t1 t2) Hne),
            (proj2 (Nat.eqb_neq t2 t1)) in H by congruence; cbn in H.
    destruct H as [H _]; cbn in H; congruence.
  Qed.

  (** ** Dispatch observes registrations. *)
  Theorem on_emit_not_indep cb t1 t2 :
    ~ RevertIndep (Σ := EventBus) (On cb) t1 Emit t2.
  Proof.
    intros HRI.
    assert (Hy : yields (Σ := EventBus) (On cb) t1 (remove_tok t1)).
    { exists [], [(t1, cb)], []; reflexivity. }
    destruct (HRI _ Hy) as [H _].
    specialize (H [(t1, cb)]); cbn in H.
    rewrite Nat.eqb_refl in H; cbn in H.
    destruct H as [_ [_ H]]; discriminate.
  Qed.

  (** ** Unregistering by callback is not an inverse: with the callback
      already registered once, undoing the second registration removes the
      first hook. *)
  Theorem on_by_callback_not_witnessed cb t :
    ~ Witnessed (Σ := EventBus) (OnByCallback cb) t.
  Proof.
    intros Hw.
    set (s := [(S t, cb)]).
    assert (Hrun : @run EventBus (OnByCallback cb) t s
                   = Some (s ++ [(t, cb)], remove_first_cb cb, [])).
    { change (erun (OnByCallback cb) t s
              = Some (s ++ [(t, cb)], remove_first_cb cb, [])).
      unfold erun, mem, s; cbn [existsb fst].
      rewrite (proj2 (Nat.eqb_neq (S t) t) (Nat.neq_succ_diag_l t)).
      reflexivity. }
    pose proof (Hw _ _ _ _ Hrun) as H; cbn in H.
    destruct (cb_eq_dec cb cb) as [_|]; [|contradiction].
    injection H as H; exact (Nat.neq_succ_diag_l t (eq_sym H)).
  Qed.
End EventBus.
