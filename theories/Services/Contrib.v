(** * Contribution keys (docs/CONTRIB.md, stage E6a)

    A registry whose table is derived, not mutated. Each fiber contributes
    tagged entries [(tag, name, value)]; the state is the multiset of live
    contributions, compared by [Permutation]; reading a name resolves it
    from the whole multiset. Compare [Registry.v], where the state is the
    table itself and a second registration under a taken name fails.

    - [Contribute e] never fails. Its inverse removes one copy of [e]
      ([Listeners.remove_first]), an exact inverse up to [Permutation], as
      for listener registration ([contrib_well_behaved]).
    - A name is private or public ([public]). A private name read by tag
      [q] resolves among [q]'s own contributions only
      ([resolve_private_local]): no other component can collide with it.
      This is the hygiene half of the design.
    - A public name resolves among every contribution: the entries of
      greatest priority, if they are one entry, give [ROne]; otherwise the
      result is [RConflict]. A collision is a value, not a failed fiber.
    - Resolution depends on the multiset alone ([resolve_perm]), so
      reading respects ≃ ([contrib_well_behaved]), unlike dispatch on an
      ordered list of listeners ([EventBus.on_not_commute]).
    - Two contributions commute ([contribute_commute]); a contribution and
      a read of the name it contributes to do not
      ([contribute_read_not_commute]). So a startup program must not read
      what another fiber may contribute; stage E6b excludes that pair from
      the meeting relation. *)

From Stdlib Require Import RelationClasses List PeanoNat Bool Permutation.
From Cordis Require Import Prelude Service Listeners.
Import ListNotations.

Section Contrib.
  Context (Tag Name V : Type).
  Context (tag_eq_dec : forall x y : Tag, {x = y} + {x <> y}).
  Context (name_eq_dec : forall x y : Name, {x = y} + {x <> y}).
  Context (v_eq_dec : forall x y : V, {x = y} + {x <> y}).
  Context (public : Name -> bool) (prio : V -> nat).

  (** ** Entries *)
  Definition Entry : Type := (Tag * Name * V)%type.

  Definition etag (e : Entry) : Tag := fst (fst e).
  Definition ename (e : Entry) : Name := snd (fst e).
  Definition eval (e : Entry) : V := snd e.

  Definition entry_eq_dec : forall x y : Entry, {x = y} + {x <> y}.
  Proof.
    intros [[t1 n1] v1] [[t2 n2] v2].
    destruct (tag_eq_dec t1 t2), (name_eq_dec n1 n2), (v_eq_dec v1 v2);
      first [left; congruence | right; congruence].
  Defined.

  Definition teqb (x y : Tag) : bool := if tag_eq_dec x y then true else false.
  Definition neqb (x y : Name) : bool := if name_eq_dec x y then true else false.

  (** ** Resolution *)
  Inductive Res : Type :=
  | RAbsent
  | ROne (t : Tag) (v : V)
  | RConflict.

  (** The entries a read of [x] by [q] considers. *)
  Definition visible_to (q : Tag) (x : Name) (e : Entry) : bool :=
    neqb (ename e) x && (public x || teqb (etag e) q).

  Definition top (l : list Entry) : list Entry :=
    let m := list_max (map (fun e => prio (eval e)) l) in
    nodup entry_eq_dec (filter (fun e => Nat.eqb (prio (eval e)) m) l).

  Definition classify (l : list Entry) : Res :=
    match l with
    | [] => RAbsent
    | [e] => ROne (etag e) (eval e)
    | _ => RConflict
    end.

  Definition resolve (s : list Entry) (q : Tag) (x : Name) : Res :=
    classify (top (filter (visible_to q x) s)).

  (** ** The service *)
  Inductive COp : Type :=
  | Contribute (e : Entry)
  | Read (q : Tag) (x : Name).

  Local Notation rf := (remove_first Entry entry_eq_dec).

  Definition crun (a : COp) (_ : Tok) (s : list Entry)
    : option (list Entry * (list Entry -> list Entry) * option Res) :=
    match a with
    | Contribute e => Some (e :: s, rf e, None)
    | Read q x => Some (s, fun s' => s', Some (resolve s q x))
    end.

  Definition Contrib : Service := {|
    St := list Entry; st_eq := @Permutation Entry;
    st_eq_equiv := Permutation_Equivalence Entry;
    Op := COp; Out := option Res; run := crun
  |}.

  (** ** Resolution depends on the multiset alone *)
  Lemma filter_perm (f : Entry -> bool) l l' :
    Permutation l l' -> Permutation (filter f l) (filter f l').
  Proof.
    induction 1 as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; cbn.
    - constructor.
    - destruct (f x); [apply perm_skip|]; exact IH.
    - destruct (f x), (f y); try reflexivity; apply perm_swap.
    - transitivity (filter f l'); assumption.
  Qed.

  Lemma list_max_perm l l' : Permutation l l' -> list_max l = list_max l'.
  Proof.
    assert (H : forall l l', Permutation l l' -> list_max l' <= list_max l).
    { intros l1 l2 P; apply list_max_le, Forall_forall; intros k Hk.
      apply (proj1 (Forall_forall _ l1) (proj1 (list_max_le l1 (list_max l1)) (le_n _))).
      exact (Permutation_in _ (Permutation_sym P) Hk). }
    intros P; apply Nat.le_antisymm; [apply H; symmetry|apply H]; exact P.
  Qed.

  Lemma nodup_perm l l' :
    Permutation l l' -> Permutation (nodup entry_eq_dec l) (nodup entry_eq_dec l').
  Proof.
    intros P; apply NoDup_Permutation; try apply NoDup_nodup.
    intros e; rewrite !nodup_In; split; intros H;
      [exact (Permutation_in _ P H) | exact (Permutation_in _ (Permutation_sym P) H)].
  Qed.

  Lemma top_perm l l' : Permutation l l' -> Permutation (top l) (top l').
  Proof.
    intros P; unfold top.
    rewrite (list_max_perm _ _ (Permutation_map _ P)).
    apply nodup_perm, filter_perm, P.
  Qed.

  Lemma classify_perm l l' : Permutation l l' -> classify l = classify l'.
  Proof.
    intros P; destruct l as [|e [|e2 r]].
    - rewrite (Permutation_nil P); reflexivity.
    - rewrite (Permutation_length_1_inv P); reflexivity.
    - pose proof (Permutation_length P) as L; cbn in L.
      destruct l' as [|a [|b r']]; cbn in L; try discriminate; reflexivity.
  Qed.

  Theorem resolve_perm s s' q x :
    Permutation s s' -> resolve s q x = resolve s' q x.
  Proof. intros P; apply classify_perm, top_perm, filter_perm, P. Qed.

  (** ** Hygiene: a private name sees its own tag's contributions only *)
  Lemma visible_private q x e :
    public x = false -> visible_to q x e = visible_to q x e && teqb (etag e) q.
  Proof.
    intros Hp; unfold visible_to; rewrite Hp; cbn.
    destruct (neqb (ename e) x), (teqb (etag e) q); reflexivity.
  Qed.

  Theorem resolve_private_local s q x :
    public x = false ->
    resolve s q x = resolve (filter (fun e => teqb (etag e) q) s) q x.
  Proof.
    intros Hp; unfold resolve; f_equal; f_equal.
    induction s as [|e s IH]; cbn; [reflexivity|].
    rewrite (visible_private q x e Hp).
    destruct (teqb (etag e) q) eqn:Et; cbn; rewrite ?Et, ?andb_true_r, ?andb_false_r;
      [destruct (visible_to q x e); [f_equal|]; exact IH | exact IH].
  Qed.

  (** Contributions under another tag do not move a private name. *)
  Corollary private_isolated s s' q x :
    public x = false ->
    filter (fun e => teqb (etag e) q) s = filter (fun e => teqb (etag e) q) s' ->
    resolve s q x = resolve s' q x.
  Proof.
    intros Hp E; rewrite (resolve_private_local s q x Hp), (resolve_private_local s' q x Hp), E;
      reflexivity.
  Qed.

  (** ** The service hypotheses that hold for every operation *)
  Theorem contrib_well_behaved a t : WellBehaved (Σ := Contrib) a t.
  Proof.
    split.
    - intros s s' g o; destruct a as [e|q x]; cbn; intros [= <- <- _];
        [rewrite rf_head; reflexivity | reflexivity].
    - intros s1 s2 P; destruct a as [e|q x]; cbn.
      + split; [apply perm_skip; exact P | split; [intros y; reflexivity | reflexivity]].
      + split; [exact P | split; [intros y; reflexivity | rewrite (resolve_perm _ _ q x P); reflexivity]].
    - intros s s' g o; destruct a as [e|q x]; cbn; intros [= _ <- _] y z P;
        [exact (rf_respects _ entry_eq_dec e y z P) | exact P].
  Qed.

  Lemma contrib_inverse_uniform (a : COp) (t : nat) (s1 s2 s1' s2' : list Entry)
      (g1 g2 : list Entry -> list Entry) (o1 o2 : option Res) :
    @run Contrib a t s1 = Some (s1', g1, o1) -> @run Contrib a t s2 = Some (s2', g2, o2) ->
    fun_eq (Σ := Contrib) g1 g2.
  Proof. destruct a; cbn; intros [= _ <- _] [= _ <- _] y; reflexivity. Qed.

  Lemma contrib_token_irrelevant (a : COp) (t t' : nat) (s : list Entry) :
    match @run Contrib a t s, @run Contrib a t' s with
    | None, None => True
    | Some (s1, _, o1), Some (s2, _, o2) => @st_eq Contrib s1 s2 /\ o1 = o2
    | _, _ => False
    end.
  Proof. destruct a; cbn; split; reflexivity. Qed.

  (** A contribution never fails, so a collision never fails a fiber. *)
  Lemma contribute_total e t s : exists s' g, @run Contrib (Contribute e) t s = Some (s', g, None).
  Proof. exists (e :: s), (rf e); reflexivity. Qed.

  (** ** Commutation *)
  Lemma contribute_commute e1 e2 t1 t2 :
    Commute (Σ := Contrib) (Contribute e1) t1 (Contribute e2) t2.
  Proof. intros s; cbn; split; [apply perm_swap | split; reflexivity]. Qed.

  Lemma read_commute q1 x1 q2 x2 t1 t2 :
    Commute (Σ := Contrib) (Read q1 x1) t1 (Read q2 x2) t2.
  Proof. intros s; cbn; split; [reflexivity | split; reflexivity]. Qed.

  (** A read sees whether a contribution to its name has happened yet. *)
  Theorem contribute_read_not_commute e q t1 t2 :
    visible_to q (ename e) e = true ->
    ~ Commute (Σ := Contrib) (Contribute e) t1 (Read q (ename e)) t2.
  Proof.
    intros Hv H; specialize (H []); cbn in H.
    unfold resolve, top in H; cbn in H; rewrite Hv in H; cbn in H.
    rewrite Nat.max_0_r, Nat.eqb_refl in H; cbn in H.
    destruct H as [_ [_ E]]; discriminate E.
  Qed.
End Contrib.

Arguments RAbsent {Tag V}.
Arguments ROne {Tag V} t v.
Arguments RConflict {Tag V}.
Arguments Contribute {Tag Name V} e.
Arguments Read {Tag Name V} q x.
