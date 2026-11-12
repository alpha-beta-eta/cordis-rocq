(** * A name-keyed registry (e.g. [ctx.tools])

    The state maps names to optional values and is compared pointwise.
    [Register x v] fails when x is taken; its inverse deletes x.
    [Lookup x] reads the entry at x. *)

From Stdlib Require Import RelationClasses.
From Cordis Require Import Prelude Service.

Section Registry.
  Context (Name V : Type).
  Context (name_eq_dec : forall x y : Name, {x = y} + {x <> y}).

  Definition RSt : Type := Name -> option V.

  Definition req (s1 s2 : RSt) : Prop := forall x, s1 x = s2 x.

  #[local] Instance req_equiv : Equivalence req.
  Proof.
    split.
    - intros s x; reflexivity.
    - intros s1 s2 H x; symmetry; apply H.
    - intros s1 s2 s3 H1 H2 x; rewrite H1; apply H2.
  Qed.

  Inductive ROp : Type :=
  | Register (x : Name) (v : V)
  | Lookup (x : Name).

  Definition upd (s : RSt) (x : Name) (o : option V) : RSt :=
    fun y => if name_eq_dec y x then o else s y.

  Definition rrun (a : ROp) (_ : Tok) (s : RSt)
    : option (RSt * (RSt -> RSt) * option V) :=
    match a with
    | Register x v =>
        match s x with
        | None => Some (upd s x (Some v), fun s' => upd s' x None, None)
        | Some _ => None
        end
    | Lookup x => Some (s, fun s' => s', s x)
    end.

  Definition Registry : Service := {|
    St := RSt; st_eq := req; st_eq_equiv := req_equiv;
    Op := ROp; Out := option V; run := rrun
  |}.

  Lemma upd_same s x o : upd s x o x = o.
  Proof. unfold upd; destruct (name_eq_dec x x); congruence. Qed.

  Lemma upd_other s x y o : y <> x -> upd s x o y = s y.
  Proof. intros H; unfold upd; destruct (name_eq_dec y x); congruence. Qed.

  Ltac upd_simpl :=
    repeat first
      [ rewrite upd_same
      | rewrite upd_other by (intro; subst; contradiction) ].

  (** ** Every operation is well behaved. *)
  Theorem registry_well_behaved (a : ROp) (t : Tok) : WellBehaved (Σ := Registry) a t.
  Proof.
    split.
    - intros s s' g o; destruct a as [x v | x]; cbn.
      + destruct (s x) eqn:Ex; [discriminate|].
        intros [= <- <- _] y; unfold upd.
        destruct (name_eq_dec y x); [subst; congruence | reflexivity].
      + intros [= <- <- _]; reflexivity.
    - intros s1 s2 H; destruct a as [x v | x]; cbn.
      + rewrite <- (H x); destruct (s1 x); cbn; [exact I|].
        split; [|split; [|reflexivity]].
        * intros y; unfold upd; destruct (name_eq_dec y x); [reflexivity | apply H].
        * intros s y; reflexivity.
      + split; [exact H | split; [intros s y; reflexivity | apply H]].
    - intros s s' g o; destruct a as [x v | x]; cbn.
      + destruct (s x); [discriminate|].
        intros [= _ <- _] s1 s2 H y; unfold upd.
        destruct (name_eq_dec y x); [reflexivity | apply H].
      + intros [= _ <- _] s1 s2 H; exact H.
  Qed.

  (** The inverse a [Register x v] yields is deleting x. *)
  Lemma register_yields x v t g :
    yields (Σ := Registry) (Register x v) t g -> g = fun s => upd s x None.
  Proof.
    intros (s & s' & o & H); cbn in H.
    destruct (s x); cbn in H; [discriminate|].
    injection H as _ <- _; reflexivity.
  Qed.

  (** ** Registrations under distinct names are revert-independent ... *)
  Theorem register_revert_indep x v y w t1 t2 :
    x <> y ->
    RevertIndep (Σ := Registry) (Register x v) t1 (Register y w) t2.
  Proof.
    intros Hxy g Hg; apply register_yields in Hg; subst g; split.
    - intros s; cbn.
      rewrite (upd_other s x y None) by congruence.
      destruct (s y); cbn; [exact I|].
      split; [|split; [intros s1 z; reflexivity | reflexivity]].
      intros z; unfold upd.
      destruct (name_eq_dec z y), (name_eq_dec z x); congruence.
    - intros h s Hh; apply register_yields in Hh; subst h.
      intros z; cbn; unfold upd.
      destruct (name_eq_dec z y), (name_eq_dec z x); congruence.
  Qed.

  (** ... and they commute. *)
  Theorem register_commute x v y w t1 t2 :
    x <> y -> Commute (Σ := Registry) (Register x v) t1 (Register y w) t2.
  Proof.
    intros Hxy s; unfold seq2; cbn.
    destruct (s x) eqn:Ex, (s y) eqn:Ey; cbn;
      rewrite ?(upd_other s x y) by congruence;
      rewrite ?(upd_other s y x) by congruence;
      rewrite ?Ex, ?Ey; cbn; try exact I.
    split; [|split; reflexivity].
    intros z; unfold upd.
    destruct (name_eq_dec z y), (name_eq_dec z x); congruence.
  Qed.

  (** ** Two registrations under the same name are not revert-independent:
      withdrawing the first changes whether the second succeeds. *)
  Theorem register_same_not_indep x v w t1 t2 :
    ~ RevertIndep (Σ := Registry) (Register x v) t1 (Register x w) t2.
  Proof.
    intros HRI.
    set (empty := fun _ : Name => @None V).
    assert (Hy : yields (Σ := Registry) (Register x v) t1 (fun s => upd s x None)).
    { exists empty, (upd empty x (Some v)), None; reflexivity. }
    destruct (HRI _ Hy) as [H _].
    specialize (H (upd empty x (Some v))); cbn in H.
    rewrite upd_same, upd_same in H; exact H.
  Qed.

  (** ** Reading another plugin's entry is not revert-independent of it. *)
  Theorem register_lookup_indep x v y t1 t2 :
    x <> y -> RevertIndep (Σ := Registry) (Register x v) t1 (Lookup y) t2.
  Proof.
    intros Hxy g Hg; apply register_yields in Hg; subst g; split.
    - intros s; cbn.
      split; [intros z; reflexivity | split; [intros s1 z; reflexivity|]].
      apply upd_other; congruence.
    - intros h s (s0 & s0' & o & Hh); cbn in Hh; injection Hh as _ <- _.
      intros z; reflexivity.
  Qed.

  Theorem register_lookup_same_not_indep x v t1 t2 :
    ~ RevertIndep (Σ := Registry) (Register x v) t1 (Lookup x) t2.
  Proof.
    intros HRI.
    set (empty := fun _ : Name => @None V).
    assert (Hy : yields (Σ := Registry) (Register x v) t1 (fun s => upd s x None)).
    { exists empty, (upd empty x (Some v)), None; reflexivity. }
    destruct (HRI _ Hy) as [H _].
    specialize (H (upd empty x (Some v))); cbn in H.
    destruct H as [_ [_ H]].
    rewrite upd_same, upd_same in H; discriminate.
  Qed.
End Registry.
