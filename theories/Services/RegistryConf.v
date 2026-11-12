(** * The registry under the confluence hypotheses

    [reg_meet a b] says when the registry lets two fibers perform a and b at
    one key: any two registrations, any two lookups, and a registration
    with a lookup of another name. The registry meets every hypothesis of
    the confluence theorems for it ([registry_hyps]).

    - Two registrations under one name used to be the obstacle
      ([Registry.register_same_not_indep]): withdrawing the first lets the
      second succeed. But on a state that follows the first, the second
      fails, so it is never pending beside it; [RevAfter] asks nothing then.
    - A lookup of a name another fiber registers at the same key is
      excluded: it depends on whether that fiber has registered yet
      ([Registry.register_lookup_same_not_indep]). A fiber looking up the
      names it registers itself is fine: one fiber's operations are never
      compared with each other. *)

From Stdlib Require Import RelationClasses.
From Cordis Require Import Prelude Service ServiceSeq Registry Compose.

Section RegistryConf.
  Context (Name V : Type).
  Context (name_eq_dec : forall x y : Name, {x = y} + {x <> y}).

  Local Notation Reg := (Registry Name V name_eq_dec).
  Local Notation upd := (upd Name V name_eq_dec).

  Definition reg_meet (a b : ROp Name V) : Prop :=
    match a, b with
    | Register _ _ x _, Lookup _ _ y => x <> y
    | Lookup _ _ x, Register _ _ y _ => x <> y
    | _, _ => True
    end.

  (** After a registration of x, x stays taken. *)
  Lemma after_taken (G : ROp Name V -> Prop) x v ta s :
    After (Σ := Reg) G (Register Name V x v) ta s -> s x <> None.
  Proof.
    intros H; induction H as [s0 s' g o Hr|w b tb w' h o Hw IH Gb Ht Hr].
    - cbn in Hr; destruct (s0 x); [discriminate|]; injection Hr as <- _ _.
      rewrite upd_same; discriminate.
    - destruct b as [y w0|y]; cbn in Hr.
      + destruct (w y) eqn:Ey; [discriminate|]; injection Hr as <- _ _.
        destruct (name_eq_dec x y) as [->|Hne]; [rewrite upd_same; discriminate|].
        rewrite upd_other by exact Hne; exact IH.
      + injection Hr as <- _ _; exact IH.
  Qed.

  Lemma lookup_yields x t g : yields (Σ := Reg) (Lookup Name V x) t g -> g = fun s => s.
  Proof. intros (s & s' & o & H); cbn in H; injection H as _ <- _; reflexivity. Qed.

  Theorem registry_hyps : ConfHyps Reg reg_meet.
  Proof.
    split.
    - exact (registry_well_behaved Name V name_eq_dec).
    - intros [x v|x] t s1 s2 s1' s2' g1 g2 o1 o2; cbn.
      + destruct (s1 x), (s2 x); try discriminate; intros [= _ <- _] [= _ <- _] y z; reflexivity.
      + intros [= _ <- _] [= _ <- _] y z; reflexivity.
    - intros [x v|x] t t' s; cbn.
      + destruct (s x); cbn; [exact I | split; [intro z; reflexivity | reflexivity]].
      + split; [intro z; reflexivity | reflexivity].
    - intros [x v|x] b ta tb g Mab Ht Hy s Hs.
      + destruct b as [y w|y]; cbn in Mab.
        * pose proof (after_taken _ x v ta s Hs) as Hx.
          destruct (name_eq_dec x y) as [<-|Hne].
          -- unfold shifted_ok; cbn; destruct (s x); [exact I | contradiction].
          -- exact (revert_indep_after (Σ := Reg) _ _ _ _ _ g
                      (register_revert_indep Name V name_eq_dec x v y w ta tb Hne) Hy s Hs).
        * exact (revert_indep_after (Σ := Reg) _ _ _ _ _ g
                   (register_lookup_indep Name V name_eq_dec x v y ta tb Mab) Hy s Hs).
      + apply lookup_yields in Hy; subst g; unfold shifted_ok.
        destruct (@run Reg b tb s) as [[[x1 h] o]|]; [|exact I].
        split; [intro z; reflexivity | split; [intros y z; reflexivity | reflexivity]].
    - intros [x v|x] [y w|y] ta tb Mab Ht; cbn in Mab.
      + destruct (name_eq_dec x y) as [<-|Hne];
          [|exact (register_commute Name V name_eq_dec x v y w ta tb Hne)].
        intros s; unfold seq2; cbn; destruct (s x); cbn; [exact I|].
        rewrite !upd_same; exact I.
      + intros s; unfold seq2; cbn; destruct (s x) eqn:Ex; cbn; [exact I|].
        rewrite upd_other by (intros E; apply Mab; symmetry; exact E).
        split; [intro z; reflexivity | split; reflexivity].
      + intros s; unfold seq2; cbn; destruct (s y) eqn:Ey; cbn; [exact I|].
        rewrite upd_other by exact Mab.
        split; [intro z; reflexivity | split; reflexivity].
      + intros s; unfold seq2; cbn.
        split; [intro z; reflexivity | split; reflexivity].
  Qed.
End RegistryConf.
