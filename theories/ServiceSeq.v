(** * Sequences of operations on one service (for state confluence)

    [Replay l s0 s]: running the operations of [l] (with their tokens) from
    [s0], each of them succeeding, ends at [s].

    The hypotheses speak of a relation [M] on operations: [M a b] says a and
    b may meet, that is, be performed on one binding by two different
    fibers. Under them:
    - removing an operation from the middle of a replay is the same as
      running its inverse at the end, when the operations after it meet it
      ([replay_remove]);
    - reordering a replay so that each fiber's operations keep their order
      changes its end only up to ≃ ([replay_shuffle], with fibers given as
      labels of tokens); so does permuting blocks of operations and changing
      tokens ([replay_blocks]);
    - an operation run after operations it meets sees the outcome it sees
      at the start ([outcome_after]).

    Hypotheses:
    - [Hwb]: every operation is well behaved;
    - [HUI]: the inverse an operation yields does not depend on the state;
    - [HTI]: the token does not matter, up to ≃;
    - [HMs]: [M] is symmetric;
    - [HCom]: operations that meet commute under distinct tokens;
    - [HRI]: withdrawing a is not disturbed by a later operation b it
      meets, on the states that can follow a ([After]) and where b
      succeeds; this is [RevertIndep]'s first clause, restricted to those
      cases ([revert_indep_after]). *)

From Stdlib Require Import List PeanoNat Lia RelationClasses Permutation.
From Cordis Require Import Prelude Service.
Import ListNotations.

(** The states that can follow [a] under [ta]: its results, then
    operations satisfying [G] under other tokens. *)
Section After.
  Context {Σ : Service} (G : Op Σ -> Prop).

  Inductive After (a : Op Σ) (ta : nat) : St Σ -> Prop :=
  | af_run x x' g o : run a ta x = Some (x', g, o) -> After a ta x'
  | af_step w b tb w' h o :
      After a ta w -> G b -> tb <> ta -> run b tb w = Some (w', h, o) -> After a ta w'.
End After.

Section Seq.
  Context {Σ : Service}.
  Local Notation S := (St Σ).
  Local Notation Item := (Op Σ * nat)%type.

  Variable M : Op Σ -> Op Σ -> Prop.
  Hypothesis Hwb : forall a t, WellBehaved (Σ := Σ) a t.
  Hypothesis HUI : forall (a : Op Σ) (t : nat) (s1 s2 s1' s2' : S) (g1 g2 : S -> S) (o1 o2 : Out Σ),
    run a t s1 = Some (s1', g1, o1) -> run a t s2 = Some (s2', g2, o2) ->
    fun_eq (Σ := Σ) g1 g2.
  Hypothesis HTI : forall (a : Op Σ) (t t' : nat) (s : S),
    match run a t s, run a t' s with
    | None, None => True
    | Some (s1, _, o1), Some (s2, _, o2) => s1 ≃ s2 /\ o1 = o2
    | _, _ => False
    end.
  Hypothesis HMs : forall a b, M a b -> M b a.
  Hypothesis HRI : forall (a b : Op Σ) (ta tb : nat) (g : S -> S), M a b -> ta <> tb ->
    yields (Σ := Σ) a ta g ->
    forall x, After (M a) a ta x -> shifted_ok (Σ := Σ) g (run b tb x) (run b tb (g x)).
  Hypothesis HCom : forall (a b : Op Σ) (ta tb : nat), M a b -> ta <> tb ->
    Commute (Σ := Σ) a ta b tb.

  Inductive Replay : list Item -> S -> S -> Prop :=
  | rp_nil s : Replay [] s s
  | rp_cons a t l s s1 g o s2 :
      run a t s = Some (s1, g, o) -> Replay l s1 s2 -> Replay ((a, t) :: l) s s2.

  Lemma replay_app l1 l2 s s2 :
    Replay (l1 ++ l2) s s2 <-> exists s1, Replay l1 s s1 /\ Replay l2 s1 s2.
  Proof.
    revert s; induction l1 as [|[a t] l1 IH]; intros s; cbn.
    - split; [intros H; exists s; split; [constructor | exact H]|].
      intros (s1 & H1 & H2); inversion H1; subst; exact H2.
    - split.
      + intros H; inversion H as [|a' t' l' s' s1 g o s2' Hr Hl]; subst.
        apply IH in Hl as (s3 & H3 & H4).
        exists s3; split; [econstructor; eauto | exact H4].
      + intros (s1 & H1 & H2); inversion H1 as [|a' t' l' s' s3 g o s4 Hr Hl]; subst.
        econstructor; [exact Hr|]; apply IH; eauto.
  Qed.

  (** Replays respect ≃. *)
  Lemma replay_respects l s x s' :
    Replay l s s' -> s ≃ x -> exists x', Replay l x x' /\ s' ≃ x'.
  Proof.
    intros H; revert x; induction H as [s|a t l s s1 g o s2 Hr Hl IH]; intros x Hsx.
    - exists x; split; [constructor | exact Hsx].
    - pose proof (wb_respects a t (Hwb a t) s x Hsx) as Hres.
      rewrite Hr in Hres.
      destruct (run a t x) as [[[x1 h] o']|] eqn:Hx; cbn in Hres; [|contradiction].
      destruct Hres as [E _].
      destruct (IH x1 E) as (x' & Hx' & E').
      exists x'; split; [econstructor; eauto | exact E'].
  Qed.

  (** A replay determines its end up to ≃. *)
  Lemma replay_det l s s1 s2 : Replay l s s1 -> Replay l s s2 -> s1 ≃ s2.
  Proof.
    intros H1; revert s2; induction H1 as [s|a t l s s1 g o s2 Hr Hl IH]; intros s3 H2.
    - inversion H2; reflexivity.
    - inversion H2 as [|a' t' l' s' s1' g' o' s2' Hr' Hl']; subst.
      rewrite Hr in Hr'; injection Hr' as <- <- <-.
      exact (IH _ Hl').
  Qed.

  (** Running an inverse after foreign operations: the inverse moves to the
      front. *)
  Lemma replay_shift (P : S -> Prop) (g : S -> S) l x s y :
    respects (Σ := Σ) g ->
    (forall b tb, In (b, tb) l -> forall z, P z -> shifted_ok (Σ := Σ) g (run b tb z) (run b tb (g z))) ->
    (forall b tb, In (b, tb) l -> forall z z' h o, P z -> run b tb z = Some (z', h, o) -> P z') ->
    P x -> Replay l x s -> y ≃ g x -> exists s', Replay l y s' /\ s' ≃ g s.
  Proof.
    intros Hg Hsh Hcl HP H; revert y HP; induction H as [x|b tb l x x1 h o x2 Hr Hl IH]; intros y HP Hy.
    - exists y; split; [constructor | exact Hy].
    - pose proof (Hsh b tb (or_introl eq_refl) x HP) as Hs; rewrite Hr in Hs.
      destruct (run b tb (g x)) as [[[z h'] o']|] eqn:Hz; cbn in Hs; [|contradiction].
      destruct Hs as [Ez _].
      pose proof (wb_respects b tb (Hwb b tb) (g x) y (symmetry Hy)) as Hres.
      rewrite Hz in Hres.
      destruct (run b tb y) as [[[y1 k] o'']|] eqn:Hy1; cbn in Hres; [|contradiction].
      destruct Hres as [E1 _].
      destruct (IH (fun b' tb' Hin => Hsh b' tb' (or_intror Hin))
                   (fun b' tb' Hin => Hcl b' tb' (or_intror Hin)) y1
                   (Hcl b tb (or_introl eq_refl) x x1 h o HP Hr)) as (s' & Hs' & E').
      { transitivity z; [symmetry; exact E1 | exact Ez]. }
      exists s'; split; [econstructor; eauto | exact E'].
  Qed.

  (** ** Removing an operation from the middle *)
  Lemma replay_remove a t g l1 l2 s0 s :
    (forall b tb, In (b, tb) l2 -> M a b /\ tb <> t) ->
    yields (Σ := Σ) a t g ->
    Replay (l1 ++ (a, t) :: l2) s0 s ->
    exists s', Replay (l1 ++ l2) s0 s' /\ g s ≃ s'.
  Proof.
    intros Hl2 Hy0 H; pose proof Hy0 as (z & z' & oz & Hz).
    apply replay_app in H as (y & Hy & H2).
    inversion H2 as [|a' t' l' y' y1 g' o s2' Hr Hl]; subst.
    pose proof (wb_witness a t (Hwb a t) y y1 g' o Hr) as Hw.
    pose proof (HUI a t z y z' y1 g g' oz o Hz Hr) as Hgg.
    assert (Hg : respects (Σ := Σ) g) by exact (wb_inv a t (Hwb a t) z z' g oz Hz).
    assert (Hsh : forall b tb, In (b, tb) l2 ->
              forall w, After (M a) a t w -> shifted_ok (Σ := Σ) g (run b tb w) (run b tb (g w))).
    { intros b tb Hin w Hw'; destruct (Hl2 b tb Hin) as [Mb Ht].
      exact (HRI a b t tb g Mb (fun E => Ht (eq_sym E)) Hy0 w Hw'). }
    assert (Hcl : forall b tb, In (b, tb) l2 ->
              forall w w' h o, After (M a) a t w -> run b tb w = Some (w', h, o) -> After (M a) a t w').
    { intros b tb Hin w w' h o' Hw' Hrun; destruct (Hl2 b tb Hin) as [Mb Ht].
      exact (af_step (M a) a t w b tb w' h o' Hw' Mb Ht Hrun). }
    destruct (replay_shift (After (M a) a t) g l2 y1 s y Hg Hsh Hcl (af_run (M a) a t y y1 g' o Hr) Hl)
      as (s' & Hs' & E).
    { transitivity (g' y1); [symmetry; exact Hw | symmetry; apply Hgg]. }
    exists s'; split; [apply replay_app; eauto | symmetry; exact E].
  Qed.

  (** ** Changing tokens *)
  Lemma replay_tokens l l' s s1 :
    map fst l = map fst l' -> Replay l s s1 ->
    forall x, s ≃ x -> exists x1, Replay l' x x1 /\ s1 ≃ x1.
  Proof.
    intros E H; revert l' E; induction H as [s|a t l s s1 g o s2 Hr Hl IH]; intros l' E x Hx.
    - destruct l'; [|discriminate]; exists x; split; [constructor | exact Hx].
    - destruct l' as [|[a' t'] l']; [discriminate|]; cbn in E; injection E as -> E.
      pose proof (HTI a' t t' s) as Ht; rewrite Hr in Ht.
      destruct (run a' t' s) as [[[s1' g1] o1]|] eqn:Hr'; [|contradiction].
      destruct Ht as [E1 _].
      pose proof (wb_respects a' t' (Hwb a' t') s x Hx) as Hres; rewrite Hr' in Hres.
      destruct (run a' t' x) as [[[x1 h] o2]|] eqn:Hx1; cbn in Hres; [|contradiction].
      destruct Hres as [E2 _].
      destruct (IH l' E x1) as (x2 & Hx2 & E3).
      { transitivity s1'; [exact E1 | exact E2]. }
      exists x2; split; [econstructor; eauto | exact E3].
  Qed.

  (** ** Moving operations past operations they meet *)
  Lemma replay_swap a t b u l s s2 :
    M a b -> t <> u ->
    Replay ((a, t) :: (b, u) :: l) s s2 ->
    exists s2', Replay ((b, u) :: (a, t) :: l) s s2' /\ s2 ≃ s2'.
  Proof.
    intros Mab Htu H.
    inversion H as [|a1 t1 l1 s' s1 g o s3 Hr Hl]; subst.
    inversion Hl as [|b1 u1 l2 s1' s4 h o' s5 Hr' Hl']; subst.
    pose proof (HCom a b t u Mab Htu s) as Hc; unfold seq2 in Hc.
    rewrite Hr, Hr' in Hc.
    destruct (run b u s) as [[[x1 h1] ob]|] eqn:Hb; [|contradiction].
    destruct (run a t x1) as [[[x2 h2] oa]|] eqn:Ha; [|contradiction].
    destruct Hc as [E _].
    destruct (replay_respects l s4 x2 s2 Hl' E) as (s2' & Hs2' & E').
    exists s2'; split; [econstructor; [exact Hb | econstructor; [exact Ha | exact Hs2']] | exact E'].
  Qed.

  Lemma move_front p y q s0 s :
    (forall z, In z p -> M (fst z) (fst y) /\ snd z <> snd y) ->
    Replay (p ++ y :: q) s0 s ->
    exists s', Replay (y :: p ++ q) s0 s' /\ s ≃ s'.
  Proof.
    revert s0 s; induction p as [|z p IH]; intros s0 s Hp H; [exists s; split; [exact H | reflexivity]|].
    cbn in H; inversion H as [|a t l x x1 g o x2 Hr Hl]; subst.
    destruct (IH x1 s (fun z' Hz => Hp z' (or_intror Hz)) Hl) as (s' & H' & E).
    destruct y as [b u].
    destruct (Hp (a, t) (or_introl eq_refl)) as [Mz Ht]; cbn in Mz, Ht.
    destruct (replay_swap a t b u (p ++ q) s0 s' Mz Ht (rp_cons a t _ s0 x1 g o s' Hr H')) as (s'' & H'' & E').
    exists s''; split; [exact H'' | transitivity s'; assumption].
  Qed.

  (** *** Keeping each fiber's order *)
  Section Shuffle.
    Context {L : Type} (L_eq_dec : forall x y : L, {x = y} + {x <> y}) (lab : nat -> L).

    Definition flab (λ : L) (l : list Item) : list Item :=
      filter (fun x => if L_eq_dec (lab (snd x)) λ then true else false) l.

    Definition Cross (l : list Item) : Prop :=
      forall x y, In x l -> In y l -> lab (snd x) <> lab (snd y) -> M (fst x) (fst y).

    Lemma flab_app λ l1 l2 : flab λ (l1 ++ l2) = flab λ l1 ++ flab λ l2.
    Proof. apply filter_app. Qed.

    Lemma in_flab λ x l : In x (flab λ l) <-> In x l /\ lab (snd x) = λ.
    Proof.
      unfold flab; rewrite filter_In.
      destruct (L_eq_dec (lab (snd x)) λ) as [E|N]; split; intros [H1 H2].
      - split; [exact H1 | exact E].
      - split; [exact H1 | reflexivity].
      - discriminate.
      - contradiction.
    Qed.

    Lemma flab_same_in l1 l2 x : (forall λ, flab λ l1 = flab λ l2) -> In x l2 -> In x l1.
    Proof.
      intros E Hx.
      assert (H : In x (flab (lab (snd x)) l2)) by (apply in_flab; auto).
      rewrite <- E in H; apply in_flab in H as [H _]; exact H.
    Qed.

    Lemma flab_nil_all l : (forall λ, flab λ l = []) -> l = [].
    Proof.
      destruct l as [|y l]; [reflexivity|]; intros H.
      specialize (H (lab (snd y))); unfold flab in H; cbn in H.
      destruct (L_eq_dec (lab (snd y)) (lab (snd y))); [discriminate | contradiction].
    Qed.

    Lemma flab_split λ x rest l :
      flab λ l = x :: rest -> exists p q, l = p ++ x :: q /\ flab λ p = [] /\ flab λ q = rest.
    Proof.
      induction l as [|y l IH]; [discriminate|]; unfold flab; cbn.
      destruct (L_eq_dec (lab (snd y)) λ) as [Ey|Ny].
      - intros [= -> E]; exists [], l; split; [reflexivity|]; split; [reflexivity | exact E].
      - intros H; destruct (IH H) as (p & q & -> & Hp & Hq).
        exists (y :: p), q; split; [reflexivity|]; split; [|exact Hq].
        cbn; destruct (L_eq_dec (lab (snd y)) λ); [contradiction | exact Hp].
    Qed.

    (** Two replays of the same operations that agree on each fiber's
        order end ≃. *)
    (** Reordering a replay so that each fiber keeps its order. *)
    Lemma replay_shuffle_ex l1 l2 s0 s1 :
      Cross l1 -> (forall λ, flab λ l1 = flab λ l2) ->
      Replay l1 s0 s1 -> exists s2, Replay l2 s0 s2 /\ s1 ≃ s2.
    Proof.
      revert l1 s0 s1; induction l2 as [|[a t] r IH]; intros l1 s0 s1 Cr Ef H1.
      - rewrite (flab_nil_all l1 Ef) in H1; inversion H1; subst.
        exists s1; split; [constructor | reflexivity].
      - set (λ := lab t).
        assert (Hλ : flab λ l1 = (a, t) :: flab λ r).
        { rewrite (Ef λ); unfold flab; cbn; destruct (L_eq_dec (lab t) λ); [reflexivity | contradiction]. }
        destruct (flab_split λ (a, t) (flab λ r) l1 Hλ) as (p & q & -> & Hp & Hq).
        assert (Hpl : forall z, In z p -> lab (snd z) <> λ).
        { intros z Hz Ez; assert (In z (flab λ p)) by (apply in_flab; auto); rewrite Hp in H; exact H. }
        assert (Hmv : forall z, In z p -> M (fst z) (fst (a, t)) /\ snd z <> snd (a, t)).
        { intros z Hz; split.
          - apply Cr; [apply in_or_app; left; exact Hz | apply in_or_app; right; left; reflexivity|].
            exact (Hpl z Hz).
          - intros Et; apply (Hpl z Hz); unfold λ; rewrite Et; reflexivity. }
        destruct (move_front p (a, t) q s0 s1 Hmv H1) as (s1' & H1' & E1).
        inversion H1' as [|a1 t1 l x x1 g o x2 Hr Hl]; subst.
        assert (Ef' : forall μ, flab μ (p ++ q) = flab μ r).
        { intros μ; rewrite flab_app.
          destruct (L_eq_dec μ λ) as [->|Hne].
          - rewrite Hp, Hq; reflexivity.
          - pose proof (Ef μ) as E; rewrite flab_app in E; unfold flab in E |- *; cbn in E.
            destruct (L_eq_dec (lab t) μ) as [Et|_]; [exfalso; apply Hne; rewrite <- Et; reflexivity|].
            rewrite <- E; reflexivity. }
        assert (Cr' : Cross (p ++ q)).
        { intros x y Hx Hy; apply Cr; apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff in Hy as [Hy|Hy];
            apply in_app_iff; auto; right; right; assumption. }
        destruct (IH (p ++ q) x1 s1' Cr' Ef' Hl) as (s2 & H2 & E2).
        exists s2; split; [econstructor; eauto | transitivity s1'; assumption].
    Qed.

    Lemma replay_shuffle l1 l2 s0 s0' s1 s2 :
      s0 ≃ s0' -> Cross l1 -> (forall λ, flab λ l1 = flab λ l2) ->
      Replay l1 s0 s1 -> Replay l2 s0' s2 -> s1 ≃ s2.
    Proof.
      intros E0 Cr Ef H1 H2.
      destruct (replay_shuffle_ex l1 l2 s0 s1 Cr Ef H1) as (s3 & H3 & E13).
      destruct (replay_respects l2 s0 s0' s3 H3 E0) as (s4 & H4 & E34).
      pose proof (replay_det l2 s0' s4 s2 H4 H2) as E42.
      transitivity s3; [exact E13|]; transitivity s4; assumption.
    Qed.

    (** Splitting off one fiber's operations. *)
    Definition fnot (λ : L) (l : list Item) : list Item :=
      filter (fun x => if L_eq_dec (lab (snd x)) λ then false else true) l.

    Lemma flab_flab λ μ l : flab μ (flab λ l) = if L_eq_dec μ λ then flab λ l else [].
    Proof.
      destruct (L_eq_dec μ λ) as [->|Ne]; induction l as [|x l IH]; unfold flab in *; cbn; auto;
        destruct (L_eq_dec (lab (snd x)) λ) as [E|N]; cbn; auto.
      - rewrite E; destruct (L_eq_dec λ λ); [rewrite IH; reflexivity | contradiction].
      - destruct (L_eq_dec (lab (snd x)) μ); [congruence | exact IH].
    Qed.

    Lemma flab_fnot λ μ l : flab μ (fnot λ l) = if L_eq_dec μ λ then [] else flab μ l.
    Proof.
      destruct (L_eq_dec μ λ) as [->|Ne]; induction l as [|x l IH]; unfold flab, fnot in *; cbn; auto;
        destruct (L_eq_dec (lab (snd x)) λ) as [E|N]; cbn; auto.
      - destruct (L_eq_dec (lab (snd x)) λ); [contradiction | exact IH].
      - destruct (L_eq_dec (lab (snd x)) μ); [congruence | exact IH].
      - destruct (L_eq_dec (lab (snd x)) μ); [rewrite IH; reflexivity | exact IH].
    Qed.

    Lemma flab_partition λ l μ : flab μ l = flab μ (flab λ l ++ fnot λ l).
    Proof.
      rewrite flab_app, flab_flab, flab_fnot.
      destruct (L_eq_dec μ λ) as [->|_]; [rewrite app_nil_r; reflexivity | reflexivity].
    Qed.
  End Shuffle.

  (** *** Permuting blocks *)
  Fixpoint CrossB (bs : list (list Item)) : Prop :=
    match bs with
    | [] => True
    | B :: bs' =>
        (forall x y, In x B -> In y (concat bs') -> M (fst x) (fst y) /\ snd x <> snd y) /\ CrossB bs'
    end.

  Lemma swap_blocks B1 B2 r s0 s :
    (forall x y, In x B1 -> In y B2 -> M (fst x) (fst y) /\ snd x <> snd y) ->
    Replay (B1 ++ B2 ++ r) s0 s -> exists s', Replay (B2 ++ B1 ++ r) s0 s' /\ s ≃ s'.
  Proof.
    revert s0 s; induction B2 as [|y B2 IH]; intros s0 s HB H; [exists s; split; [exact H | reflexivity]|].
    cbn in H.
    destruct (move_front B1 y (B2 ++ r) s0 s (fun z Hz => HB z y Hz (or_introl eq_refl)) H) as (s' & H' & E).
    inversion H' as [|a t l x x1 g o x2 Hr Hl]; subst.
    destruct (IH x1 s' (fun x0 y0 Hx Hy => HB x0 y0 Hx (or_intror Hy)) Hl) as (s'' & H'' & E').
    exists s''; split; [econstructor; eauto | transitivity s'; assumption].
  Qed.

  Lemma in_concat_perm (bs bs' : list (list Item)) y :
    Permutation bs bs' -> In y (concat bs) -> In y (concat bs').
  Proof.
    intros P Hy; apply in_concat in Hy as (B & HB & Hy).
    apply in_concat; exists B; split; [exact (Permutation_in _ P HB) | exact Hy].
  Qed.

  Lemma crossb_perm bs bs' : Permutation bs bs' -> CrossB bs -> CrossB bs'.
  Proof.
    intros P; induction P as [|B l l' P IH|B1 B2 l|l l' l'' P1 IH1 P2 IH2]; cbn; auto.
    - intros [H1 H2]; split; [|exact (IH H2)].
      intros x y Hx Hy; apply H1; [exact Hx | exact (in_concat_perm _ _ y (Permutation_sym P) Hy)].
    - intros [H1 [H2 H3]]; split; [|split; [|exact H3]].
      + intros x y Hx Hy; apply in_app_iff in Hy as [Hy|Hy].
        * destruct (H1 y x Hy (in_or_app _ _ _ (or_introl Hx))) as [Hm Ht]; split; [exact (HMs _ _ Hm) | congruence].
        * exact (H2 x y Hx Hy).
      + intros x y Hx Hy; exact (H1 x y Hx (in_or_app _ _ _ (or_intror Hy))).
  Qed.

  Lemma replay_blocks_perm bs bs' s0 s :
    Permutation bs bs' -> CrossB bs -> Replay (concat bs) s0 s ->
    exists s', Replay (concat bs') s0 s' /\ s ≃ s'.
  Proof.
    intros P; revert s0 s; induction P as [|B l l' P IH|B1 B2 l|l l' l'' P1 IH1 P2 IH2];
      intros s0 s C H; cbn in *.
    - exists s; split; [exact H | reflexivity].
    - apply replay_app in H as (s1 & H1 & H2).
      destruct (IH s1 s (proj2 C) H2) as (s' & H' & E).
      exists s'; split; [apply replay_app; eauto | exact E].
    - destruct C as [H1 _].
      apply (swap_blocks B2 B1 (concat l) s0 s); [|exact H].
      intros x y Hx Hy; exact (H1 x y Hx (in_or_app _ _ _ (or_introl Hy))).
    - destruct (IH1 s0 s C H) as (s1 & H1 & E1).
      destruct (IH2 s0 s1 (crossb_perm l l' P1 C) H1) as (s2 & H2 & E2).
      exists s2; split; [exact H2 | transitivity s1; assumption].
  Qed.

  Definition nonnil {A} (l : list A) : bool := match l with [] => false | _ => true end.

  Lemma concat_nonnil (bs : list (list Item)) : concat (filter nonnil bs) = concat bs.
  Proof. induction bs as [|[|x B] bs IH]; cbn; [reflexivity | exact IH | rewrite IH; reflexivity]. Qed.

  Lemma crossb_filter bs : CrossB bs -> CrossB (filter nonnil bs).
  Proof.
    induction bs as [|[|x B] bs IH]; cbn; [auto | intros [_ H]; exact (IH H)|].
    intros [H1 H2]; split; [|exact (IH H2)].
    intros x0 y Hx Hy; apply H1; [exact Hx|]; rewrite concat_nonnil in Hy; exact Hy.
  Qed.

  Lemma map_nonnil (bs : list (list Item)) :
    map (map fst) (filter nonnil bs) = filter nonnil (map (map fst) bs).
  Proof. induction bs as [|[|x B] bs IH]; cbn; [reflexivity | exact IH | rewrite IH; reflexivity]. Qed.

  (** Two replays made of the same blocks of operations, in any order of
      blocks and under any tokens, end ≃, when operations of different
      blocks meet. *)
  Lemma replay_blocks bs1 bs2 s0 s1 s2 :
    CrossB bs1 ->
    Permutation (filter nonnil (map (map fst) bs1)) (filter nonnil (map (map fst) bs2)) ->
    Replay (concat bs1) s0 s1 -> Replay (concat bs2) s0 s2 -> s1 ≃ s2.
  Proof.
    intros C P H1 H2.
    rewrite <- concat_nonnil in H1, H2; rewrite <- !map_nonnil in P.
    apply Permutation_sym in P.
    destruct (Permutation_map_inv _ _ P) as (bs3 & E3 & P3).
    destruct (replay_blocks_perm _ bs3 s0 s1 P3 (crossb_filter bs1 C) H1) as (s3 & H3 & E13).
    assert (Ef : map fst (concat bs3) = map fst (concat (filter nonnil bs2))) by (rewrite !concat_map, <- E3; reflexivity).
    destruct (replay_tokens _ _ s0 s3 Ef H3 s0 (reflexivity _)) as (s4 & H4 & E34).
    pose proof (replay_det _ s0 s4 s2 H4 H2) as E42.
    transitivity s3; [exact E13|]; transitivity s4; assumption.
  Qed.

  (** ** Outcomes do not see operations they meet *)
  Lemma outcome_after a t l s0 s :
    (forall b u, In (b, u) l -> M b a /\ u <> t) ->
    Replay l s0 s ->
    forall s' g o, run a t s = Some (s', g, o) ->
    exists s0' g0, run a t s0 = Some (s0', g0, o).
  Proof.
    intros Hl H; induction H as [s|b u l s s1 h ob s2 Hr Hl' IH]; intros s' g o Hrun.
    - eauto.
    - destruct (IH (fun b' u' Hin => Hl b' u' (or_intror Hin)) s' g o Hrun) as (x & gx & Hx).
      destruct (Hl b u (or_introl eq_refl)) as [Mba Hu].
      pose proof (HCom b a u t Mba Hu s) as Hc.
      unfold seq2 in Hc; rewrite Hr, Hx in Hc.
      destruct (run a t s) as [[[y gy] oa]|] eqn:Hy; [|contradiction].
      destruct (run b u y) as [[[y' gy'] ob']|]; [|contradiction].
      destruct Hc as [_ [_ Eo]].
      exists y, gy; rewrite Eo; reflexivity.
  Qed.
End Seq.

(** The hypothesis [HRI] above asks less than [RevertIndep]. *)
Lemma revert_indep_after {Σ : Service} (G : Op Σ -> Prop) a ta b tb g :
  RevertIndep (Σ := Σ) a ta b tb -> yields (Σ := Σ) a ta g ->
  forall x, After G a ta x -> shifted_ok (Σ := Σ) g (run b tb x) (run b tb (g x)).
Proof. intros H Hy x _; exact (shifted_ok_of _ _ _ (proj1 (H g Hy) x)). Qed.

(** [After] grows with the set of operations it allows. *)
Lemma after_mono {Σ : Service} (G1 G2 : Op Σ -> Prop) :
  (forall a, G1 a -> G2 a) -> forall a ta x, After G1 a ta x -> After G2 a ta x.
Proof.
  intros HG a ta x H; induction H as [x x' g o Hr|w b tb w' h o Hw IH Gb Ht Hr].
  - exact (af_run G2 a ta x x' g o Hr).
  - exact (af_step G2 a ta w b tb w' h o IH (HG b Gb) Ht Hr).
Qed.
