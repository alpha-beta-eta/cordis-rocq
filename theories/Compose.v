(** * Composing services

    1. [ConfHyps Σ R]: the service hypotheses the confluence theorems use,
       for a relation [R] on operations: [R a b] when a and b may meet, that
       is, when two fibers may perform them at one key.
       [service_confluence] instantiates [spawn_confluence] from them; it
       asks [R] to cover the pairs the programs allow ([CoPair]).
    2. [Sum Σ1 Σ2]: two services side by side. A state belongs to one of
       them; an operation of one service fails on a state of the other.
       [sum_hyps]: the hypotheses hold for the sum when they hold for each
       part. Operations of different parts never meet on one state, so they
       commute and stay out of each other's way. *)

From Stdlib Require Import RelationClasses List.
From Cordis Require Import Prelude Service ServiceSeq Calculus Recovery Termination Progress Confluence StateInv Episode StateConf SpawnConf.
Import ListNotations.

(** ** The hypotheses, bundled *)
Definition UniformInv (Σ : Service) : Prop :=
  forall (a : Op Σ) (t : nat) (s1 s2 s1' s2' : St Σ) (g1 g2 : St Σ -> St Σ) (o1 o2 : Out Σ),
    run a t s1 = Some (s1', g1, o1) -> run a t s2 = Some (s2', g2, o2) -> fun_eq (Σ := Σ) g1 g2.

Definition TokIrr (Σ : Service) : Prop :=
  forall (a : Op Σ) (t t' : nat) (s : St Σ),
    match run a t s, run a t' s with
    | None, None => True
    | Some (s1, _, o1), Some (s2, _, o2) => s1 ≃ s2 /\ o1 = o2
    | _, _ => False
    end.

Definition RevAfter (Σ : Service) (R : Op Σ -> Op Σ -> Prop) : Prop :=
  forall (a b : Op Σ) (ta tb : nat) (g : St Σ -> St Σ), R a b -> ta <> tb ->
    yields (Σ := Σ) a ta g ->
    forall x, After (R a) a ta x -> shifted_ok (Σ := Σ) g (run b tb x) (run b tb (g x)).

Definition ComG (Σ : Service) (R : Op Σ -> Op Σ -> Prop) : Prop :=
  forall (a b : Op Σ) (ta tb : nat), R a b -> ta <> tb -> Commute (Σ := Σ) a ta b tb.

Record ConfHyps (Σ : Service) (G : Op Σ -> Op Σ -> Prop) : Prop := {
  ch_wb : forall a t, WellBehaved (Σ := Σ) a t;
  ch_ui : UniformInv Σ;
  ch_ti : TokIrr Σ;
  ch_ri : RevAfter Σ G;
  ch_com : ComG Σ G
}.

(** ** Confluence from the bundle *)
Section Generic.
  Context {Σ : Service} (G : Op Σ -> Op Σ -> Prop) (H : ConfHyps Σ G).
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context {C : Type} (prog : C -> @Component K Σ C).
  Variable Kb : nat.
  Hypothesis HK : forall c, Bounded Σ Kb (body Σ (prog c)).
  Variable rank : C -> nat.
  Variable Rb : nat.
  Hypothesis Hrank : forall c c', Above Σ prog c c' -> rank c < rank c'.
  Hypothesis Hbnd : forall c, rank c <= Rb.
  Hypothesis Total : forall c k, In k (provs Σ (prog c)) -> AllDoneProv Σ k (body Σ (prog c)).
  (** Every pair of operations two fibers may perform at one key is in [G]. *)
  Hypothesis HG : forall k a b, CoPair Σ prog k a b -> G a b.

  Theorem service_confluence (γ0 γ1 γ2 : State Σ) :
    PInv K_eq_dec Σ prog Kb γ0 -> SLInv Σ γ0 ->
    LRun K_eq_dec Σ prog γ0 γ1 -> LRun K_eq_dec Σ prog γ0 γ2 ->
    quiet K_eq_dec Σ prog γ1 -> quiet K_eq_dec Σ prog γ2 ->
    NoFailed Σ γ1 -> NoFailed Σ γ2 ->
    Agree Σ γ1 γ2.
  Proof.
    exact (spawn_confluence K_eq_dec Σ prog Kb HK rank Rb Hrank Hbnd Total
             (ch_wb _ _ H) (ch_ui _ _ H) (ch_ti _ _ H)
             (fun k a b ta tb g Cab Ht Hy x Hx =>
                ch_ri _ _ H a b ta tb g (HG k a b Cab) Ht Hy x
                  (after_mono _ _ (fun b' => HG k a b') a ta x Hx))
             (fun k a b ta tb Cab Ht => ch_com _ _ H a b ta tb (HG k a b Cab) Ht)
             γ0 γ1 γ2).
  Qed.
End Generic.

(** ** Two services side by side *)
Section Sum.
  Context (Σ1 Σ2 : Service).
  Local Notation S1 := (St Σ1).
  Local Notation S2 := (St Σ2).

  Definition sum_eq (x y : S1 + S2) : Prop :=
    match x, y with
    | inl a, inl b => a ≃ b
    | inr a, inr b => a ≃ b
    | _, _ => False
    end.

  #[local] Instance sum_eq_equiv : Equivalence sum_eq.
  Proof.
    split.
    - intros [a|a]; cbn; reflexivity.
    - intros [a|a] [b|b] E; cbn in *; try contradiction; symmetry; exact E.
    - intros [a|a] [b|b] [c|c] E1 E2; cbn in *; try contradiction; etransitivity; eauto.
  Qed.

  Definition lift1 (g : S1 -> S1) (x : S1 + S2) : S1 + S2 :=
    match x with inl a => inl (g a) | inr b => inr b end.
  Definition lift2 (g : S2 -> S2) (x : S1 + S2) : S1 + S2 :=
    match x with inl a => inl a | inr b => inr (g b) end.

  Definition srun (a : Op Σ1 + Op Σ2) (t : nat) (x : S1 + S2)
      : option ((S1 + S2) * (S1 + S2 -> S1 + S2) * (Out Σ1 + Out Σ2)) :=
    match a, x with
    | inl a1, inl s1 =>
        match run a1 t s1 with Some (s', g, o) => Some (inl s', lift1 g, inl o) | None => None end
    | inr a2, inr s2 =>
        match run a2 t s2 with Some (s', g, o) => Some (inr s', lift2 g, inr o) | None => None end
    | _, _ => None
    end.

  Definition Sum : Service := {|
    St := S1 + S2; st_eq := sum_eq; st_eq_equiv := sum_eq_equiv;
    Op := Op Σ1 + Op Σ2; Out := Out Σ1 + Out Σ2; run := srun
  |}.

  (** Operations of different parts never meet on one state; pairs from
      one part meet as that part says. *)
  Definition sumG (G1 : Op Σ1 -> Op Σ1 -> Prop) (G2 : Op Σ2 -> Op Σ2 -> Prop)
      (a b : Op Σ1 + Op Σ2) : Prop :=
    match a, b with
    | inl a1, inl b1 => G1 a1 b1
    | inr a2, inr b2 => G2 a2 b2
    | _, _ => True
    end.

  (** *** Inversion *)
  Lemma srun_inl a t x x' g o : srun (inl a) t x = Some (x', g, o) ->
    exists s s' g1 o1, x = inl s /\ run a t s = Some (s', g1, o1) /\ x' = inl s' /\ g = lift1 g1 /\ o = inl o1.
  Proof.
    destruct x as [s|s]; cbn; [|discriminate].
    destruct (run a t s) as [[[s' g1] o1]|] eqn:E; [|discriminate].
    intros [= <- <- <-]; exists s, s', g1, o1; auto.
  Qed.

  Lemma srun_inr a t x x' g o : srun (inr a) t x = Some (x', g, o) ->
    exists s s' g1 o1, x = inr s /\ run a t s = Some (s', g1, o1) /\ x' = inr s' /\ g = lift2 g1 /\ o = inr o1.
  Proof.
    destruct x as [s|s]; cbn; [discriminate|].
    destruct (run a t s) as [[[s' g1] o1]|] eqn:E; [|discriminate].
    intros [= <- <- <-]; exists s, s', g1, o1; auto.
  Qed.

  Lemma lift1_respects g : respects (Σ := Σ1) g -> respects (Σ := Sum) (lift1 g).
  Proof. intros Hg [a|a] [b|b] E; cbn in *; try contradiction; [apply Hg; exact E | exact E]. Qed.
  Lemma lift2_respects g : respects (Σ := Σ2) g -> respects (Σ := Sum) (lift2 g).
  Proof. intros Hg [a|a] [b|b] E; cbn in *; try contradiction; [exact E | apply Hg; exact E]. Qed.

  Lemma lift1_fun_eq g h : fun_eq (Σ := Σ1) g h -> fun_eq (Σ := Sum) (lift1 g) (lift1 h).
  Proof. intros E [a|a]; cbn; [apply E | reflexivity]. Qed.
  Lemma lift2_fun_eq g h : fun_eq (Σ := Σ2) g h -> fun_eq (Σ := Sum) (lift2 g) (lift2 h).
  Proof. intros E [a|a]; cbn; [reflexivity | apply E]. Qed.

  (** *** Well behaved *)
  Lemma sum_wb : (forall a t, WellBehaved (Σ := Σ1) a t) -> (forall a t, WellBehaved (Σ := Σ2) a t) ->
    forall a t, WellBehaved (Σ := Sum) a t.
  Proof.
    intros W1 W2 [a|a] t; split.
    - intros x x' g o Hr; apply srun_inl in Hr as (s & s' & g1 & o1 & -> & Hr & -> & -> & ->); cbn.
      exact (wb_witness a t (W1 a t) s s' g1 o1 Hr).
    - intros [s1|s1] [s2|s2] E; cbn in E; try contradiction; cbn; [|exact I].
      pose proof (wb_respects a t (W1 a t) s1 s2 E) as R.
      destruct (run a t s1) as [[[x1 g1] o1]|], (run a t s2) as [[[x2 g2] o2]|];
        cbn in R |- *; try contradiction; try exact I.
      destruct R as (Ex & Eg & Eo); split; [exact Ex | split; [apply lift1_fun_eq; exact Eg | congruence]].
    - intros x x' g o Hr; apply srun_inl in Hr as (s & s' & g1 & o1 & -> & Hr & -> & -> & ->).
      apply lift1_respects; exact (wb_inv a t (W1 a t) s s' g1 o1 Hr).
    - intros x x' g o Hr; apply srun_inr in Hr as (s & s' & g1 & o1 & -> & Hr & -> & -> & ->); cbn.
      exact (wb_witness a t (W2 a t) s s' g1 o1 Hr).
    - intros [s1|s1] [s2|s2] E; cbn in E; try contradiction; cbn; [exact I|].
      pose proof (wb_respects a t (W2 a t) s1 s2 E) as R.
      destruct (run a t s1) as [[[x1 g1] o1]|], (run a t s2) as [[[x2 g2] o2]|];
        cbn in R |- *; try contradiction; try exact I.
      destruct R as (Ex & Eg & Eo); split; [exact Ex | split; [apply lift2_fun_eq; exact Eg | congruence]].
    - intros x x' g o Hr; apply srun_inr in Hr as (s & s' & g1 & o1 & -> & Hr & -> & -> & ->).
      apply lift2_respects; exact (wb_inv a t (W2 a t) s s' g1 o1 Hr).
  Qed.

  (** *** Uniform inverses, token irrelevance *)
  Lemma sum_ui : UniformInv Σ1 -> UniformInv Σ2 -> UniformInv Sum.
  Proof.
    intros U1 U2 [a|a] t x1 x2 x1' x2' g1 g2 o1 o2 H1 H2.
    - apply srun_inl in H1 as (s1 & s1' & h1 & p1 & -> & R1 & -> & -> & ->).
      apply srun_inl in H2 as (s2 & s2' & h2 & p2 & -> & R2 & -> & -> & ->).
      apply lift1_fun_eq; exact (U1 a t s1 s2 s1' s2' h1 h2 p1 p2 R1 R2).
    - apply srun_inr in H1 as (s1 & s1' & h1 & p1 & -> & R1 & -> & -> & ->).
      apply srun_inr in H2 as (s2 & s2' & h2 & p2 & -> & R2 & -> & -> & ->).
      apply lift2_fun_eq; exact (U2 a t s1 s2 s1' s2' h1 h2 p1 p2 R1 R2).
  Qed.

  Lemma sum_ti : TokIrr Σ1 -> TokIrr Σ2 -> TokIrr Sum.
  Proof.
    intros T1 T2 [a|a] t t' [s|s]; cbn; try exact I.
    - pose proof (T1 a t t' s) as T.
      destruct (run a t s) as [[[x1 g1] o1]|], (run a t' s) as [[[x2 g2] o2]|];
        cbn in *; try contradiction; try exact I.
      destruct T as [E Eo]; split; [exact E | congruence].
    - pose proof (T2 a t t' s) as T.
      destruct (run a t s) as [[[x1 g1] o1]|], (run a t' s) as [[[x2 g2] o2]|];
        cbn in *; try contradiction; try exact I.
      destruct T as [E Eo]; split; [exact E | congruence].
  Qed.

  (** *** Withdrawing, after an operation of one part *)
  Lemma after_inl (Good : Op Sum -> Prop) a ta x :
    After (Σ := Sum) Good (inl a) ta x ->
    exists s, x = inl s /\ After (Σ := Σ1) (fun a1 => Good (inl a1)) a ta s.
  Proof.
    intros H; induction H as [x x' g o Hr|w b tb w' h o Hw IH Gb Ht Hr].
    - apply srun_inl in Hr as (s & s' & g1 & o1 & -> & R & -> & -> & ->).
      exists s'; split; [reflexivity | exact (af_run _ a ta s s' g1 o1 R)].
    - destruct IH as (s & -> & Ha).
      destruct b as [b|b]; [|cbn in Hr; discriminate].
      apply srun_inl in Hr as (s0 & s' & h1 & o1 & E & R & -> & -> & ->); injection E as <-.
      exists s'; split; [reflexivity | exact (af_step _ a ta s b tb s' h1 o1 Ha Gb Ht R)].
  Qed.

  Lemma after_inr (Good : Op Sum -> Prop) a ta x :
    After (Σ := Sum) Good (inr a) ta x ->
    exists s, x = inr s /\ After (Σ := Σ2) (fun a2 => Good (inr a2)) a ta s.
  Proof.
    intros H; induction H as [x x' g o Hr|w b tb w' h o Hw IH Gb Ht Hr].
    - apply srun_inr in Hr as (s & s' & g1 & o1 & -> & R & -> & -> & ->).
      exists s'; split; [reflexivity | exact (af_run _ a ta s s' g1 o1 R)].
    - destruct IH as (s & -> & Ha).
      destruct b as [b|b]; [cbn in Hr; discriminate|].
      apply srun_inr in Hr as (s0 & s' & h1 & o1 & E & R & -> & -> & ->); injection E as <-.
      exists s'; split; [reflexivity | exact (af_step _ a ta s b tb s' h1 o1 Ha Gb Ht R)].
  Qed.

  Lemma sum_ri G1 G2 : RevAfter Σ1 G1 -> RevAfter Σ2 G2 -> RevAfter Sum (sumG G1 G2).
  Proof.
    intros R1 R2 [a|a] [b|b] ta tb g Gab Ht (z & z' & oz & Hz) x Hx; cbn in Gab; unfold shifted_ok.
    - apply srun_inl in Hz as (s0 & s0' & g1 & o1 & _ & Hz1 & _ & -> & _).
      destruct (after_inl _ a ta x Hx) as (s & -> & Ha).
      pose proof (R1 a b ta tb g1 Gab Ht (ex_intro _ s0 (ex_intro _ s0' (ex_intro _ o1 Hz1))) s Ha) as Sh.
      unfold shifted_ok in Sh; cbn.
      destruct (run b tb s) as [[[x1 h] o]|]; [|exact I].
      destruct (run b tb (g1 s)) as [[[x2 h'] o']|]; [|contradiction].
      destruct Sh as (E & Eh & Eo); split; [exact E | split; [apply lift1_fun_eq; exact Eh | congruence]].
    - destruct (after_inl _ a ta x Hx) as (s & -> & _); cbn; exact I.
    - destruct (after_inr _ a ta x Hx) as (s & -> & _); cbn; exact I.
    - apply srun_inr in Hz as (s0 & s0' & g1 & o1 & _ & Hz1 & _ & -> & _).
      destruct (after_inr _ a ta x Hx) as (s & -> & Ha).
      pose proof (R2 a b ta tb g1 Gab Ht (ex_intro _ s0 (ex_intro _ s0' (ex_intro _ o1 Hz1))) s Ha) as Sh.
      unfold shifted_ok in Sh; cbn.
      destruct (run b tb s) as [[[x1 h] o]|]; [|exact I].
      destruct (run b tb (g1 s)) as [[[x2 h'] o']|]; [|contradiction].
      destruct Sh as (E & Eh & Eo); split; [exact E | split; [apply lift2_fun_eq; exact Eh | congruence]].
  Qed.

  (** *** Commutation *)
  Lemma seq2_inl (a b : Op Σ1) ta tb s :
    seq2 (Σ := Sum) (inl a) ta (inl b) tb (inl s) =
    match seq2 (Σ := Σ1) a ta b tb s with Some (s2, oa, ob) => Some (inl s2, inl oa, inl ob) | None => None end.
  Proof.
    unfold seq2; cbn; destruct (run a ta s) as [[[s1 g] oa]|]; cbn; [|reflexivity].
    destruct (run b tb s1) as [[[s2 h] ob]|]; reflexivity.
  Qed.

  Lemma seq2_inr (a b : Op Σ2) ta tb s :
    seq2 (Σ := Sum) (inr a) ta (inr b) tb (inr s) =
    match seq2 (Σ := Σ2) a ta b tb s with Some (s2, oa, ob) => Some (inr s2, inr oa, inr ob) | None => None end.
  Proof.
    unfold seq2; cbn; destruct (run a ta s) as [[[s1 g] oa]|]; cbn; [|reflexivity].
    destruct (run b tb s1) as [[[s2 h] ob]|]; reflexivity.
  Qed.

  Lemma seq2_lr (a : Op Σ1) (b : Op Σ2) ta tb x : seq2 (Σ := Sum) (inl a) ta (inr b) tb x = None.
  Proof.
    unfold seq2; destruct x as [s|s]; cbn; [|reflexivity].
    destruct (run a ta s) as [[[s1 g] o]|]; reflexivity.
  Qed.

  Lemma seq2_rl (a : Op Σ2) (b : Op Σ1) ta tb x : seq2 (Σ := Sum) (inr a) ta (inl b) tb x = None.
  Proof.
    unfold seq2; destruct x as [s|s]; cbn; [reflexivity|].
    destruct (run a ta s) as [[[s1 g] o]|]; reflexivity.
  Qed.

  Lemma sum_com G1 G2 : ComG Σ1 G1 -> ComG Σ2 G2 -> ComG Sum (sumG G1 G2).
  Proof.
    intros C1 C2 [a|a] [b|b] ta tb Gab Ht x; cbn in Gab.
    - destruct x as [s|s]; [|unfold seq2; cbn; exact I].
      rewrite !seq2_inl; pose proof (C1 a b ta tb Gab Ht s) as Hc.
      destruct (seq2 a ta b tb s) as [[[s1 oa] ob]|], (seq2 b tb a ta s) as [[[s2 ob'] oa']|];
        cbn in *; try contradiction; try exact I.
      destruct Hc as (E & E1 & E2); split; [exact E | split; congruence].
    - rewrite seq2_lr, seq2_rl; exact I.
    - rewrite seq2_rl, seq2_lr; exact I.
    - destruct x as [s|s]; [unfold seq2; cbn; exact I|].
      rewrite !seq2_inr; pose proof (C2 a b ta tb Gab Ht s) as Hc.
      destruct (seq2 a ta b tb s) as [[[s1 oa] ob]|], (seq2 b tb a ta s) as [[[s2 ob'] oa']|];
        cbn in *; try contradiction; try exact I.
      destruct Hc as (E & E1 & E2); split; [exact E | split; congruence].
  Qed.

  Theorem sum_hyps G1 G2 : ConfHyps Σ1 G1 -> ConfHyps Σ2 G2 -> ConfHyps Sum (sumG G1 G2).
  Proof.
    intros H1 H2; split.
    - exact (sum_wb (ch_wb _ _ H1) (ch_wb _ _ H2)).
    - exact (sum_ui (ch_ui _ _ H1) (ch_ui _ _ H2)).
    - exact (sum_ti (ch_ti _ _ H1) (ch_ti _ _ H2)).
    - exact (sum_ri G1 G2 (ch_ri _ _ H1) (ch_ri _ _ H2)).
    - exact (sum_com G1 G2 (ch_com _ _ H1) (ch_com _ _ H2)).
  Qed.
End Sum.
