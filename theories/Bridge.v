(** * From §3 to §4: the algebra the calculus runs on

    Three links between the algebra of §3 (Twisted.v, EffectFun.v,
    Independence.v) and the calculus of §4.

    1. §3.1 read up to ≃, partially (Lemma 38, Definition 36). An effect
       function may fail where a precondition does not hold (the [Maybe]
       reading of Definition 19). [PWitnessed]: the inverse returns, up to
       ≃, to where the effect was applied, and everything respects ≃. It is
       closed under ⋄ ([pdiamond_witnessed], Theorem 11) and under the
       composition by outcome of Definition 30 ([pbind_witnessed], equation
       (36)). With ≃ the equality and total functions, it is Definition 8
       ([witnessed_total_iff], [pdiamond_total]).

    2. The calculus's programs as §3 effect functions ([denote]): an
       operation is the lift of equation (31), a provision the [set] of
       Definition 20, and a program the composite of Definition 30. Every
       program denotes a witnessed effect function on the store
       ([denote_witnessed]): unloading a component, by itself, recovers the
       store up to ≃. Operations at distinct keys are independent
       ([distinct_keys], Theorem 45).

    3. Definition 44 (key commutativity) implies the calculus's hypotheses:
       revert-independence and commutation ([paper_revert_indep],
       [paper_commute]), hence the bundle [ConfHyps] the generic
       confluence theorem takes ([paper_confhyps]) and the hypothesis of
       recovery exactness ([paper_hind]). The theorems of §4 therefore hold
       under the paper's own assumption (Definition 46 makes every key
       commutative); the calculus asks for less (only pairs that may meet,
       at distinct tokens). *)

From Stdlib Require Import List PeanoNat RelationClasses.
From Cordis Require Import Prelude Twisted EffectFun Service Calculus Recovery ServiceSeq Compose.
Import ListNotations.

(** ** 1. Partial effect functions up to ≃ *)
Section Setoid.
  Context {Γ : Type} (eqv : Γ -> Γ -> Prop) {Heqv : Equivalence eqv}.
  Local Notation "x ≈ y" := (eqv x y) (at level 70, no associativity).

  (** 𝔈Γ read in [Maybe]: [None] where a precondition fails. *)
  Definition PEff : Type := Γ -> option (Γ * End Γ).

  Definition respectsR (g : End Γ) : Prop := forall x y, x ≈ y -> g x ≈ g y.
  Definition fun_eqR (g h : End Γ) : Prop := forall x, g x ≈ h x.

  Definition peq (r1 r2 : option (Γ * End Γ)) : Prop :=
    match r1, r2 with
    | None, None => True
    | Some (x, g), Some (y, h) => x ≈ y /\ fun_eqR g h
    | _, _ => False
    end.

  (** Definition 36, read in [Maybe]. *)
  Record PWitnessed (e : PEff) : Prop := {
    pw_witness : forall γ δ g, e γ = Some (δ, g) -> g δ ≈ γ;
    pw_inv : forall γ δ g, e γ = Some (δ, g) -> respectsR g;
    pw_resp : forall γ γ', γ ≈ γ' -> peq (e γ) (e γ')
  }.

  Definition peta : PEff := fun γ => Some (γ, id).

  Definition pdiamond (e1 e2 : PEff) : PEff :=
    fun γ => match e2 γ with
             | Some (δ, s) => match e1 δ with Some (ε, t) => Some (ε, s ∘ t) | None => None end
             | None => None
             end.

  Lemma peta_witnessed : PWitnessed peta.
  Proof.
    split.
    - intros γ δ g E; injection E as <- <-; reflexivity.
    - intros γ δ g E; injection E as <- <-; intros x y H; exact H.
    - intros γ γ' H; split; [exact H | intros x; reflexivity].
  Qed.

  (** Theorem 11, up to ≃. *)
  Theorem pdiamond_witnessed e1 e2 : PWitnessed e1 -> PWitnessed e2 -> PWitnessed (pdiamond e1 e2).
  Proof.
    intros W1 W2; split.
    - intros γ ε h E; unfold pdiamond in E.
      destruct (e2 γ) as [[δ s]|] eqn:E2; [|discriminate].
      destruct (e1 δ) as [[ε' t]|] eqn:E1; [|discriminate].
      injection E as <- <-; unfold comp.
      transitivity (s δ); [apply (pw_inv _ W2 _ _ _ E2); exact (pw_witness _ W1 _ _ _ E1)|].
      exact (pw_witness _ W2 _ _ _ E2).
    - intros γ ε h E; unfold pdiamond in E.
      destruct (e2 γ) as [[δ s]|] eqn:E2; [|discriminate].
      destruct (e1 δ) as [[ε' t]|] eqn:E1; [|discriminate].
      injection E as <- <-; intros x y H; unfold comp.
      apply (pw_inv _ W2 _ _ _ E2); apply (pw_inv _ W1 _ _ _ E1); exact H.
    - intros γ γ' H; unfold pdiamond.
      pose proof (pw_resp _ W2 γ γ' H) as R2.
      destruct (e2 γ) as [[δ s]|] eqn:E2, (e2 γ') as [[δ' s']|] eqn:E2'; cbn in R2;
        try contradiction; [|exact I].
      destruct R2 as [Hd Hs].
      pose proof (pw_resp _ W1 δ δ' Hd) as R1.
      destruct (e1 δ) as [[ε t]|] eqn:E1, (e1 δ') as [[ε' t']|] eqn:E1'; cbn in R1;
        try contradiction; cbn; [|exact I].
      destruct R1 as [He Ht]; split; [exact He|].
      intros x; unfold comp.
      transitivity (s (t' x)); [apply (pw_inv _ W2 _ _ _ E2); apply Ht | apply Hs].
  Qed.

  (** Composition by outcome (Definition 30, equation (32)): one stage
      yields an outcome, and the outcome chooses what follows. *)
  Definition pbind {B} (a : Γ -> option (Γ * End Γ * B)) (k : B -> PEff) : PEff :=
    fun γ => match a γ with
             | Some (δ, s, b) => match k b δ with Some (ε, t) => Some (ε, s ∘ t) | None => None end
             | None => None
             end.

  (** A stage with an outcome, witnessed and respecting ≃ (Definition 29). *)
  Record PWitnessedO {B} (a : Γ -> option (Γ * End Γ * B)) : Prop := {
    po_witness : forall γ δ g o, a γ = Some (δ, g, o) -> g δ ≈ γ;
    po_inv : forall γ δ g o, a γ = Some (δ, g, o) -> respectsR g;
    po_resp : forall γ γ', γ ≈ γ' ->
      match a γ, a γ' with
      | None, None => True
      | Some (x, g, o), Some (y, h, o') => x ≈ y /\ fun_eqR g h /\ o = o'
      | _, _ => False
      end
  }.

  Theorem pbind_witnessed {B} (a : Γ -> option (Γ * End Γ * B)) (k : B -> PEff) :
    PWitnessedO a -> (forall b, PWitnessed (k b)) -> PWitnessed (pbind a k).
  Proof.
    intros Wa Wk; split.
    - intros γ ε h E; unfold pbind in E.
      destruct (a γ) as [[[δ s] b]|] eqn:Ea; [|discriminate].
      destruct (k b δ) as [[ε' t]|] eqn:Ek; [|discriminate].
      injection E as <- <-; unfold comp.
      transitivity (s δ); [apply (po_inv _ Wa _ _ _ _ Ea); exact (pw_witness _ (Wk b) _ _ _ Ek)|].
      exact (po_witness _ Wa _ _ _ _ Ea).
    - intros γ ε h E; unfold pbind in E.
      destruct (a γ) as [[[δ s] b]|] eqn:Ea; [|discriminate].
      destruct (k b δ) as [[ε' t]|] eqn:Ek; [|discriminate].
      injection E as <- <-; intros x y H; unfold comp.
      apply (po_inv _ Wa _ _ _ _ Ea); apply (pw_inv _ (Wk b) _ _ _ Ek); exact H.
    - intros γ γ' H; unfold pbind.
      pose proof (po_resp _ Wa γ γ' H) as Ra.
      destruct (a γ) as [[[δ s] b]|] eqn:Ea, (a γ') as [[[δ' s'] b']|] eqn:Ea'; cbn in Ra;
        try contradiction; [|exact I].
      destruct Ra as (Hd & Hs & <-).
      pose proof (pw_resp _ (Wk b) δ δ' Hd) as R1.
      destruct (k b δ) as [[ε t]|] eqn:E1, (k b δ') as [[ε' t']|] eqn:E1'; cbn in R1;
        try contradiction; cbn; [|exact I].
      destruct R1 as [He Ht]; split; [exact He|].
      intros x; unfold comp.
      transitivity (s (t' x)); [apply (po_inv _ Wa _ _ _ _ Ea); apply Ht | apply Hs].
  Qed.

  (** A sequence, applied head first. *)
  Fixpoint pdiamonds (es : list PEff) : PEff :=
    match es with [] => peta | e :: es' => pdiamond (pdiamonds es') e end.

  Lemma pdiamonds_witnessed es : Forall PWitnessed es -> PWitnessed (pdiamonds es).
  Proof.
    induction 1 as [|e es He _ IH]; cbn; [exact peta_witnessed | exact (pdiamond_witnessed _ _ IH He)].
  Qed.
End Setoid.

Arguments PEff : clear implicits.

(** With ≃ the equality and no failure, the reading is Definition 8. *)
Definition ptotal {Γ : Type} (e : Eff Γ) : PEff Γ := fun γ => Some (e γ).

Lemma pdiamond_total {Γ : Type} (e1 e2 : Eff Γ) γ :
  pdiamond (ptotal e1) (ptotal e2) γ = ptotal (e1 ⋄ e2) γ.
Proof. unfold pdiamond, ptotal, diamond; destruct (e2 γ) as [δ s]; cbn; destruct (e1 δ); reflexivity. Qed.

Lemma witnessed_total_iff {Γ : Type} (e : Eff Γ) :
  PWitnessed (@eq Γ) (ptotal e) <-> EffectFun.Witnessed e.
Proof.
  split.
  - intros W γ; destruct (e γ) as [δ g] eqn:E.
    apply (pw_witness _ _ W γ δ g); unfold ptotal; rewrite E; reflexivity.
  - intros H; split.
    + intros γ δ g E; unfold ptotal in E; injection E as E; specialize (H γ); rewrite E in H; exact H.
    + intros γ δ g _ x y ->; reflexivity.
    + intros γ γ' ->; unfold ptotal; destruct (e γ'); split; [reflexivity | intros x; reflexivity].
Qed.

(** ** 2. Programs as effect functions on the store *)
Section Mediated.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type}.

  (** The coeffect context: a value at each bound key (Definition 19). *)
  Definition Store : Type := K -> option (St Σ).

  Definition seq_opt (o1 o2 : option (St Σ)) : Prop :=
    match o1, o2 with None, None => True | Some x, Some y => x ≃ y | _, _ => False end.

  Lemma seq_opt_refl o : seq_opt o o.
  Proof. destruct o; cbn; [reflexivity | exact I]. Qed.

  (** Definition 33: the same keys, bound to related values. *)
  Definition store_eq (σ σ' : Store) : Prop := forall k, seq_opt (σ k) (σ' k).

  Global Instance store_eq_equiv : Equivalence store_eq.
  Proof.
    split.
    - intros σ k; destruct (σ k); cbn; [reflexivity | exact I].
    - intros σ σ' H k; specialize (H k); destruct (σ k), (σ' k); cbn in *; try contradiction; auto.
      symmetry; exact H.
    - intros σ1 σ2 σ3 H12 H23 k; specialize (H12 k); specialize (H23 k).
      destruct (σ1 k), (σ2 k), (σ3 k); cbn in *; try contradiction; auto.
      transitivity s0; assumption.
  Qed.

  Definition supd (σ : Store) (k : K) (v : option (St Σ)) : Store :=
    fun k' => if K_eq_dec k' k then v else σ k'.

  Lemma supd_same σ k v : supd σ k v k = v.
  Proof. unfold supd; destruct (K_eq_dec k k); [reflexivity | contradiction]. Qed.

  Lemma supd_other σ k v j : j <> k -> supd σ k v j = σ j.
  Proof. intros H; unfold supd; destruct (K_eq_dec j k); [contradiction | reflexivity]. Qed.

  (** The lift of an operation at [k] (equation (31)): it reads and writes
      the binding at [k] alone. *)
  Definition oplift (k : K) (a : Op Σ) (t : nat) (σ : Store) : option (Store * End Store * Out Σ) :=
    match σ k with
    | Some v =>
        match run a t v with
        | Some (v', g, o) => Some (supd σ k (Some v'), (fun σ' => supd σ' k (option_map g (σ' k))), o)
        | None => None
        end
    | None => None
    end.

  (** [set] of Definition 20: defined where [k] is unbound; the inverse
      restricts. *)
  Definition setk (k : K) (s : St Σ) (σ : Store) : option (Store * End Store) :=
    match σ k with
    | None => Some (supd σ k (Some s), fun σ' => supd σ' k None)
    | Some _ => None
    end.

  (** ⟦P⟧: a program read as the composite of Definition 30. As in the
      calculus, every operation, provision and spawn draws the next number
      from [t]: an operation uses it as its token. Registering a child is
      not a store effect (Definition 52), so a spawn denotes nothing here
      beyond the number it draws. *)
  Fixpoint denote (P : @Prog K Σ C) (t : nat) : PEff Store :=
    match P with
    | PDone => peta
    | PFail => fun _ => None
    | POp k a κ => pbind (oplift k a t) (fun o => denote (κ o) (Datatypes.S t))
    | PProvide k s P' => pdiamond (denote P' (Datatypes.S t)) (setk k s)
    | PSpawn _ P' => denote P' (Datatypes.S t)
    end.

  Lemma oplift_witnessed k a t : WellBehaved (Σ := Σ) a t -> PWitnessedO store_eq (oplift k a t).
  Proof.
    intros Wb; split.
    - intros σ δ g o E; unfold oplift in E.
      destruct (σ k) as [v|] eqn:Ek; [|discriminate].
      destruct (run a t v) as [[[v' g'] o']|] eqn:Er; [|discriminate].
      injection E as <- <- <-; intros j.
      destruct (K_eq_dec j k) as [->|Hne].
      + rewrite !supd_same, Ek; cbn; exact (wb_witness _ _ Wb _ _ _ _ Er).
      + rewrite !supd_other by exact Hne; apply seq_opt_refl.
    - intros σ δ g o E; unfold oplift in E.
      destruct (σ k) as [v|] eqn:Ek; [|discriminate].
      destruct (run a t v) as [[[v' g'] o']|] eqn:Er; [|discriminate].
      injection E as <- <- <-; intros σ1 σ2 H j.
      destruct (K_eq_dec j k) as [->|Hne].
      + rewrite !supd_same; specialize (H k); destruct (σ1 k), (σ2 k); cbn in *; try contradiction; auto.
        exact (wb_inv _ _ Wb _ _ _ _ Er _ _ H).
      + rewrite !supd_other by exact Hne; exact (H j).
    - intros σ σ' H; unfold oplift.
      pose proof (H k) as Hk.
      destruct (σ k) as [v|], (σ' k) as [v2|]; cbn in Hk; try contradiction; [|exact I].
      pose proof (wb_respects _ _ Wb v v2 Hk) as R.
      destruct (run a t v) as [[[x1 g1] o1]|], (run a t v2) as [[[x2 g2] o2]|]; cbn in R;
        try contradiction; [|exact I].
      destruct R as (Hx & Hg & Ho); split; [|split; [|exact Ho]].
      + intros j; destruct (K_eq_dec j k) as [->|Hne]; [rewrite !supd_same; exact Hx|].
        rewrite !supd_other by exact Hne; exact (H j).
      + intros σ'' j; destruct (K_eq_dec j k) as [->|Hne].
        * rewrite !supd_same; destruct (σ'' k); cbn; [exact (Hg _) | exact I].
        * rewrite !supd_other by exact Hne; apply seq_opt_refl.
  Qed.

  Lemma setk_witnessed k s : PWitnessed store_eq (setk k s).
  Proof.
    split.
    - intros σ δ g E; unfold setk in E; destruct (σ k) eqn:Ek; [discriminate|].
      injection E as <- <-; intros j.
      destruct (K_eq_dec j k) as [->|Hne]; [rewrite supd_same, Ek; exact I|].
      rewrite !supd_other by exact Hne; apply seq_opt_refl.
    - intros σ δ g E; unfold setk in E; destruct (σ k); [discriminate|].
      injection E as <- <-; intros σ1 σ2 H j.
      destruct (K_eq_dec j k) as [->|Hne]; [rewrite !supd_same; exact I|].
      rewrite !supd_other by exact Hne; exact (H j).
    - intros σ σ' H; unfold setk; pose proof (H k) as Hk.
      destruct (σ k), (σ' k); cbn in Hk; try contradiction; cbn; [exact I|].
      split; [|intros σ'' j; apply seq_opt_refl].
      intros j; destruct (K_eq_dec j k) as [->|Hne]; [rewrite !supd_same; apply seq_opt_refl|].
      rewrite !supd_other by exact Hne; exact (H j).
  Qed.

  (** Every program denotes a witnessed effect function: run by itself and
      then reverted, a component leaves the store as it found it, up to ≃
      (Theorems 11 and 16 with Lemma 38, for Definition 30). *)
  Theorem denote_witnessed :
    (forall a t, WellBehaved (Σ := Σ) a t) ->
    forall P t, PWitnessed store_eq (denote P t).
  Proof.
    intros Hwb P; induction P as [| |k a κ IH|k s P IH|c P IH]; intros t; cbn [denote].
    - exact (peta_witnessed store_eq).
    - split; [intros; discriminate | intros; discriminate | intros γ γ' _; exact I].
    - exact (pbind_witnessed store_eq _ _ (oplift_witnessed k a t (Hwb a t)) (fun o => IH o _)).
    - exact (pdiamond_witnessed store_eq _ _ (IH _) (setk_witnessed k s)).
    - exact (IH _).
  Qed.

  Lemma store_eq_ext (σ σ' : Store) : (forall j, σ j = σ' j) -> store_eq σ σ'.
  Proof. intros H j; rewrite H; apply seq_opt_refl. Qed.

  (** *** Theorem 45: operations at distinct keys are independent

      A map is local to [k] when it changes no other key and its value at
      [k] depends on the value at [k] alone. The forward map and every
      inverse of an operation at [k] are local to [k]; maps local to
      distinct keys commute, and a map local to [k'] disturbs neither the
      definedness, the inverse, nor the outcome of an operation at [k]. *)
  Definition LocalAt (k : K) (f : End Store) : Prop :=
    (forall σ j, j <> k -> f σ j = σ j) /\ (forall σ σ', σ k = σ' k -> f σ k = f σ' k).

  (** The forward map, total: where the operation fails it stays put. *)
  Definition opfwd (k : K) (a : Op Σ) (t : nat) (σ : Store) : Store :=
    match oplift k a t σ with Some (σ', _, _) => σ' | None => σ end.

  Lemma opfwd_at k a t τ :
    opfwd k a t τ k =
      match τ k with
      | Some v => match run a t v with Some (v', _, _) => Some v' | None => Some v end
      | None => None
      end.
  Proof.
    unfold opfwd, oplift; destruct (τ k) as [v|] eqn:E; [|exact E].
    destruct (run a t v) as [[[v' g] o]|]; [apply supd_same | exact E].
  Qed.

  Lemma opfwd_local k a t : LocalAt k (opfwd k a t).
  Proof.
    split.
    - unfold opfwd, oplift; intros σ j Hne; destruct (σ k) as [v|]; [|reflexivity].
      destruct (run a t v) as [[[v' g] o]|]; [exact (supd_other _ _ _ _ Hne) | reflexivity].
    - intros σ σ' E; rewrite !opfwd_at, E; reflexivity.
  Qed.

  Lemma opinv_local k a t σ σ' g o :
    oplift k a t σ = Some (σ', g, o) -> LocalAt k g.
  Proof.
    unfold oplift; intros E; destruct (σ k) as [v|]; [|discriminate].
    destruct (run a t v) as [[[v' g'] o']|]; [|discriminate]; injection E as _ <- _; split.
    - intros σ1 j Hne; exact (supd_other _ _ _ _ Hne).
    - intros σ1 σ2 Eq; rewrite !supd_same, Eq; reflexivity.
  Qed.

  Lemma local_commute k k' f g : k <> k' -> LocalAt k f -> LocalAt k' g ->
    forall σ j, f (g σ) j = g (f σ) j.
  Proof.
    intros Hk [Fo Fk] [Go Gk] σ j.
    destruct (K_eq_dec j k) as [->|Hj].
    - rewrite (Go (f σ) k Hk); apply Fk; exact (Go σ k Hk).
    - destruct (K_eq_dec j k') as [->|Hj'].
      + rewrite (Fo (g σ) k' Hj); symmetry; apply Gk; exact (Fo σ k' Hj).
      + rewrite (Fo _ j Hj), (Go _ j Hj'), (Go _ j Hj'), (Fo _ j Hj); reflexivity.
  Qed.

  Lemma oplift_shift k k' a t f : k <> k' -> LocalAt k' f -> forall σ,
    match oplift k a t σ, oplift k a t (f σ) with
    | None, None => True
    | Some (σ1, g, o), Some (σ2, h, o') => (forall j, σ2 j = f σ1 j) /\ g = h /\ o = o'
    | _, _ => False
    end.
  Proof.
    intros Hk [Fo Fk] σ; unfold oplift.
    rewrite (Fo σ k Hk); destruct (σ k) as [v|] eqn:Ev; [|exact I].
    destruct (run a t v) as [[[v' g] o]|]; [|exact I].
    split; [|split; reflexivity]; intros j.
    destruct (K_eq_dec j k) as [->|Hj].
    - rewrite supd_same, (Fo _ k Hk), supd_same; reflexivity.
    - rewrite (supd_other _ _ _ _ Hj).
      destruct (K_eq_dec j k') as [->|Hj'].
      + apply Fk; rewrite (supd_other _ _ _ _ Hj); reflexivity.
      + rewrite (Fo _ j Hj'), (Fo _ j Hj'), (supd_other _ _ _ _ Hj); reflexivity.
  Qed.

  Theorem distinct_keys k k' a b ta tb : k <> k' ->
    (* the generators of the two operations commute *)
    (forall f g, LocalAt k f -> LocalAt k' g -> forall σ j, f (g σ) j = g (f σ) j) /\
    LocalAt k (opfwd k a ta) /\ LocalAt k' (opfwd k' b tb) /\
    (forall σ σ' g o, oplift k a ta σ = Some (σ', g, o) -> LocalAt k g) /\
    (forall σ σ' g o, oplift k' b tb σ = Some (σ', g, o) -> LocalAt k' g) /\
    (* and neither disturbs what the other yields *)
    (forall f σ, LocalAt k' f ->
       match oplift k a ta σ, oplift k a ta (f σ) with
       | None, None => True
       | Some (σ1, g, o), Some (σ2, h, o') => (forall j, σ2 j = f σ1 j) /\ g = h /\ o = o'
       | _, _ => False
       end) /\
    (forall f σ, LocalAt k f ->
       match oplift k' b tb σ, oplift k' b tb (f σ) with
       | None, None => True
       | Some (σ1, g, o), Some (σ2, h, o') => (forall j, σ2 j = f σ1 j) /\ g = h /\ o = o'
       | _, _ => False
       end).
  Proof.
    intros Hk; split; [intros f g Hf Hg; exact (local_commute k k' f g Hk Hf Hg)|].
    split; [apply opfwd_local|]; split; [apply opfwd_local|].
    split; [intros σ σ' g o; apply opinv_local|]; split; [intros σ σ' g o; apply opinv_local|].
    split; [intros f σ Hf; exact (oplift_shift k k' a ta f Hk Hf σ)|].
    intros f σ Hf; exact (oplift_shift k' k b tb f (not_eq_sym Hk) Hf σ).
  Qed.
End Mediated.

(** ** 3. Key commutativity (Definition 44) implies the calculus's hypotheses *)
Section KeyCommutative.
  Context {Σ : Service}.
  Local Notation V := (St Σ).

  (** Operations act on the value at their key alone, so their lifts at one
      key are independent exactly when they are as maps on values. The
      generators of an operation (Definition 40) are its forward map and
      the inverses it yields; in the [Maybe] reading the forward map is
      partial. *)
  Definition fwdp (a : Op Σ) (t : nat) (x : V) : option V :=
    match run a t x with Some (x', _, _) => Some x' | None => None end.

  Definition oeq (o1 o2 : option V) : Prop :=
    match o1, o2 with None, None => True | Some x, Some y => x ≃ y | _, _ => False end.

  Definition obind (p : V -> option V) (o : option V) : option V :=
    match o with Some x => p x | None => None end.

  (** Two partial maps commute: both composites defined or neither, and
      related where defined. *)
  Definition PComm (p q : V -> option V) : Prop := forall x, oeq (obind p (q x)) (obind q (p x)).

  Definition GenOf (a : Op Σ) (t : nat) (p : V -> option V) : Prop :=
    (forall x, p x = fwdp a t x) \/ (exists g, yields (Σ := Σ) a t g /\ forall x, p x = Some (g x)).

  (** A transformation [q] disturbs neither the definedness, the inverse,
      nor the outcome of [a] (equations (40) and (41)). *)
  Definition Undist (a : Op Σ) (t : nat) (q : V -> option V) : Prop :=
    forall x y, q x = Some y ->
      match run a t x, run a t y with
      | None, None => True
      | Some (_, g, o), Some (_, h, o') => fun_eq (Σ := Σ) g h /\ o = o'
      | _, _ => False
      end.

  (** Definition 44, for one pair of operations at their tokens. *)
  Definition PaperIndep (a : Op Σ) (ta : nat) (b : Op Σ) (tb : nat) : Prop :=
    (forall p q, GenOf a ta p -> GenOf b tb q -> PComm p q) /\
    (forall q, GenOf b tb q -> Undist a ta q) /\
    (forall p, GenOf a ta p -> Undist b tb p).

  Theorem paper_revert_indep a ta b tb : PaperIndep a ta b tb -> RevertIndep (Σ := Σ) a ta b tb.
  Proof.
    intros (Hc & Ua & Ub) g Hy.
    assert (GA : GenOf a ta (fun x => Some (g x))) by (right; exists g; split; [exact Hy | reflexivity]).
    assert (GB : GenOf b tb (fwdp b tb)) by (left; reflexivity).
    split.
    - intros x; pose proof (Ub _ GA x (g x) eq_refl) as U.
      pose proof (Hc _ _ GA GB x) as Cx; unfold obind, fwdp in Cx.
      unfold shifted.
      destruct (run b tb x) as [[[x1 h] o]|] eqn:E1, (run b tb (g x)) as [[[x2 h'] o']|] eqn:E2;
        cbn in U, Cx; try contradiction; [|exact I].
      destruct U as [Hh Ho]; split; [symmetry; exact Cx|]; split; [intros z; symmetry; apply Hh | auto].
    - intros h z Hyh.
      assert (GB' : GenOf b tb (fun x => Some (h x))) by (right; exists h; split; [exact Hyh | reflexivity]).
      exact (Hc _ _ GA GB' z).
  Qed.

  Theorem paper_commute a ta b tb : PaperIndep a ta b tb -> Commute (Σ := Σ) a ta b tb.
  Proof.
    intros (Hc & Ua & Ub) s.
    assert (GA : GenOf a ta (fwdp a ta)) by (left; reflexivity).
    assert (GB : GenOf b tb (fwdp b tb)) by (left; reflexivity).
    pose proof (Hc _ _ GA GB s) as Cs.
    unfold seq2.
    destruct (run a ta s) as [[[s1 ga] oa]|] eqn:Ea, (run b tb s) as [[[s1' gb] ob]|] eqn:Eb.
    - pose proof (Ub _ GA s s1 ltac:(unfold fwdp; rewrite Ea; reflexivity)) as U1; rewrite Eb in U1.
      pose proof (Ua _ GB s s1' ltac:(unfold fwdp; rewrite Eb; reflexivity)) as U2; rewrite Ea in U2.
      unfold obind, fwdp in Cs; rewrite Ea, Eb in Cs.
      destruct (run b tb s1) as [[[s2 g2] ob2]|], (run a ta s1') as [[[s2' g2'] oa2]|];
        cbn in U1, U2, Cs; try contradiction.
      destruct U1 as [_ Ho1]; destruct U2 as [_ Ho2]; split; [symmetry; exact Cs | split; congruence].
    - pose proof (Ub _ GA s s1 ltac:(unfold fwdp; rewrite Ea; reflexivity)) as U1; rewrite Eb in U1.
      destruct (run b tb s1); [contradiction | exact I].
    - pose proof (Ua _ GB s s1' ltac:(unfold fwdp; rewrite Eb; reflexivity)) as U2; rewrite Ea in U2.
      destruct (run a ta s1'); [contradiction | exact I].
    - exact I.
  Qed.

  (** The bundle the generic confluence theorem takes, from Definition 44 on
      the pairs that may meet, together with well-behavedness, uniform
      inverses, and token irrelevance. *)
  Corollary paper_confhyps (G : Op Σ -> Op Σ -> Prop) :
    (forall a t, WellBehaved (Σ := Σ) a t) -> UniformInv Σ -> TokIrr Σ ->
    (forall a b ta tb, G a b -> ta <> tb -> PaperIndep a ta b tb) ->
    ConfHyps Σ G.
  Proof.
    intros Hwb HUI HTI HP; split; [exact Hwb | exact HUI | exact HTI | |].
    - intros a b ta tb g Hab Ht Hy x HA.
      exact (revert_indep_after (G a) a ta b tb g (paper_revert_indep _ _ _ _ (HP a b ta tb Hab Ht)) Hy x HA).
    - intros a b ta tb Hab Ht; exact (paper_commute _ _ _ _ (HP a b ta tb Hab Ht)).
  Qed.
End KeyCommutative.

(** The hypothesis of recovery exactness ([Recovery.Hind]), from
    Definition 44 on the pairs two fibers may perform at one key. *)
Corollary paper_hind {K : Type} {Σ : Service} {C : Type} (prog : C -> @Component K Σ C) :
  (forall k a b ta tb, CoPair Σ prog k a b -> ta <> tb -> PaperIndep a ta b tb) ->
  forall k a b ta tb, CoPair Σ prog k a b -> ta <> tb -> RevertIndep (Σ := Σ) a ta b tb.
Proof. intros H k a b ta tb Hc Ht; exact (paper_revert_indep _ _ _ _ (H k a b ta tb Hc Ht)). Qed.

(** ** 4. ⟦·⟧ commutes with the calculus's steps

    Read through its store ([cstore]: the service state at each bound key),
    a step of the calculus performs one stage of [denote]: an [L-Step] at
    an operation applies the lift [oplift] and records, as its undo item,
    the inverse the lift yields; an [L-Step] at a provision applies [setk];
    and an [L-Undo] of that item applies the same inverse while the
    binding it was taken on is still there. The calculus's accumulator is
    therefore the composite inverse of §3.1, run item by item in LIFO
    order. Assembled over a whole activation ([lone_denote]): a fiber that
    loads by itself to Active takes the store where [denote] takes it, and
    the items it adds compose ([uinterp]) to the inverse [denote] yields,
    up to ≃. *)
Section Steps.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).
  Local Notation State := (@State K Σ C).

  Definition cstore (γ : State) : @Store K Σ := fun k => option_map (bst Σ) (binds Σ γ k).

  Lemma op_stage (γ : State) m f k a κ acc w b s' g o :
    op_binding K_eq_dec Σ prog γ m f k w = Some b -> run a (next Σ γ) (bst Σ b) = Some (s', g, o) ->
    exists σ' gl, oplift K_eq_dec Σ k a (next Σ γ) (cstore γ) = Some (σ', gl, o) /\
      (forall j, cstore (load_step K_eq_dec Σ prog γ m f (POp k a κ) acc w) j = σ' j) /\
      (forall τ, gl τ = supd K_eq_dec Σ τ k (option_map g (τ k))).
  Proof.
    intros Hb Hr.
    pose proof (op_binding_spec K_eq_dec Σ prog γ m f k w b Hb) as Hbk.
    assert (Ck : cstore γ k = Some (bst Σ b)) by (unfold cstore; rewrite Hbk; reflexivity).
    rewrite (load_step_op K_eq_dec Σ prog γ m f k a κ acc w), Hb, Hr.
    unfold oplift; rewrite Ck, Hr.
    eexists _, _; split; [reflexivity|]; split; [|reflexivity].
    intros j; unfold cstore, supd, bupd, keqb; cbn.
    destruct (K_eq_dec j k); reflexivity.
  Qed.

  Lemma op_undo (γ γ' : State) n f k p t g acc w z :
    undo_step K_eq_dec Σ γ n f (UOp Σ k p t g) acc w z = Some γ' ->
    forall j, cstore γ' j =
      (match binds Σ γ k with
       | Some b => if Nat.eqb (pid Σ b) p then supd K_eq_dec Σ (cstore γ) k (option_map g (cstore γ k))
                   else cstore γ
       | None => cstore γ
       end) j.
  Proof.
    cbn [undo_step]; destruct (binds Σ γ k) as [b|] eqn:Hb; [destruct (Nat.eqb (pid Σ b) p)|];
      intros [= <-] j; [|reflexivity | reflexivity].
    unfold cstore, supd, bupd, keqb; cbn.
    destruct (K_eq_dec j k) as [->|]; [rewrite Hb; reflexivity | reflexivity].
  Qed.

  Lemma prov_stage (γ : State) m f k s P acc w :
    kmem K_eq_dec k (provs Σ (prog (Calculus.comp Σ f))) = true -> binds Σ γ k = None ->
    exists σ' gl, setk K_eq_dec Σ k s (cstore γ) = Some (σ', gl) /\
      (forall j, cstore (load_step K_eq_dec Σ prog γ m f (PProvide k s P) acc w) j = σ' j) /\
      (forall τ, gl τ = supd K_eq_dec Σ τ k None).
  Proof.
    intros Hk Hbk.
    assert (Ck : cstore γ k = None) by (unfold cstore; rewrite Hbk; reflexivity).
    cbn [load_step]; rewrite Hk, Hbk.
    unfold setk; rewrite Ck.
    eexists _, _; split; [reflexivity|]; split; [|reflexivity].
    intros j; unfold cstore, supd, bupd, keqb; cbn.
    destruct (K_eq_dec j k); reflexivity.
  Qed.

  Lemma prov_undo (γ γ' : State) n f k p acc w z :
    undo_step K_eq_dec Σ γ n f (UProv Σ k p) acc w z = Some γ' ->
    forall j, cstore γ' j =
      (match binds Σ γ k with
       | Some b => if Nat.eqb (pid Σ b) p then supd K_eq_dec Σ (cstore γ) k None else cstore γ
       | None => cstore γ
       end) j.
  Proof.
    cbn [undo_step]; destruct (relied Σ γ n p); [discriminate|].
    destruct (binds Σ γ k) as [b|] eqn:Hb; [destruct (Nat.eqb (pid Σ b) p)|];
      intros [= <-] j; [|reflexivity | reflexivity].
    unfold cstore, supd, bupd, keqb; cbn.
    destruct (K_eq_dec j k); reflexivity.
  Qed.

  (** *** A whole activation

      The undo items read as maps on the store, and an accumulator as their
      composite in LIFO order: the head, the newest item, runs first. *)
  Definition uitem (u : @Undo K Σ) : End (@Store K Σ) :=
    match u with
    | UOp _ k _ _ g => fun τ => supd K_eq_dec Σ τ k (option_map g (τ k))
    | UProv _ k _ => fun τ => supd K_eq_dec Σ τ k None
    | USpawn _ _ => fun τ => τ
    end.

  Fixpoint uinterp (l : list (@Undo K Σ)) : End (@Store K Σ) :=
    match l with [] => fun τ => τ | u :: l' => fun τ => uinterp l' (uitem u τ) end.

  Lemma uinterp_snoc l u τ : uinterp (l ++ [u]) τ = uitem u (uinterp l τ).
  Proof. revert τ; induction l as [|u' l IH]; intros τ; cbn; [reflexivity | apply IH]. Qed.

  (** Steps of one fiber alone. *)
  Inductive Lone (n : nat) : State -> State -> Prop :=
  | lone_nil γ : Lone n γ γ
  | lone_cons γ γ1 γ2 : step K_eq_dec Σ prog γ (LStep n) = Some γ1 -> Lone n γ1 γ2 -> Lone n γ γ2.

  Lemma lstep_shape (γ γ1 : State) n :
    step K_eq_dec Σ prog γ (LStep n) = Some γ1 ->
    exists f P acc w, fibers Σ γ n = Some f /\ life Σ f = Loading Σ P acc w /\
      γ1 = load_step K_eq_dec Σ prog γ n f P acc w.
  Proof.
    cbn [Calculus.step]; destruct (fibers Σ γ n) as [f|]; [|discriminate].
    destruct (life Σ f) as [|P acc w| |] eqn:Hl; try discriminate.
    destruct (target_is K_eq_dec Σ prog γ n w); [intros [= <-] | discriminate].
    exists f, P, acc, w; auto.
  Qed.

  Lemma set_life_at (γ : State) n f l :
    fibers Σ (set_life Σ γ n f l) n =
      Some (mkFiber Σ (Calculus.comp Σ f) (Calculus.parent Σ f) (Calculus.disposed Σ f) l).
  Proof. unfold set_life, set_fiber, with_fibers, fupd; cbn; rewrite Nat.eqb_refl; reflexivity. Qed.

  (** Once the fiber has left Loading, it takes no further step. *)
  Lemma lone_end (γ0 γ2 : State) n f l f' acc' w' :
    Lone n (set_life Σ γ0 n f l) γ2 -> (forall P a w, l <> Loading Σ P a w) ->
    fibers Σ γ2 n = Some f' -> life Σ f' = Active Σ acc' w' -> l = Active Σ acc' w'.
  Proof.
    intros R Hl H2 L2; inversion R as [γ E|γ γ1 γ3 Hs R' E1 E2]; subst.
    - rewrite set_life_at in H2; injection H2 as <-; exact L2.
    - destruct (lstep_shape _ _ _ Hs) as (f0 & P & acc & w & Hf0 & Hl0 & _).
      rewrite set_life_at in Hf0; injection Hf0 as <-; cbn in Hl0; exfalso; exact (Hl _ _ _ Hl0).
  Qed.

  (** A fiber that loads by itself, from [Loading P acc w] to Active, takes
      the store where [denote P] takes it, and the items it adds to its
      accumulator, read as maps on the store, compose to the inverse
      [denote P] yields; both up to ≃. *)
  Theorem lone_denote :
    (forall a t, WellBehaved (Σ := Σ) a t) ->
    forall n (γ γ' : State), Lone n γ γ' ->
    forall f P acc w f' acc' w',
      fibers Σ γ n = Some f -> life Σ f = Loading Σ P acc w ->
      fibers Σ γ' n = Some f' -> life Σ f' = Active Σ acc' w' ->
      exists σ' g, denote K_eq_dec Σ P (next Σ γ) (cstore γ) = Some (σ', g) /\
        store_eq Σ σ' (cstore γ') /\
        exists pre, acc' = pre ++ acc /\ fun_eqR (store_eq Σ) g (uinterp pre).
  Proof.
    intros Hwb n γ γ' R; induction R as [γ|γ γ1 γ2 Hs R IH];
      intros f P acc w f' acc' w' Hf Hl Hf' Hl'.
    { rewrite Hf in Hf'; injection Hf' as <-; congruence. }
    destruct (lstep_shape _ _ _ Hs) as (f0 & P0 & acc0 & w0 & Hf0 & Hl0 & ->).
    rewrite Hf in Hf0; injection Hf0 as <-; rewrite Hl in Hl0; injection Hl0 as <- <- <-.
    (* the inverse of a stage, composed with the inverse of the rest *)
    assert (Glue : forall (gs : End (@Store K Σ)) u g3 pre',
              respectsR (store_eq Σ) gs -> (forall τ, gs τ = uitem u τ) ->
              fun_eqR (store_eq Σ) g3 (uinterp pre') ->
              fun_eqR (store_eq Σ) (gs ∘ g3) (uinterp (pre' ++ [u]))).
    { intros gs u g3 pre' Rs Es H3 τ; unfold comp; rewrite uinterp_snoc, <- Es; apply Rs; apply H3. }
    destruct P as [| |k a κ|k s P'|c P'].
    - (* done *)
      cbn [load_step] in R.
      pose proof (lone_end _ _ _ _ _ _ _ _ R ltac:(intros ? ? ? E; discriminate) Hf' Hl') as E.
      injection E as <- <-.
      inversion R as [γ0 E1|γ0 γ3 γ4 Hs' _ E1 E2]; subst.
      + exists (cstore γ), (fun τ => τ); split; [reflexivity|]; split.
        * apply store_eq_ext; intros j; reflexivity.
        * exists []; split; [reflexivity | intros τ; reflexivity].
      + destruct (lstep_shape _ _ _ Hs') as (f0 & P & a0 & w0 & Hf0 & Hl0 & _).
        rewrite set_life_at in Hf0; injection Hf0 as <-; discriminate.
    - (* fail *)
      cbn [load_step] in R.
      pose proof (lone_end _ _ _ _ _ _ _ _ R ltac:(intros ? ? ? E; discriminate) Hf' Hl'); discriminate.
    - (* operation *)
      rewrite (load_step_op K_eq_dec Σ prog γ n f k a κ acc w) in R, IH.
      destruct (op_binding K_eq_dec Σ prog γ n f k w) as [b|] eqn:Hb;
        [|pose proof (lone_end _ _ _ _ _ _ _ _ R ltac:(intros ? ? ? E; discriminate) Hf' Hl'); discriminate].
      destruct (run a (next Σ γ) (bst Σ b)) as [[[s' g] o]|] eqn:Hr;
        [|pose proof (lone_end _ _ _ _ _ _ _ _ R ltac:(intros ? ? ? E; discriminate) Hf' Hl'); discriminate].
      destruct (IH _ _ _ _ _ _ _ (set_life_at _ _ _ _) eq_refl Hf' Hl') as (σ2 & g2 & D2 & S2 & pre' & Ea & G2).
      destruct (op_stage γ n f k a κ acc w b s' g o Hb Hr) as (σ1 & gl & Hop & Hσ1 & Hgl).
      rewrite (load_step_op K_eq_dec Σ prog γ n f k a κ acc w), Hb, Hr in Hσ1.
      cbn [denote]; unfold pbind; rewrite Hop.
      pose proof (pw_resp _ _ (denote_witnessed K_eq_dec Σ Hwb (κ o) (Datatypes.S (next Σ γ))) _ _
                    (store_eq_ext _ _ _ Hσ1)) as Rp.
      cbn [next set_life set_fiber with_fibers bump log_op with_binds Calculus.next] in D2.
      rewrite D2 in Rp.
      destruct (denote K_eq_dec Σ (κ o) (Datatypes.S (next Σ γ)) σ1) as [[σ3 g3]|]; cbn in Rp; [|contradiction].
      destruct Rp as [S3 G3].
      exists σ3, (gl ∘ g3); split; [reflexivity|]; split; [etransitivity; [symmetry; exact S3 | exact S2]|].
      exists (pre' ++ [UOp Σ k (pid Σ b) (next Σ γ) g]); split; [rewrite Ea, <- app_assoc; reflexivity|].
      apply Glue; [exact (po_inv _ _ (oplift_witnessed K_eq_dec Σ k a _ (Hwb a _)) _ _ _ _ Hop) | exact Hgl |].
      intros τ; transitivity (g2 τ); [symmetry; apply G3 | apply G2].
    - (* provision *)
      cbn [load_step] in R, IH.
      destruct (kmem K_eq_dec k (provs Σ (prog (Calculus.comp Σ f)))) eqn:Hk;
        [|pose proof (lone_end _ _ _ _ _ _ _ _ R ltac:(intros ? ? ? E; discriminate) Hf' Hl'); discriminate].
      destruct (binds Σ γ k) as [b|] eqn:Hbk;
        [pose proof (lone_end _ _ _ _ _ _ _ _ R ltac:(intros ? ? ? E; discriminate) Hf' Hl'); discriminate|].
      destruct (IH _ _ _ _ _ _ _ (set_life_at _ _ _ _) eq_refl Hf' Hl') as (σ2 & g2 & D2 & S2 & pre' & Ea & G2).
      destruct (prov_stage γ n f k s P' acc w Hk Hbk) as (σ1 & gs & Hst & Hσ1 & Hgs).
      cbn [load_step] in Hσ1; rewrite Hk, Hbk in Hσ1.
      cbn [denote]; unfold pdiamond; rewrite Hst.
      pose proof (pw_resp _ _ (denote_witnessed K_eq_dec Σ Hwb P' (Datatypes.S (next Σ γ))) _ _
                    (store_eq_ext _ _ _ Hσ1)) as Rp.
      cbn [next set_life set_fiber with_fibers bump log_ini with_binds Calculus.next] in D2.
      rewrite D2 in Rp.
      destruct (denote K_eq_dec Σ P' (Datatypes.S (next Σ γ)) σ1) as [[σ3 g3]|]; cbn in Rp; [|contradiction].
      destruct Rp as [S3 G3].
      exists σ3, (gs ∘ g3); split; [reflexivity|]; split; [etransitivity; [symmetry; exact S3 | exact S2]|].
      exists (pre' ++ [UProv Σ k (next Σ γ)]); split; [rewrite Ea, <- app_assoc; reflexivity|].
      apply Glue; [exact (pw_inv _ _ (setk_witnessed K_eq_dec Σ k s) _ _ _ Hst) | exact Hgs |].
      intros τ; transitivity (g2 τ); [symmetry; apply G3 | apply G2].
    - (* spawn *)
      cbn [load_step] in R, IH.
      destruct (conflict K_eq_dec Σ prog γ c) eqn:Hc;
        [pose proof (lone_end _ _ _ _ _ _ _ _ R ltac:(intros ? ? ? E; discriminate) Hf' Hl'); discriminate|].
      destruct (IH _ _ _ _ _ _ _ (set_life_at _ _ _ _) eq_refl Hf' Hl') as (σ2 & g2 & D2 & S2 & pre' & Ea & G2).
      (* a spawn leaves the bindings as they are *)
      cbn [denote]; exists σ2, g2; split; [exact D2|]; split; [exact S2|].
      exists (pre' ++ [USpawn Σ (next Σ γ)]); split; [rewrite Ea, <- app_assoc; reflexivity|].
      intros τ; rewrite uinterp_snoc; cbn [uitem]; apply G2.
  Qed.
End Steps.
