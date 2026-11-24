(** * Recovery exactness (R3, third part)

    Counterpart of the paper's Theorem 68 and Corollary 69.

    Fix a fiber [n]. Along an execution, maintain a shadow store: every
    other fiber's operations and undos are applied to it, and every binding
    is created and removed as in the real store, but [n]'s own operations
    and undos are skipped. The invariant: for every key, applying [n]'s
    pending inverses on that binding (last in, first out) to the real state
    gives, up to ≃, the shadow state. Once [n] holds no pending operation
    (for instance after it unloaded), the real store agrees with the
    shadow: [n] withdrew its own contribution and nothing else.

    Hypotheses: every operation is well behaved, and any two operations
    that components may perform, under distinct tokens, are
    revert-independent (Service.v). *)

From Stdlib Require Import List PeanoNat Bool Lia RelationClasses.
From Cordis Require Import Prelude Service Calculus Preservation Ordering.
Import ListNotations.

Section Recovery.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).
  Local Notation Fiber := (@Fiber K Σ C).
  Local Notation Life := (@Life K Σ C).
  Local Notation Undo := (@Undo K Σ).
  Local Notation Prog := (@Prog K Σ C).
  Local Notation S := (St Σ).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation next := (next Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation view_of := (view_of Σ).
  Local Notation acc_of := (acc_of Σ).
  Local Notation pid := (pid Σ).
  Local Notation owner := (owner Σ).
  Local Notation bst := (bst Σ).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation WF := (WF K_eq_dec Σ prog).
  Local Notation cbody c := (body Σ (prog c)).

  (** ** Operations a program may perform, and residual programs *)
  Inductive OpIn (a : Op Σ) : Prog -> Prop :=
  | op_here k κ : OpIn a (POp k a κ)
  | op_cont k b κ o : OpIn a (κ o) -> OpIn a (POp k b κ)
  | op_prov k s P : OpIn a P -> OpIn a (PProvide k s P)
  | op_spawn c P : OpIn a P -> OpIn a (PSpawn c P).

  (** [OpAt k a P]: [P] may perform [a] at key [k]. *)
  Inductive OpAt (k : K) (a : Op Σ) : Prog -> Prop :=
  | at_here κ : OpAt k a (POp k a κ)
  | at_cont k' b κ o : OpAt k a (κ o) -> OpAt k a (POp k' b κ)
  | at_prov k' s P : OpAt k a P -> OpAt k a (PProvide k' s P)
  | at_spawn c P : OpAt k a P -> OpAt k a (PSpawn c P).

  Lemma OpAt_OpIn k a P : OpAt k a P -> OpIn a P.
  Proof.
    intros H; induction H.
    - apply op_here.
    - eapply op_cont; eauto.
    - apply op_prov; auto.
    - apply op_spawn; auto.
  Qed.

  (** [Sub P Q]: [P] is what remains of [Q] after some steps. *)
  Inductive Sub : Prog -> Prog -> Prop :=
  | sub_refl P : Sub P P
  | sub_op P k a κ o : Sub P (κ o) -> Sub P (POp k a κ)
  | sub_prov P k s Q : Sub P Q -> Sub P (PProvide k s Q)
  | sub_spawn P c Q : Sub P Q -> Sub P (PSpawn c Q).

  Lemma Sub_trans P Q R : Sub P Q -> Sub Q R -> Sub P R.
  Proof.
    intros H1 H2; revert H1; induction H2; intros H1.
    - exact H1.
    - eapply sub_op; eauto.
    - apply sub_prov; auto.
    - apply sub_spawn; auto.
  Qed.

  Lemma Sub_OpAt k a P Q : Sub P Q -> OpAt k a P -> OpAt k a Q.
  Proof.
    intros HS HO; induction HS.
    - exact HO.
    - eapply at_cont; exact (IHHS HO).
    - apply at_prov; exact (IHHS HO).
    - apply at_spawn; exact (IHHS HO).
  Qed.

  (** Two operations at one key that two fibers may perform: from two
      components, or from one component that may run in several fibers
      (it provides nothing, so nothing keeps it to one fiber). *)
  Definition CoPair (k : K) (a b : Op Σ) : Prop :=
    exists c c', OpAt k a (cbody c) /\ OpAt k b (cbody c') /\ (c = c' -> provs Σ (prog c) = []).

  Lemma CoPair_sym k a b : CoPair k a b -> CoPair k b a.
  Proof.
    intros (c & c' & H1 & H2 & H3); exists c', c; split; [exact H2|]; split; [exact H1|].
    intros E; subst c'; exact (H3 eq_refl).
  Qed.

  Lemma overlaps_self (l : list K) : overlaps K_eq_dec l l = false -> l = [].
  Proof.
    destruct l as [|k l]; [reflexivity|]; intros H; exfalso.
    unfold overlaps, kmem, keqb in H; cbn in H.
    destruct (K_eq_dec k k); [cbn in H; discriminate | contradiction].
  Qed.

  (** Operations of two present fibers at one key may meet. *)
  Lemma copair_wf (γ : State) m fm m' fm' k a b :
    WF γ -> m <> m' -> fibers γ m = Some fm -> fibers γ m' = Some fm' ->
    OpAt k a (cbody (fcomp fm)) -> OpAt k b (cbody (fcomp fm')) -> CoPair k a b.
  Proof.
    intros W Hne Hm Hm' Ha Hb; exists (fcomp fm), (fcomp fm'); split; [exact Ha|]; split; [exact Hb|].
    intros E; apply overlaps_self.
    pose proof (wf_disjoint K_eq_dec Σ prog γ W m m' fm fm' Hne Hm Hm') as D.
    unfold fprovs in D; rewrite <- E in D; exact D.
  Qed.

  Lemma OpIn_Sub a P Q : Sub P Q -> OpIn a P -> OpIn a Q.
  Proof.
    intros HS; induction HS; intros HO.
    - exact HO.
    - eapply op_cont; eauto.
    - apply op_prov; auto.
    - apply op_spawn; auto.
  Qed.

  (** ** Provenance *)
  Definition ProvF (N : nat) (f : Fiber) : Prop :=
    (forall P acc w, life f = Loading Σ P acc w -> Sub P (cbody (fcomp f))) /\
    (forall k p t g, In (UOp Σ k p t g) (acc_of (life f)) ->
       p < N /\ t < N /\
       exists a s s' o, OpAt k a (cbody (fcomp f)) /\ run a t s = Some (s', g, o)).

  (** Distinct fibers hold no operation undo item under a common token. *)
  Definition TokDistinct (γ : State) : Prop :=
    forall m1 m2 f1 f2 k1 p1 g1 k2 p2 g2 t,
      m1 <> m2 -> fibers γ m1 = Some f1 -> fibers γ m2 = Some f2 ->
      In (UOp Σ k1 p1 t g1) (acc_of (life f1)) ->
      In (UOp Σ k2 p2 t g2) (acc_of (life f2)) -> False.

  Record Prov (γ : State) : Prop := {
    pv_fib : forall m f, fibers γ m = Some f -> ProvF (next γ) f;
    pv_tok : TokDistinct γ
  }.

  Lemma ProvF_mono N N' f : N <= N' -> ProvF N f -> ProvF N' f.
  Proof.
    intros HN [H1 H2]; split; [exact H1|].
    intros k p t g Hin; destruct (H2 k p t g Hin) as (Hp & Ht & Hx); repeat split; auto; lia.
  Qed.

  Lemma ProvF_inactive N f z : life f = Inactive Σ z -> ProvF N f.
  Proof. intros Hl; split; rewrite Hl; [discriminate | intros k p t g []]. Qed.

  Lemma prov_init : Prov (@init K Σ C).
  Proof. split; cbn; [discriminate | intros; discriminate]. Qed.

  (** A step that keeps or adds Inactive fibers and replaces at most one. *)
  Lemma prov_add (γ γ' : State) :
    Prov γ -> next γ <= next γ' ->
    (forall m fm, fibers γ' m = Some fm ->
       fibers γ m = Some fm \/ (fibers γ m = None /\ exists z, life fm = Inactive Σ z)) ->
    Prov γ'.
  Proof.
    intros [P1 P2] HN Hlk; split.
    - intros m fm H; destruct (Hlk m fm H) as [H0|[_ [z Hz]]].
      + exact (ProvF_mono _ _ _ HN (P1 m fm H0)).
      + exact (ProvF_inactive _ _ z Hz).
    - intros m1 m2 f1 f2 k1 p1 g1 k2 p2 g2 t Hne H1 H2 I1 I2.
      destruct (Hlk m1 f1 H1) as [G1|[_ [z1 Z1]]]; [|rewrite Z1 in I1; destruct I1].
      destruct (Hlk m2 f2 H2) as [G2|[_ [z2 Z2]]]; [|rewrite Z2 in I2; destruct I2].
      exact (P2 m1 m2 f1 f2 k1 p1 g1 k2 p2 g2 t Hne G1 G2 I1 I2).
  Qed.

  Lemma prov_replace (γ γ' : State) n f f' :
    Prov γ -> fibers γ n = Some f -> next γ <= next γ' -> fibers γ' n = Some f' ->
    (forall m fm, m <> n -> fibers γ' m = Some fm ->
       fibers γ m = Some fm \/ (fibers γ m = None /\ exists z, life fm = Inactive Σ z)) ->
    ProvF (next γ') f' ->
    (forall k p t g, In (UOp Σ k p t g) (acc_of (life f')) ->
       In (UOp Σ k p t g) (acc_of (life f)) \/ next γ <= t) ->
    Prov γ'.
  Proof.
    intros [P1 P2] Hn HN Hn' Hlk Hf' Hitems.
    assert (Lk : forall m fm, fibers γ' m = Some fm ->
              (m = n /\ fm = f') \/ (m <> n /\ fibers γ m = Some fm) \/
              (m <> n /\ exists z, life fm = Inactive Σ z)).
    { intros m fm H; destruct (Nat.eq_dec m n) as [->|Hmn].
      - left; split; congruence.
      - destruct (Hlk m fm Hmn H) as [H0|[_ Hz]]; [right; left | right; right]; auto. }
    split.
    - intros m fm H; destruct (Lk m fm H) as [[_ ->]|[[_ H0]|[_ [z Hz]]]].
      + exact Hf'.
      + exact (ProvF_mono _ _ _ HN (P1 m fm H0)).
      + exact (ProvF_inactive _ _ z Hz).
    - intros m1 m2 f1 f2 k1 p1 g1 k2 p2 g2 t Hne H1 H2 I1 I2.
      assert (Old : forall m fm k p g, m <> n -> fibers γ' m = Some fm ->
                    In (UOp Σ k p t g) (acc_of (life fm)) ->
                    fibers γ m = Some fm /\ t < next γ).
      { intros m fm k p g Hmn H I.
        destruct (Lk m fm H) as [[E _]|[[_ H0]|[_ [z Hz]]]]; [contradiction| |].
        - split; [exact H0|]; exact (proj1 (proj2 (proj2 (P1 m fm H0) k p t g I))).
        - rewrite Hz in I; destruct I. }
      destruct (Nat.eq_dec m1 n) as [->|Hn1], (Nat.eq_dec m2 n) as [->|Hn2];
        [contradiction | | |].
      + rewrite Hn' in H1; injection H1 as <-.
        destruct (Old m2 f2 k2 p2 g2 Hn2 H2 I2) as [G2 Ht2].
        destruct (Hitems k1 p1 t g1 I1) as [I1'|Ht]; [|lia].
        exact (P2 n m2 f f2 k1 p1 g1 k2 p2 g2 t Hne Hn G2 I1' I2).
      + rewrite Hn' in H2; injection H2 as <-.
        destruct (Old m1 f1 k1 p1 g1 Hn1 H1 I1) as [G1 Ht1].
        destruct (Hitems k2 p2 t g2 I2) as [I2'|Ht]; [|lia].
        exact (P2 m1 n f1 f k1 p1 g1 k2 p2 g2 t Hne G1 Hn I1 I2').
      + destruct (Old m1 f1 k1 p1 g1 Hn1 H1 I1) as [G1 _].
        destruct (Old m2 f2 k2 p2 g2 Hn2 H2 I2) as [G2 _].
        exact (P2 m1 m2 f1 f2 k1 p1 g1 k2 p2 g2 t Hne G1 G2 I1 I2).
  Qed.

  (** Replacing the life of fiber [n] in place. *)
  Lemma prov_relife (γ γ1 : State) n f (l : Life) :
    Prov γ -> fibers γ n = Some f -> next γ <= next γ1 ->
    (forall m fm, fibers γ1 m = Some fm ->
       fibers γ m = Some fm \/ (fibers γ m = None /\ exists z, life fm = Inactive Σ z)) ->
    ProvF (next γ1) (mkFiber Σ (fcomp f) (Calculus.parent Σ f) (Calculus.disposed Σ f) l) ->
    (forall k p t g, In (UOp Σ k p t g) (acc_of l) ->
       In (UOp Σ k p t g) (acc_of (life f)) \/ next γ <= t) ->
    Prov (set_life Σ γ1 n f l).
  Proof.
    intros P Hn HN Hlk Hf' Hit.
    eapply (prov_replace γ _ n f); eauto.
    - cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity.
    - intros m fm Hmn H; rewrite fibers_set_life in H.
      destruct (Nat.eqb_spec m n); [contradiction | exact (Hlk m fm H)].
  Qed.

  Lemma lk_same (γ : State) : forall m fm, fibers γ m = Some fm ->
    fibers γ m = Some fm \/ (fibers γ m = None /\ exists z, life fm = Inactive Σ z).
  Proof. intros; left; assumption. Qed.

  (** The life of [n] keeps its program residual and its operation items. *)
  Lemma provf_keep N f (l : Life) :
    ProvF N f ->
    (forall P acc w, l = Loading Σ P acc w -> exists acc' w', life f = Loading Σ P acc' w') ->
    (forall k p t g, In (UOp Σ k p t g) (acc_of l) -> In (UOp Σ k p t g) (acc_of (life f))) ->
    ProvF N (mkFiber Σ (fcomp f) (Calculus.parent Σ f) (Calculus.disposed Σ f) l).
  Proof.
    intros [H1 H2] Hl Hi; split; cbn.
    - intros P acc w E; destruct (Hl P acc w E) as (acc' & w' & E'); exact (H1 P acc' w' E').
    - intros k p t g I; exact (H2 k p t g (Hi k p t g I)).
  Qed.

  Ltac keep_goals Hold :=
    first [ intros ? ? ? ?E; discriminate E
          | intros ? ? ? ? ?I; left; exact I
          | (cbn; lia)
          | (intros ? ? ? ? ?I; eapply Hold; [cbn; lia | exact I])
          | (intros ? ? ?Hm; left; exact Hm) ].

  Theorem prov_step (γ γ' : State) ℓ :
    WF γ -> Prov γ -> step γ ℓ = Some γ' -> Prov γ'.
  Proof.
    intros W PV H.
    pose proof (pv_fib _ PV) as PF.
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n n0|n]; cbn [step] in H.
    - (* OInsert *)
      destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      apply (prov_add γ); [exact PV | cbn; lia|].
      intros m fm; cbn; unfold fupd; destruct (Nat.eqb_spec m (next γ)) as [->|_].
      + intros [= <-]; right; split; [exact (fresh_none K_eq_dec Σ prog γ W) | eexists; reflexivity].
      + intros Hm; left; exact Hm.
    - (* ODispose *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate]; injection H as <-.
      apply (prov_replace γ _ n f
               (mkFiber Σ (fcomp f) (Calculus.parent Σ f) true (life f)) PV Hn).
      + cbn; lia.
      + cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity.
      + intros m fm Hmn Hm; cbn in Hm; unfold fupd in Hm.
        destruct (Nat.eqb_spec m n); [contradiction | left; exact Hm].
      + destruct (PF n f Hn) as [Q1 Q2]; split; cbn; auto.
      + intros k p t g I; left; exact I.
    - (* OReset *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate; injection H as <-.
      apply (prov_relife γ γ n f); auto using lk_same.
      + apply (ProvF_inactive _ _ None); reflexivity.
      + intros k p t g [].
    - (* LBegin *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (target Σ prog γ n); [|discriminate]; injection H as <-.
      apply (prov_relife γ γ n f); auto using lk_same.
      + split; cbn; [intros P0 acc w [= <- _ _]; apply sub_refl | intros k p t g []].
      + intros k p t g [].
    - (* LStep *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [|P0 acc w| |] eqn:Hl; try discriminate.
      destruct (may_step K_eq_dec Σ prog γ n P0 w); [|discriminate]; injection H as <-.
      destruct (PF n f Hn) as [Q1 Q2].
      pose proof (Q1 P0 acc w Hl) as Hsub.
      assert (Hkeep : forall l, (forall P acc' w', l = Loading Σ P acc' w' -> Sub P P0) ->
                (forall k p t g, In (UOp Σ k p t g) (acc_of l) ->
                   In (UOp Σ k p t g) acc \/ next γ <= t) ->
                forall γ1, next γ <= next γ1 ->
                (forall k p t g, In (UOp Σ k p t g) (acc_of l) ->
                   p < next γ1 /\ t < next γ1 /\
                   exists a s s' o, OpAt k a (cbody (fcomp f)) /\ run a t s = Some (s', g, o)) ->
                (forall m fm, fibers γ1 m = Some fm ->
                   fibers γ m = Some fm \/ (fibers γ m = None /\ exists z, life fm = Inactive Σ z)) ->
                Prov (set_life Σ γ1 n f l)).
      { intros l Hl1 Hl2 γ1 HN Hl3 Hlk.
        apply (prov_relife γ γ1 n f); auto.
        - split; cbn.
          + intros P acc' w' E; exact (Sub_trans _ _ _ (Hl1 P acc' w' E) Hsub).
          + exact Hl3.
        - intros k p t g I; rewrite Hl; exact (Hl2 k p t g I). }
      assert (Hold : forall k p t g, In (UOp Σ k p t g) acc ->
                p < next γ /\ t < next γ /\
                exists a s s' o, OpAt k a (cbody (fcomp f)) /\ run a t s = Some (s', g, o)).
      { intros k p t g I; apply (Q2 k p t g); rewrite Hl; exact I. }
      assert (Hold' : forall N, next γ <= N -> forall k p t g, In (UOp Σ k p t g) acc ->
                p < N /\ t < N /\
                exists a s s' o, OpAt k a (cbody (fcomp f)) /\ run a t s = Some (s', g, o)).
      { intros N HN k p t g I; destruct (Hold k p t g I) as (? & ? & ?); repeat split; auto; lia. }
      assert (Hbump : forall m fm, fibers γ m = Some fm ->
                fibers γ m = Some fm \/ (fibers γ m = None /\ exists z, life fm = Inactive Σ z))
        by exact (lk_same γ).
      destruct P0 as [| |k a κ|k s P'|c P']; cbn [load_step].
      + apply (Hkeep (Active Σ acc w)); keep_goals Hold'.
      + apply (Hkeep (Unloading Σ acc w (Some EUser))); keep_goals Hold'.
      + match goal with |- Prov (match ?x with _ => _ end) => destruct x as [p|] end.
        2: { apply (Hkeep (Unloading Σ acc w (Some EUnresolved))); keep_goals Hold'. }
        destruct (binds γ k) as [b|] eqn:Hb.
        2: { apply (Hkeep (Unloading Σ acc w (Some EUnresolved))); keep_goals Hold'. }
        destruct (Nat.eqb (pid b) p) eqn:Hp.
        2: { apply (Hkeep (Unloading Σ acc w (Some EUnresolved))); keep_goals Hold'. }
        destruct (run a (next γ) (bst b)) as [[[s' g] o]|] eqn:Hrun.
        * apply (Hkeep (Loading Σ (κ o) (UOp Σ k p (next γ) g :: acc) w)); cbn.
          -- intros P acc' w' [= <- _ _]; eapply sub_op; apply sub_refl.
          -- intros k0 p0 t0 g0 [E|I]; [injection E as -> -> -> ->; right; lia | left; exact I].
          -- lia.
          -- intros k0 p0 t0 g0 [E|I].
             ++ injection E as <- <- <- <-.
                apply Nat.eqb_eq in Hp; subst p.
                pose proof (wf_pids K_eq_dec Σ prog γ W k b Hb).
                split; [lia | split; [lia|]].
                exists a, (bst b), s', o; split; [|exact Hrun].
                apply (Sub_OpAt k a (POp k a κ)); [exact Hsub | apply at_here].
             ++ eapply Hold'; [cbn; lia | exact I].
          -- intros m fm Hm; left; exact Hm.
        * apply (Hkeep (Unloading Σ acc w (Some EOp))); keep_goals Hold'.
      + destruct (kmem K_eq_dec k (provs Σ (prog (fcomp f)))).
        2: { apply (Hkeep (Unloading Σ acc w (Some EConflict))); keep_goals Hold'. }
        destruct (binds γ k).
        { apply (Hkeep (Unloading Σ acc w (Some EConflict))); keep_goals Hold'. }
        apply (Hkeep (Loading Σ P' (UProv Σ k (next γ) :: acc) w)); cbn.
        * intros P acc' w' [= <- _ _]; apply sub_prov, sub_refl.
        * intros k0 p0 t0 g0 [E|I]; [discriminate | left; exact I].
        * lia.
        * intros k0 p0 t0 g0 [E|I]; [discriminate | eapply Hold'; [cbn; lia | exact I]].
        * intros m fm Hm; left; exact Hm.
      + destruct (conflict K_eq_dec Σ prog γ c).
        { apply (Hkeep (Unloading Σ acc w (Some EConflict))); keep_goals Hold'. }
        apply (Hkeep (Loading Σ P' (USpawn Σ (next γ) :: acc) w)); cbn.
        * intros P acc' w' [= <- _ _]; apply sub_spawn, sub_refl.
        * intros k0 p0 t0 g0 [E|I]; [discriminate | left; exact I].
        * lia.
        * intros k0 p0 t0 g0 [E|I]; [discriminate | eapply Hold'; [cbn; lia | exact I]].
        * intros m fm; unfold fupd; destruct (Nat.eqb_spec m (next γ)) as [->|_].
          -- intros [= <-]; right; split; [exact (fresh_none K_eq_dec Σ prog γ W)|].
             eexists; reflexivity.
          -- intros Hm; left; exact Hm.
    - (* LDivert *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [|P0 acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [discriminate|]; injection H as <-.
      apply (prov_relife γ γ n f); auto using lk_same.
      + apply provf_keep; [exact (PF n f Hn) | discriminate | rewrite Hl; auto].
      + intros k p t g I; left; rewrite Hl; exact I.
    - (* LLeave *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ n w); [discriminate|]; injection H as <-.
      apply (prov_relife γ γ n f); auto using lk_same.
      + apply provf_keep; [exact (PF n f Hn) | discriminate | rewrite Hl; auto].
      + intros k p t g I; left; rewrite Hl; exact I.
    - (* LUndo *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      assert (Hrel : forall γ1, next γ1 = next γ -> fibers γ1 = fibers γ ->
                Prov (set_life Σ γ1 n f (Unloading Σ acc w z))).
      { intros γ1 HN HF; apply (prov_relife γ γ1 n f); auto.
        - lia.
        - intros m fm; rewrite HF; apply lk_same.
        - rewrite HN; apply provf_keep; [exact (PF n f Hn) | discriminate|].
          intros k p t g I; rewrite Hl; right; exact I.
        - intros k p t g I; left; rewrite Hl; right; exact I. }
      destruct u as [k p t g|k p|m]; cbn [undo_step] in H.
      + destruct (binds γ k) as [b|]; [destruct (Nat.eqb (pid b) p)|];
          injection H as <-; apply Hrel; reflexivity.
      + destruct (relied Σ γ n p); [discriminate|].
        destruct (binds γ k) as [b|]; [destruct (Nat.eqb (pid b) p)|];
          injection H as <-; apply Hrel; reflexivity.
      + destruct (fibers γ m); [discriminate|]; injection H as <-; apply Hrel; reflexivity.
    - (* LRetireChild *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|[k p t g|k p|m0] acc] w z]; try discriminate.
      destruct (fibers γ m0) as [g|] eqn:Hg; [|discriminate].
      unheld H; destruct (Calculus.disposed Σ g); [discriminate|]; injection H as <-.
      apply (prov_replace γ _ m0 g
               (mkFiber Σ (fcomp g) (Calculus.parent Σ g) true (life g)) PV Hg).
      + cbn; lia.
      + cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity.
      + intros m fm Hmn Hm; cbn in Hm; unfold fupd in Hm.
        destruct (Nat.eqb_spec m m0); [contradiction | left; exact Hm].
      + destruct (PF m0 g Hg) as [Q1 Q2]; split; cbn; auto.
      + intros k0 p0 t0 g0 I; left; exact I.
    - (* LUnloaded *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      injection H as <-.
      apply (prov_relife γ γ n f); auto using lk_same.
      + apply (ProvF_inactive _ _ z); reflexivity.
      + intros k p t g [].
    - (* LRemove *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [z| | |]; try discriminate.
      destruct (Calculus.disposed Σ f && negb (has_child Σ γ n)); [|discriminate].
      injection H as <-.
      apply (prov_add γ); [exact PV | cbn; lia|].
      intros m fm; cbn; unfold fupd; destruct (Nat.eqb_spec m n); [discriminate|].
      intros Hm; left; exact Hm.
    - (* OReact *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (nth_error (reacts Σ (prog (fcomp f))) n0) as [c|]; [|discriminate].
      destruct (Calculus.disposed Σ f || conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      destruct (PF n f Hn) as [Q1 Q2].
      apply (prov_relife γ _ n f); [exact PV | exact Hn | cbn; lia | | |].
      + intros m fm; cbn; unfold fupd; destruct (Nat.eqb_spec m (next γ)) as [->|_].
        * intros [= <-]; right; split; [exact (fresh_none K_eq_dec Σ prog γ W) | eexists; reflexivity].
        * intros Hm; left; exact Hm.
      + split; cbn; [intros P0 acc' w' E; discriminate|].
        intros k p t g [E|Hin]; [discriminate|].
        assert (Hin' : In (UOp Σ k p t g) (acc_of (life f))) by (rewrite Hl; exact Hin).
        destruct (Q2 k p t g Hin') as (Hp & Ht & Hx); repeat split; auto; lia.
      + intros k p t g [E|Hin]; [discriminate|]; left; rewrite Hl; exact Hin.
    - (* ORestart *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (Calculus.disposed Σ f); [discriminate|].
      destruct (life f) as [|P0 acc w|acc w|] eqn:Hl; try discriminate; injection H as <-;
      (apply (prov_relife γ γ n f); auto using lk_same;
       [ apply provf_keep; [exact (PF n f Hn) | discriminate | rewrite Hl; auto]
       | intros k p t g I; left; rewrite Hl; exact I ]).
  Qed.

  (** ** Events on bindings

      [event γ ℓ] says what step [ℓ] does to the bindings at [γ]: an
      operation of fiber [m] on key [k], an undo of [m] on [k], the creation
      or the removal of the binding at [k], or nothing. *)
  Local Notation Binding := (Binding Σ).
  Definition Store : Type := K -> option S.

  Definition op_binding (γ : State) (m : nat) (f : Fiber) (k : K) (w : View)
    : option Binding :=
    let rp := if kmem K_eq_dec k (deps Σ (prog (fcomp f))) then lookup_view K_eq_dec k w
              else match binds γ k with
                   | Some b => if Nat.eqb (owner b) m then Some (pid b) else None
                   | None => None
                   end in
    match rp, binds γ k with
    | Some p, Some b => if Nat.eqb (pid b) p then Some b else None
    | _, _ => None
    end.

  Inductive Event : Type :=
  | EvNone
  | EvOp (m : nat) (k : K) (a : Op Σ) (t : nat)
  | EvInv (m : nat) (k : K) (g : S -> S)
  | EvCreate (k : K) (s : S)
  | EvRemove (k : K).

  Definition event (γ : State) (ℓ : @Label C) : Event :=
    match ℓ with
    | LStep m =>
        match fibers γ m with
        | Some f =>
            match life f with
            | Loading _ P _ w =>
                if may_step K_eq_dec Σ prog γ m P w then
                  match P with
                  | POp k a _ =>
                      match op_binding γ m f k w with
                      | Some _ => EvOp m k a (next γ)
                      | None => EvNone
                      end
                  | PProvide k s _ =>
                      if kmem K_eq_dec k (provs Σ (prog (fcomp f))) then
                        match binds γ k with None => EvCreate k s | Some _ => EvNone end
                      else EvNone
                  | _ => EvNone
                  end
                else EvNone
            | _ => EvNone
            end
        | None => EvNone
        end
    | LUndo m =>
        match fibers γ m with
        | Some f =>
            match life f with
            | Unloading _ (UOp _ k p _ g :: _) _ _ =>
                match binds γ k with
                | Some b => if Nat.eqb (pid b) p then EvInv m k g else EvNone
                | None => EvNone
                end
            | Unloading _ (UProv _ k p :: _) _ _ =>
                if relied Σ γ m p then EvNone
                else match binds γ k with
                     | Some b => if Nat.eqb (pid b) p then EvRemove k else EvNone
                     | None => EvNone
                     end
            | _ => EvNone
            end
        | None => EvNone
        end
    | _ => EvNone
    end.

  (** ** Pending inverses *)
  Definition pacc (γ : State) (x : nat) : list Undo :=
    match fibers γ x with Some f => acc_of (life f) | None => [] end.

  (** The inverses an accumulator holds on the binding [(k, p)], most
      recent first. *)
  Fixpoint pend_list (k : K) (p : nat) (l : list Undo) : list (S -> S) :=
    match l with
    | [] => []
    | UOp _ k' p' _ g :: l' =>
        if keqb K_eq_dec k' k && Nat.eqb p' p then g :: pend_list k p l'
        else pend_list k p l'
    | _ :: l' => pend_list k p l'
    end.

  (** Undo the most recent first. *)
  Fixpoint apply_all (gs : list (S -> S)) (s : S) : S :=
    match gs with
    | [] => s
    | g :: gs' => apply_all gs' (g s)
    end.

  Lemma keqb_refl k : keqb K_eq_dec k k = true.
  Proof. unfold keqb; destruct (K_eq_dec k k); congruence. Qed.

  Lemma keqb_neq k k' : k <> k' -> keqb K_eq_dec k k' = false.
  Proof. unfold keqb; destruct (K_eq_dec k k'); congruence. Qed.

  Lemma pend_list_uop_same k p t g l :
    pend_list k p (UOp Σ k p t g :: l) = g :: pend_list k p l.
  Proof. cbn; rewrite keqb_refl, Nat.eqb_refl; reflexivity. Qed.

  Lemma pend_list_uop_other k p k' p' t g l :
    (k' <> k \/ p' <> p) -> pend_list k p (UOp Σ k' p' t g :: l) = pend_list k p l.
  Proof.
    intros H; cbn.
    destruct (keqb K_eq_dec k' k) eqn:E1, (Nat.eqb p' p) eqn:E2; cbn; try reflexivity.
    exfalso; unfold keqb in E1; destruct (K_eq_dec k' k); [|discriminate].
    apply Nat.eqb_eq in E2; destruct H; contradiction.
  Qed.

  Lemma pend_list_in k p l g :
    In g (pend_list k p l) -> exists t, In (UOp Σ k p t g) l.
  Proof.
    induction l as [|u l IH]; cbn; [intros []|].
    destruct u as [k' p' t g'|k' p'|m]; [|intros H; destruct (IH H) as [t Ht]; eauto ..].
    destruct (keqb K_eq_dec k' k && Nat.eqb p' p) eqn:E.
    - intros [<-|H].
      + apply andb_true_iff in E as [E1 E2].
        unfold keqb in E1; destruct (K_eq_dec k' k) as [->|]; [|discriminate].
        apply Nat.eqb_eq in E2; subst; exists t; left; reflexivity.
      + destruct (IH H) as [t0 Ht0]; eauto.
    - intros H; destruct (IH H) as [t0 Ht0]; eauto.
  Qed.

  Lemma pend_list_fresh k N l :
    (forall k' p' t g, In (UOp Σ k' p' t g) l -> p' < N) -> pend_list k N l = [].
  Proof.
    induction l as [|u l IH]; intros H; cbn; [reflexivity|].
    destruct u as [k' p' t g|k' p'|m]; [|apply IH; intros; eapply H; right; eauto ..].
    destruct (keqb K_eq_dec k' k && Nat.eqb p' N) eqn:E.
    - apply andb_true_iff in E as [_ E]; apply Nat.eqb_eq in E; subst.
      specialize (H k' N t g (or_introl eq_refl)); lia.
    - apply IH; intros; eapply H; right; eauto.
  Qed.

  Lemma apply_all_respects gs :
    (forall g, In g gs -> respects (Σ := Σ) g) -> respects (Σ := Σ) (apply_all gs).
  Proof.
    induction gs as [|g gs IH]; intros H x y Hxy; cbn; [exact Hxy|].
    apply IH; [intros; apply H; right; auto | apply H; [left; reflexivity | exact Hxy]].
  Qed.

  Lemma shifted_all a t gs :
    (forall g, In g gs ->
       respects (Σ := Σ) g /\ forall x, shifted (Σ := Σ) g (run a t x) (run a t (g x))) ->
    forall x, shifted (Σ := Σ) (apply_all gs) (run a t x) (run a t (apply_all gs x)).
  Proof.
    induction gs as [|g gs IH]; intros H x; cbn [apply_all].
    - destruct (run a t x) as [[[x1 h] o]|]; cbn; [|exact I].
      split; [reflexivity | split; [intros y; reflexivity | reflexivity]].
    - destruct (H g (or_introl eq_refl)) as [Hg Hsh].
      pose proof (IH (fun g' Hin => H g' (or_intror Hin)) (g x)) as IH'.
      assert (Hres : respects (Σ := Σ) (apply_all gs)).
      { apply apply_all_respects; intros g' Hin; apply (H g' (or_intror Hin)). }
      specialize (Hsh x).
      destruct (run a t x) as [[[x1 h1] o1]|];
        destruct (run a t (g x)) as [[[x2 h2] o2]|]; cbn in Hsh; try contradiction;
        destruct (run a t (apply_all gs (g x))) as [[[x3 h3] o3]|];
        cbn in IH' |- *; try contradiction; auto.
      destruct Hsh as [E2 [F2 O2]], IH' as [E3 [F3 O3]].
      split; [|split].
      + transitivity (apply_all gs x2); [exact E3 | apply Hres; exact E2].
      + intros y; transitivity (h2 y); [apply F3 | apply F2].
      + congruence.
  Qed.

  Lemma commute_all gs (h : S -> S) :
    (forall g, In g gs -> respects (Σ := Σ) g /\ forall x, g (h x) ≃ h (g x)) ->
    forall x, apply_all gs (h x) ≃ h (apply_all gs x).
  Proof.
    induction gs as [|g gs IH]; intros H x; cbn [apply_all]; [reflexivity|].
    destruct (H g (or_introl eq_refl)) as [_ Hc].
    assert (Hres : respects (Σ := Σ) (apply_all gs)).
    { apply apply_all_respects; intros g' Hin; apply (H g' (or_intror Hin)). }
    transitivity (apply_all gs (h (g x))).
    - apply Hres, Hc.
    - apply IH; intros g' Hin; apply (H g' (or_intror Hin)).
  Qed.

  (** ** The shadow store and the invariant *)
  Hypothesis Hwb : forall a t, WellBehaved (Σ := Σ) a t.
  (** Withdrawing one fiber's operation is not disturbed by another fiber's
      operation at the same key. *)
  Hypothesis Hind : forall k a b ta tb, CoPair k a b -> ta <> tb ->
    RevertIndep (Σ := Σ) a ta b tb.

  Variable n : nat.

  Definition supd (σ : Store) (k : K) (o : option S) : Store :=
    fun k' => if keqb K_eq_dec k' k then o else σ k'.

  (** The shadow skips [n]'s operations and undos, and applies everything
      else. *)
  Definition shadow_apply (e : Event) (σ : Store) : Store :=
    match e with
    | EvNone => σ
    | EvOp m k a t =>
        if Nat.eqb m n then σ
        else supd σ k (match σ k with
                       | Some s => match run a t s with
                                   | Some (s', _, _) => Some s'
                                   | None => Some s
                                   end
                       | None => None
                       end)
    | EvInv m k g => if Nat.eqb m n then σ else supd σ k (option_map g (σ k))
    | EvCreate k s => supd σ k (Some s)
    | EvRemove k => supd σ k None
    end.

  Definition pend (γ : State) (k : K) : list (S -> S) :=
    match binds γ k with
    | Some b => pend_list k (pid b) (pacc γ n)
    | None => []
    end.

  Definition Rk (ob : option Binding) (os : option S) (G : list (S -> S)) : Prop :=
    match ob, os with
    | None, None => True
    | Some b, Some s => apply_all G (bst b) ≃ s
    | _, _ => False
    end.

  Definition R (γ : State) (σ : Store) : Prop := forall k, Rk (binds γ k) (σ k) (pend γ k).

  Definition store (γ : State) : Store := fun k => option_map bst (binds γ k).

  Lemma R_store (γ : State) : (forall k p, pend_list k p (pacc γ n) = []) -> R γ (store γ).
  Proof.
    intros H k; unfold Rk, store, pend; destruct (binds γ k) as [b|]; cbn; [|exact I].
    rewrite H; cbn; reflexivity.
  Qed.

  Lemma R_transfer (γ γ' : State) σ :
    (forall k, binds γ' k = binds γ k) ->
    (forall k p, pend_list k p (pacc γ' n) = pend_list k p (pacc γ n)) ->
    R γ σ -> R γ' σ.
  Proof.
    intros Hb Hp HR k; specialize (HR k); unfold pend in *; rewrite Hb.
    destruct (binds γ k); [rewrite Hp|]; exact HR.
  Qed.

  (** What the provenance says about [n]'s pending inverses. *)
  Lemma pend_good (γ : State) k p g :
    Prov γ -> In g (pend_list k p (pacc γ n)) ->
    exists fn t a, fibers γ n = Some fn /\ In (UOp Σ k p t g) (acc_of (life fn)) /\
                   t < next γ /\ OpAt k a (cbody (fcomp fn)) /\ yields (Σ := Σ) a t g.
  Proof.
    intros PV Hin; apply pend_list_in in Hin as [t Ht].
    unfold pacc in Ht; destruct (fibers γ n) as [fn|] eqn:Hn; [|destruct Ht].
    destruct (proj2 (pv_fib _ PV n fn Hn) k p t g Ht) as (_ & Htn & a & s & s' & o & Ha & Hr).
    exists fn, t, a; repeat split; auto.
    exists s, s', o; exact Hr.
  Qed.

  Lemma pend_respects (γ : State) k p g :
    Prov γ -> In g (pend_list k p (pacc γ n)) -> respects (Σ := Σ) g.
  Proof.
    intros PV Hin; destruct (pend_good γ k p g PV Hin) as (fn & t & a & _ & _ & _ & _ & s & s' & o & Hr).
    exact (wb_inv a t (Hwb a t) s s' g o Hr).
  Qed.

  Lemma pacc_set_life (γ1 : State) x f (l : Life) :
    pacc (set_life Σ γ1 x f l) n = if Nat.eqb n x then acc_of l else pacc γ1 n.
  Proof.
    unfold pacc; rewrite fibers_set_life; destruct (Nat.eqb n x); reflexivity.
  Qed.

  (** If [n]'s accumulator is unchanged, or changed only by items that are
      not operation items, the pending inverses are unchanged. *)
  Lemma pend_list_keep (γ γ1 : State) x f (l : Life) :
    fibers γ x = Some f -> pacc γ1 n = pacc γ n ->
    (forall k p, pend_list k p (acc_of l) = pend_list k p (acc_of (life f))) ->
    forall k p, pend_list k p (pacc (set_life Σ γ1 x f l) n) = pend_list k p (pacc γ n).
  Proof.
    intros Hx Hp Hl k p; rewrite pacc_set_life.
    destruct (Nat.eqb_spec n x) as [->|_]; [|rewrite Hp; reflexivity].
    rewrite Hl; unfold pacc; rewrite Hx; reflexivity.
  Qed.

  Lemma R_transfer' (γ γ' : State) σ :
    (forall k, binds γ' k = binds γ k) -> (forall k, pend γ' k = pend γ k) ->
    R γ σ -> R γ' σ.
  Proof. intros Hb Hp HR k; specialize (HR k); rewrite Hb, Hp; exact HR. Qed.

  (** ** The events of the two compound rules *)
  Definition event_load (γ : State) m (f : Fiber) (P : Prog) (w : View) : Event :=
    match P with
    | POp k a _ =>
        match op_binding γ m f k w with Some _ => EvOp m k a (next γ) | None => EvNone end
    | PProvide k s _ =>
        if kmem K_eq_dec k (provs Σ (prog (fcomp f))) then
          match binds γ k with None => EvCreate k s | Some _ => EvNone end
        else EvNone
    | _ => EvNone
    end.

  Definition event_undo (γ : State) m (u : Undo) : Event :=
    match u with
    | UOp _ k p _ g =>
        match binds γ k with
        | Some b => if Nat.eqb (pid b) p then EvInv m k g else EvNone
        | None => EvNone
        end
    | UProv _ k p =>
        if relied Σ γ m p then EvNone
        else match binds γ k with
             | Some b => if Nat.eqb (pid b) p then EvRemove k else EvNone
             | None => EvNone
             end
    | USpawn _ _ => EvNone
    end.

  Lemma event_LStep (γ : State) x f P acc w :
    fibers γ x = Some f -> life f = Loading Σ P acc w ->
    may_step K_eq_dec Σ prog γ x P w = true ->
    event γ (LStep x) = event_load γ x f P w.
  Proof. intros Hx Hl Ht; cbn [event]; rewrite Hx, Hl, Ht; reflexivity. Qed.

  Lemma event_LUndo (γ : State) x f u acc w z :
    fibers γ x = Some f -> life f = Unloading Σ (u :: acc) w z ->
    event γ (LUndo x) = event_undo γ x u.
  Proof. intros Hx Hl; cbn [event]; rewrite Hx, Hl; destruct u; reflexivity. Qed.

  Lemma op_binding_spec (γ : State) m f k w b :
    op_binding γ m f k w = Some b -> binds γ k = Some b.
  Proof.
    unfold op_binding.
    match goal with |- match ?x with _ => _ end = _ -> _ => destruct x as [p|] end;
      [|discriminate].
    destruct (binds γ k) as [b0|]; [|discriminate].
    destruct (Nat.eqb (pid b0) p); [congruence | discriminate].
  Qed.

  Lemma load_step_op (γ : State) m f k a κ acc w :
    load_step K_eq_dec Σ prog γ m f (POp k a κ) acc w =
    match op_binding γ m f k w with
    | Some b =>
        match run a (next γ) (bst b) with
        | Some (s', g, o) =>
            set_life Σ (bump Σ (log_op Σ (with_binds Σ γ (bupd K_eq_dec Σ (binds γ) k
                (Some (mkBinding Σ (pid b) (owner b) s')))) (next γ) a)) m f
                (Loading Σ (κ o) (UOp Σ k (pid b) (next γ) g :: acc) w)
        | None => set_life Σ (bump Σ γ) m f (Unloading Σ acc w (Some EOp))
        end
    | None => set_life Σ γ m f (Unloading Σ acc w (Some EUnresolved))
    end.
  Proof.
    unfold op_binding; cbn [load_step].
    match goal with |- match ?x with _ => _ end = _ => destruct x as [p|] end;
      [|reflexivity].
    destruct (binds γ k) as [b|]; [|reflexivity].
    destruct (Nat.eqb_spec (pid b) p) as [Hp|Hp]; [subst p | reflexivity].
    reflexivity.
  Qed.

  (** The operation a Loading fiber is about to perform belongs to its
      component. *)
  Lemma loading_op (γ : State) x f k a κ acc w :
    Prov γ -> fibers γ x = Some f -> life f = Loading Σ (POp k a κ) acc w ->
    OpAt k a (cbody (fcomp f)).
  Proof.
    intros PV Hx Hl.
    apply (Sub_OpAt k a (POp k a κ)); [|apply at_here].
    exact (proj1 (pv_fib _ PV x f Hx) _ acc w Hl).
  Qed.

  (** Every pending inverse of [n] can be run after a foreign operation. *)
  Lemma pend_shift (γ : State) x f k a κ acc w p :
    WF γ -> Prov γ -> fibers γ x = Some f -> life f = Loading Σ (POp k a κ) acc w -> x <> n ->
    forall g, In g (pend_list k p (pacc γ n)) ->
      respects (Σ := Σ) g /\
      forall y, shifted (Σ := Σ) g (run a (next γ) y) (run a (next γ) (g y)).
  Proof.
    intros W PV Hx Hl Hxn g Hin.
    split; [exact (pend_respects γ k p g PV Hin)|].
    destruct (pend_good γ k p g PV Hin) as (fn & t & ai & Hn & Hit & Ht & Hai & Hy).
    pose proof (loading_op γ x f k a κ acc w PV Hx Hl) as Ha.
    assert (HRI : RevertIndep (Σ := Σ) ai t a (next γ)).
    { apply (Hind k); [exact (copair_wf γ n fn x f k ai a W (fun E => Hxn (eq_sym E)) Hn Hx Hai Ha) | lia]. }
    exact (proj1 (HRI g Hy)).
  Qed.

  (** Every pending inverse of [n] commutes with a foreign undo. *)
  Lemma pend_commute (γ : State) x f k p t h acc w z q :
    WF γ -> Prov γ -> fibers γ x = Some f ->
    life f = Unloading Σ (UOp Σ k p t h :: acc) w z -> x <> n ->
    forall g, In g (pend_list k q (pacc γ n)) ->
      respects (Σ := Σ) g /\ forall y, g (h y) ≃ h (g y).
  Proof.
    intros W PV Hx Hl Hxn g Hin.
    split; [exact (pend_respects γ k q g PV Hin)|].
    destruct (pend_good γ k q g PV Hin) as (fn & ti & ai & Hn & Hit & Hti & Hai & Hy).
    assert (Hix : In (UOp Σ k p t h) (acc_of (life f))) by (rewrite Hl; left; reflexivity).
    destruct (proj2 (pv_fib _ PV x f Hx) k p t h Hix)
      as (_ & _ & b & s & s' & o & Hb & Hrun).
    assert (Hne : ti <> t).
    { intros ->; exact (pv_tok _ PV n x fn f k q g k p h t
                          (fun E => Hxn (eq_sym E)) Hn Hx Hit Hix). }
    assert (HRI : RevertIndep (Σ := Σ) ai ti b t).
    { apply (Hind k); [|exact Hne].
      assert (Hai' : OpAt k ai (cbody (fcomp fn))) by exact Hai.
      exact (copair_wf γ n fn x f k ai b W (fun E => Hxn (eq_sym E)) Hn Hx Hai' Hb). }
    intros y; exact (proj2 (HRI g Hy) h y (ex_intro _ s (ex_intro _ s' (ex_intro _ o Hrun)))).
  Qed.

  Lemma undo_inv_respects (γ : State) x f k p t h acc w z :
    Prov γ -> fibers γ x = Some f ->
    life f = Unloading Σ (UOp Σ k p t h :: acc) w z -> respects (Σ := Σ) h.
  Proof.
    intros PV Hx Hl.
    assert (Hix : In (UOp Σ k p t h) (acc_of (life f))) by (rewrite Hl; left; reflexivity).
    destruct (proj2 (pv_fib _ PV x f Hx) k p t h Hix)
      as (_ & _ & b & s & s' & o & Hb & Hrun).
    exact (wb_inv b t (Hwb b t) s s' h o Hrun).
  Qed.

  (** The pid of a new provision is not pending. *)
  Lemma pend_fresh (γ : State) k : Prov γ -> pend_list k (next γ) (pacc γ n) = [].
  Proof.
    intros PV; apply pend_list_fresh; intros k' p' t g Hin.
    unfold pacc in Hin; destruct (fibers γ n) as [fn|] eqn:Hn; [|destruct Hin].
    exact (proj1 (proj2 (pv_fib _ PV n fn Hn) k' p' t g Hin)).
  Qed.

  (** ** A Loading step *)
  Lemma R_load (γ : State) x f P acc w σ :
    WF γ -> Prov γ -> R γ σ -> fibers γ x = Some f -> life f = Loading Σ P acc w ->
    R (load_step K_eq_dec Σ prog γ x f P acc w) (shadow_apply (event_load γ x f P w) σ).
  Proof.
    intros W PV HR Hx Hl.
    assert (Hpx : pacc γ x = acc) by (unfold pacc; rewrite Hx, Hl; reflexivity).
    assert (Hkeep : forall γ1 (l : Life),
              (forall k, binds γ1 k = binds γ k) -> fibers γ1 = fibers γ ->
              (forall k p, pend_list k p (acc_of l) = pend_list k p acc) ->
              R (set_life Σ γ1 x f l) σ).
    { intros γ1 l Hb Hf Hp; apply (R_transfer γ); [exact Hb | | exact HR].
      apply (pend_list_keep γ γ1 x f l Hx); [unfold pacc; rewrite Hf; reflexivity|].
      intros k p; rewrite Hp, Hl; reflexivity. }
    destruct P as [| |k a κ|k s P'|c P'].
    - cbn [load_step event_load shadow_apply]; apply Hkeep; reflexivity.
    - cbn [load_step event_load shadow_apply]; apply Hkeep; reflexivity.
    - (* an operation *)
      rewrite load_step_op; cbn [event_load].
      destruct (op_binding γ x f k w) as [b|] eqn:Hob.
      2: { cbn [shadow_apply]; apply Hkeep; reflexivity. }
      pose proof (op_binding_spec γ x f k w b Hob) as Hb.
      pose proof (HR k) as HRk; unfold Rk, pend in HRk; rewrite Hb in HRk.
      destruct (σ k) as [s0|] eqn:Hσk; [|contradiction].
      cbn [shadow_apply].
      destruct (Nat.eqb_spec x n) as [->|Hxn].
      + (* [n]'s own operation: the shadow does not move *)
        destruct (run a (next γ) (bst b)) as [[[s' g] o]|] eqn:Hrun.
        2: { apply Hkeep; reflexivity. }
        intros k'; unfold Rk, pend.
        rewrite pacc_set_life, Nat.eqb_refl; cbn [acc_of].
        cbn [set_life set_fiber with_fibers with_binds bump log_op log_ini binds]; unfold bupd.
        destruct (keqb K_eq_dec k' k) eqn:Ek.
        * unfold keqb in Ek; destruct (K_eq_dec k' k) as [->|]; [|discriminate].
          cbn [pid bst]; rewrite Hσk, pend_list_uop_same; cbn [apply_all].
          rewrite Hpx in HRk.
          transitivity (apply_all (pend_list k (pid b) acc) (bst b)); [|exact HRk].
          apply apply_all_respects.
          -- intros g' Hin; rewrite <- Hpx in Hin; exact (pend_respects γ k _ g' PV Hin).
          -- exact (wb_witness a (next γ) (Hwb a (next γ)) (bst b) s' g o Hrun).
        * unfold keqb in Ek; destruct (K_eq_dec k' k) as [|Hne]; [discriminate|].
          pose proof (HR k') as HRk'; unfold Rk, pend in HRk'.
          destruct (binds γ k') as [b'|]; [|exact HRk'].
          rewrite pend_list_uop_other by (left; exact (fun E => Hne (eq_sym E))).
          rewrite <- Hpx; exact HRk'.
      + (* a foreign operation *)
        assert (Hpn : forall γ1 (l : Life), pacc γ1 n = pacc γ n ->
                  pacc (set_life Σ γ1 x f l) n = pacc γ n).
        { intros γ1 l E; rewrite pacc_set_life.
          destruct (Nat.eqb_spec n x); [congruence | exact E]. }
        pose proof (shifted_all a (next γ) (pend_list k (pid b) (pacc γ n))
                      (pend_shift γ x f k a κ acc w (pid b) W PV Hx Hl Hxn) (bst b)) as Hsh.
        set (G := pend_list k (pid b) (pacc γ n)) in *.
        pose proof (wb_respects a (next γ) (Hwb a (next γ)) _ _ HRk) as Hres.
        destruct (run a (next γ) (bst b)) as [[[s' h] o]|] eqn:Hrun.
        * destruct (run a (next γ) (apply_all G (bst b))) as [[[x2 h2] o2]|];
            cbn in Hsh; [|contradiction].
          destruct Hsh as [Ex2 _].
          destruct (run a (next γ) s0) as [[[y h3] o3]|] eqn:Hy0; cbn in Hres; [|contradiction].
          destruct Hres as [Ey _].
          intros k'; unfold Rk, pend.
          rewrite Hpn by reflexivity.
          cbn [set_life set_fiber with_fibers with_binds bump log_op log_ini binds]; unfold bupd, supd.
          destruct (keqb K_eq_dec k' k) eqn:Ek.
          -- unfold keqb in Ek; destruct (K_eq_dec k' k) as [->|]; [|discriminate].
             rewrite Hσk, Hy0; cbn [pid bst].
             transitivity x2; [symmetry; exact Ex2 | exact Ey].
          -- pose proof (HR k') as HRk'; unfold Rk, pend in HRk'; exact HRk'.
        * destruct (run a (next γ) (apply_all G (bst b))) as [[[x2 h2] o2]|];
            cbn in Hsh; [contradiction|].
          destruct (run a (next γ) s0) as [[[y h3] o3]|] eqn:Hy0; cbn in Hres; [contradiction|].
          intros k'; unfold Rk, pend.
          rewrite Hpn by reflexivity.
          cbn [set_life set_fiber with_fibers with_binds bump log_op log_ini binds]; unfold supd.
          destruct (keqb K_eq_dec k' k) eqn:Ek.
          -- unfold keqb in Ek; destruct (K_eq_dec k' k) as [->|]; [|discriminate].
             rewrite Hb, Hσk, Hy0; exact HRk.
          -- pose proof (HR k') as HRk'; unfold Rk, pend in HRk'; exact HRk'.
    - (* a provision *)
      cbn [load_step event_load].
      destruct (kmem K_eq_dec k (provs Σ (prog (fcomp f)))) eqn:Hk.
      2: { cbn [shadow_apply]; apply Hkeep; reflexivity. }
      destruct (binds γ k) as [b|] eqn:Hb.
      { cbn [shadow_apply]; apply Hkeep; reflexivity. }
      cbn [shadow_apply].
      match goal with |- R ?γ' _ =>
        assert (Hpl : forall k0 p0, pend_list k0 p0 (pacc γ' n) = pend_list k0 p0 (pacc γ n))
      end.
      { intros k0 p0; rewrite pacc_set_life; cbn [acc_of].
        destruct (Nat.eqb_spec n x) as [->|_]; [rewrite Hpx|]; reflexivity. }
      match goal with |- R ?γ' _ =>
        assert (Hbd : forall k0, binds γ' k0 =
                  if keqb K_eq_dec k0 k then Some (mkBinding Σ (next γ) x s) else binds γ k0)
          by reflexivity
      end.
      intros k'; unfold Rk, pend; rewrite Hbd; unfold supd.
      destruct (keqb K_eq_dec k' k) eqn:Ek; cbn [pid bst].
      + rewrite Hpl.
        unfold keqb in Ek; destruct (K_eq_dec k' k) as [->|]; [|discriminate].
        rewrite pend_fresh by exact PV; cbn; reflexivity.
      + pose proof (HR k') as HRk'; unfold Rk, pend in HRk'.
        destruct (binds γ k') as [b'|]; [rewrite Hpl|]; exact HRk'.
    - (* a spawn *)
      cbn [load_step event_load shadow_apply].
      destruct (conflict K_eq_dec Σ prog γ c); [apply Hkeep; reflexivity|].
      apply (R_transfer γ); [intros; reflexivity | | exact HR].
      intros k p; rewrite pacc_set_life.
      destruct (Nat.eqb_spec n x) as [->|Hnx]; [rewrite Hpx; reflexivity|].
      unfold pacc; cbn; unfold fupd.
      destruct (Nat.eqb_spec n (next γ)) as [->|_]; [|reflexivity].
      rewrite (fresh_none K_eq_dec Σ prog γ W); reflexivity.
  Qed.

  (** ** An undo step *)
  Lemma R_undo (γ γ' : State) x f u acc w z σ :
    WF γ -> Prov γ -> R γ σ -> fibers γ x = Some f ->
    life f = Unloading Σ (u :: acc) w z ->
    undo_step K_eq_dec Σ γ x f u acc w z = Some γ' ->
    R γ' (shadow_apply (event_undo γ x u) σ).
  Proof.
    intros W PV HR Hx Hl H.
    assert (Hpx : pacc γ x = u :: acc) by (unfold pacc; rewrite Hx, Hl; reflexivity).
    assert (Hpn : forall γ1, fibers γ1 = fibers γ ->
              pacc (set_life Σ γ1 x f (Unloading Σ acc w z)) n
              = if Nat.eqb n x then acc else pacc γ n).
    { intros γ1 E; rewrite pacc_set_life; destruct (Nat.eqb n x); [reflexivity|].
      unfold pacc; rewrite E; reflexivity. }
    (* Popping an item that is not an operation item of [n] on a current
       binding leaves the pending inverses as they are. *)
    assert (Hpop : forall γ1, fibers γ1 = fibers γ -> (forall k, binds γ1 k = binds γ k) ->
              (forall k b, binds γ k = Some b ->
                 pend_list k (pid b) (u :: acc) = pend_list k (pid b) acc) ->
              R (set_life Σ γ1 x f (Unloading Σ acc w z)) σ).
    { intros γ1 Ef Eb Hu; apply (R_transfer' γ); [exact Eb | | exact HR].
      intros k; unfold pend; cbn [set_life set_fiber with_fibers binds]; rewrite Eb.
      destruct (binds γ k) as [b|] eqn:Hb; [|reflexivity].
      rewrite Hpn by exact Ef.
      destruct (Nat.eqb_spec n x) as [->|_]; [|reflexivity].
      rewrite Hpx; symmetry; exact (Hu k b Hb). }
    destruct u as [k p t g|k p|m]; cbn [undo_step event_undo] in *.
    - destruct (binds γ k) as [b|] eqn:Hb.
      2: { injection H as <-; cbn [shadow_apply].
           apply Hpop; [reflexivity | reflexivity|].
           intros k0 b0 Hb0; apply pend_list_uop_other; left; congruence. }
      destruct (Nat.eqb_spec (pid b) p) as [Hp|Hp].
      2: { injection H as <-; cbn [shadow_apply].
           apply Hpop; [reflexivity | reflexivity|].
           intros k0 b0 Hb0; apply pend_list_uop_other.
           destruct (K_eq_dec k k0) as [->|Hne]; [right; congruence | left; exact Hne]. }
      subst p; injection H as <-.
      pose proof (HR k) as HRk; unfold Rk, pend in HRk; rewrite Hb in HRk.
      destruct (σ k) as [s0|] eqn:Hσk; [|contradiction].
      cbn [shadow_apply].
      destruct (Nat.eqb_spec x n) as [->|Hxn].
      + (* [n]'s own undo *)
        intros k'; unfold Rk, pend.
        rewrite Hpn by reflexivity; rewrite Nat.eqb_refl.
        cbn [set_life set_fiber with_fibers with_binds binds]; unfold bupd.
        destruct (keqb K_eq_dec k' k) eqn:Ek.
        * unfold keqb in Ek; destruct (K_eq_dec k' k) as [->|]; [|discriminate].
          rewrite Hσk; cbn [pid bst].
          rewrite Hpx, pend_list_uop_same in HRk; exact HRk.
        * unfold keqb in Ek; destruct (K_eq_dec k' k) as [|Hne]; [discriminate|].
          pose proof (HR k') as HRk'; unfold Rk, pend in HRk'.
          destruct (binds γ k') as [b'|]; [|exact HRk'].
          rewrite Hpx, pend_list_uop_other in HRk' by (left; exact (fun E => Hne (eq_sym E))).
          exact HRk'.
      + (* a foreign undo *)
        pose proof (commute_all (pend_list k (pid b) (pacc γ n)) g
                      (pend_commute γ x f k (pid b) t g acc w z (pid b) W PV Hx Hl Hxn)
                      (bst b)) as Hc.
        pose proof (undo_inv_respects γ x f k (pid b) t g acc w z PV Hx Hl _ _ HRk) as Hg.
        intros k'; unfold Rk, pend.
        rewrite Hpn by reflexivity.
        destruct (Nat.eqb_spec n x) as [E|_]; [congruence|].
        cbn [set_life set_fiber with_fibers with_binds binds]; unfold bupd, supd.
        destruct (keqb K_eq_dec k' k) eqn:Ek.
        * unfold keqb in Ek; destruct (K_eq_dec k' k) as [->|]; [|discriminate].
          rewrite Hσk; cbn [pid bst option_map].
          transitivity (g (apply_all (pend_list k (pid b) (pacc γ n)) (bst b)));
            [exact Hc | exact Hg].
        * pose proof (HR k') as HRk'; unfold Rk, pend in HRk'; exact HRk'.
    - destruct (relied Σ γ x p) eqn:Hr; [discriminate|].
      destruct (binds γ k) as [b|] eqn:Hb.
      2: { injection H as <-; cbn [shadow_apply].
           apply Hpop; [reflexivity | reflexivity | reflexivity]. }
      destruct (Nat.eqb_spec (pid b) p) as [Hp|Hp].
      2: { injection H as <-; cbn [shadow_apply].
           apply Hpop; [reflexivity | reflexivity | reflexivity]. }
      injection H as <-; cbn [shadow_apply].
      intros k'; unfold Rk, pend.
      rewrite Hpn by reflexivity.
      cbn [set_life set_fiber with_fibers with_binds binds]; unfold bupd, supd.
      destruct (keqb K_eq_dec k' k) eqn:Ek; [exact I|].
      pose proof (HR k') as HRk'; unfold Rk, pend in HRk'.
      destruct (binds γ k') as [b'|]; [|exact HRk'].
      destruct (Nat.eqb_spec n x) as [->|_]; [rewrite Hpx in HRk'|]; exact HRk'.
    - destruct (fibers γ m); [discriminate|].
      injection H as <-; cbn [shadow_apply].
      apply Hpop; [reflexivity | reflexivity | reflexivity].
  Qed.

  (** ** Every step preserves the invariant *)
  Theorem R_step (γ γ' : State) ℓ σ :
    WF γ -> Prov γ -> R γ σ -> step γ ℓ = Some γ' ->
    R γ' (shadow_apply (event γ ℓ) σ).
  Proof.
    intros W PV HR H.
    assert (Keep : forall γ1 x f (l : Life),
              fibers γ x = Some f -> fibers γ1 = fibers γ ->
              (forall k, binds γ1 k = binds γ k) -> acc_of l = acc_of (life f) ->
              R (set_life Σ γ1 x f l) σ).
    { intros γ1 x f l Hx Ef Eb Ea; apply (R_transfer γ); [exact Eb | | exact HR].
      apply (pend_list_keep γ γ1 x f l Hx); [unfold pacc; rewrite Ef; reflexivity|].
      intros; rewrite Ea; reflexivity. }
    destruct ℓ as [c|x|x|x|x|x|x|x|x|x|x|x i|x].
    - (* OInsert *)
      cbn [event shadow_apply]; cbn [step] in H.
      destruct (conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      apply (R_transfer γ); [intros; reflexivity | | exact HR].
      intros k p; unfold pacc; cbn; unfold fupd.
      destruct (Nat.eqb_spec n (next γ)) as [->|_]; [|reflexivity].
      rewrite (fresh_none K_eq_dec Σ prog γ W); reflexivity.
    - (* ODispose *)
      cbn [event shadow_apply]; cbn [step] in H.
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate]; injection H as <-.
      apply (R_transfer γ); [intros; reflexivity | | exact HR].
      intros k p; unfold pacc; cbn; unfold fupd.
      destruct (Nat.eqb_spec n x) as [->|_]; [rewrite Hx|]; reflexivity.
    - (* OReset *)
      cbn [event shadow_apply]; cbn [step] in H.
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate; injection H as <-.
      apply Keep; auto; rewrite Hl; reflexivity.
    - (* LBegin *)
      cbn [event shadow_apply]; cbn [step] in H.
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (target Σ prog γ x); [|discriminate]; injection H as <-.
      apply Keep; auto; rewrite Hl; reflexivity.
    - (* LStep *)
      cbn [step] in H.
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (may_step K_eq_dec Σ prog γ x P w) eqn:Ht; [|discriminate].
      injection H as <-.
      rewrite (event_LStep γ x f P acc w Hx Hl Ht).
      apply R_load; auto.
    - (* LDivert *)
      cbn [event shadow_apply]; cbn [step] in H.
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [discriminate|]; injection H as <-.
      apply Keep; auto; rewrite Hl; reflexivity.
    - (* LLeave *)
      cbn [event shadow_apply]; cbn [step] in H.
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (target_is K_eq_dec Σ prog γ x w); [discriminate|]; injection H as <-.
      apply Keep; auto; rewrite Hl; reflexivity.
    - (* LUndo *)
      cbn [step] in H.
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      unheld H.
      rewrite (event_LUndo γ x f u acc w z Hx Hl).
      eapply R_undo; eauto.
    - (* LRetireChild *)
      cbn [event shadow_apply]; cbn [step] in H.
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|[k p t g|k p|m0] acc] w z]; try discriminate.
      destruct (fibers γ m0) as [g|] eqn:Hg; [|discriminate].
      unheld H; destruct (Calculus.disposed Σ g); [discriminate|]; injection H as <-.
      apply (R_transfer γ); [intros; reflexivity | | exact HR].
      intros k p; unfold pacc; cbn; unfold fupd.
      destruct (Nat.eqb_spec n m0) as [->|_]; [rewrite Hg|]; reflexivity.
    - (* LUnloaded *)
      cbn [event shadow_apply]; cbn [step] in H.
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:Hl; try discriminate.
      injection H as <-; apply Keep; auto; rewrite Hl; reflexivity.
    - (* LRemove *)
      cbn [event shadow_apply]; cbn [step] in H.
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [z| | |] eqn:Hl; try discriminate.
      destruct (Calculus.disposed Σ f && negb (has_child Σ γ x)); [|discriminate].
      injection H as <-.
      apply (R_transfer γ); [intros; reflexivity | | exact HR].
      intros k p; unfold pacc; cbn; unfold fupd.
      destruct (Nat.eqb_spec n x) as [->|_]; [rewrite Hx, Hl|]; reflexivity.
    - (* OReact *)
      cbn [event shadow_apply]; cbn [step] in H.
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      destruct (nth_error (reacts Σ (prog (fcomp f))) i) as [c|]; [|discriminate].
      destruct (Calculus.disposed Σ f || conflict K_eq_dec Σ prog γ c); [discriminate|]; injection H as <-.
      apply (R_transfer γ); [intros; reflexivity | | exact HR].
      intros k p; unfold pacc; cbn; unfold fupd.
      destruct (Nat.eqb_spec n x) as [->|_]; [rewrite Hx, Hl; reflexivity|].
      destruct (Nat.eqb_spec n (next γ)) as [->|_]; [|reflexivity].
      rewrite (fresh_none K_eq_dec Σ prog γ W); reflexivity.
    - (* ORestart *)
      cbn [event shadow_apply]; cbn [step] in H.
      destruct (fibers γ x) as [f|] eqn:Hx; [|discriminate].
      destruct (Calculus.disposed Σ f); [discriminate|].
      destruct (life f) as [|P acc w|acc w|] eqn:Hl; try discriminate; injection H as <-;
      (apply Keep; auto; rewrite Hl; reflexivity).
  Qed.

  (** ** Executions *)
  Fixpoint shadow_run (γ : State) (ls : list (@Label C)) (σ : Store)
    : option (State * Store) :=
    match ls with
    | [] => Some (γ, σ)
    | ℓ :: ls' =>
        match step γ ℓ with
        | Some γ' => shadow_run γ' ls' (shadow_apply (event γ ℓ) σ)
        | None => None
        end
    end.

  (** The shadow follows every execution, and only executions. *)
  Lemma shadow_run_total (γ : State) ls σ γ' :
    run_labels K_eq_dec Σ prog γ ls = Some γ' ->
    exists σ', shadow_run γ ls σ = Some (γ', σ').
  Proof.
    revert γ σ; induction ls as [|ℓ ls IH]; cbn; intros γ σ H.
    - injection H as <-; eauto.
    - destruct (step γ ℓ); [apply IH; exact H | discriminate].
  Qed.

  Lemma shadow_run_sound (γ : State) ls σ γ' σ' :
    shadow_run γ ls σ = Some (γ', σ') -> run_labels K_eq_dec Σ prog γ ls = Some γ'.
  Proof.
    revert γ σ; induction ls as [|ℓ ls IH]; cbn; intros γ σ H.
    - injection H as <- _; reflexivity.
    - destruct (step γ ℓ); [eapply IH; exact H | discriminate].
  Qed.

  Theorem recovery (γ : State) ls σ γ' σ' :
    WF γ -> Prov γ -> R γ σ -> shadow_run γ ls σ = Some (γ', σ') ->
    WF γ' /\ Prov γ' /\ R γ' σ'.
  Proof.
    revert γ σ; induction ls as [|ℓ ls IH]; cbn; intros γ σ W PV HR H.
    - injection H as <- <-; auto.
    - destruct (step γ ℓ) as [γ1|] eqn:Hs; [|discriminate].
      apply (IH γ1 _ (preservation K_eq_dec Σ prog γ γ1 ℓ W Hs)
                (prov_step γ γ1 ℓ W PV Hs) (R_step γ γ1 ℓ σ W PV HR Hs) H).
  Qed.

  (** ** Recovery exactness

      Start from a state where [n] holds no pending operation, run any
      execution, and end at a state where [n] again holds none (for
      instance, [n] has unloaded, or never loaded). Then the real store
      agrees with the shadow store, which applied every other fiber's
      operations and undos but none of [n]'s. *)
  Definition no_pending (γ : State) : Prop := forall k p, pend_list k p (pacc γ n) = [].

  Theorem recovery_exact (γ0 : State) ls γ σ :
    WF γ0 -> Prov γ0 -> no_pending γ0 ->
    shadow_run γ0 ls (store γ0) = Some (γ, σ) -> no_pending γ ->
    forall k, match binds γ k, σ k with
              | Some b, Some s => bst b ≃ s
              | None, None => True
              | _, _ => False
              end.
  Proof.
    intros W PV H0 Hrun H1 k.
    destruct (recovery γ0 ls (store γ0) γ σ W PV (R_store γ0 H0) Hrun) as (_ & _ & HR).
    specialize (HR k); unfold Rk, pend in HR.
    destruct (binds γ k) as [b|]; [rewrite H1 in HR|]; exact HR.
  Qed.

  Lemma no_pending_inactive (γ : State) :
    match fibers γ n with Some f => is_installed Σ (life f) = false | None => True end ->
    no_pending γ.
  Proof.
    intros H k p; unfold pacc; destruct (fibers γ n) as [f|]; [|reflexivity].
    destruct (life f); cbn in H |- *; first [reflexivity | discriminate].
  Qed.

  (** From the initial state: whenever [n] is not installed, the store is,
      up to ≃, what every other fiber's operations alone produce. *)
  Corollary recovery_from_init ls γ σ :
    shadow_run (@init K Σ C) ls (fun _ => None) = Some (γ, σ) ->
    match fibers γ n with Some f => is_installed Σ (life f) = false | None => True end ->
    forall k, match binds γ k, σ k with
              | Some b, Some s => bst b ≃ s
              | None, None => True
              | _, _ => False
              end.
  Proof.
    intros Hrun Hn.
    apply (recovery_exact (@init K Σ C) ls); auto.
    - exact (wf_init K_eq_dec Σ prog).
    - exact prov_init.
    - intros k p; reflexivity.
    - apply no_pending_inactive; exact Hn.
  Qed.
End Recovery.
