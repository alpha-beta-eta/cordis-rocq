(** * Who may move a value, on extended executions

    The core's [Ordering.decl_step] and [value_moves] (the second half of the
    paper's Theorem 70(3)): an operation undo item sits only in the
    accumulator of a fiber that declares or provides its key, and across a
    step that keeps a binding's pid, its value is unchanged or moved by an
    [L-Step] or [L-Undo] of such a fiber. Both carry over to the two
    extensions that change the step relation.

    - Optional dependencies: a fiber may also read a present optional key.
      Re-choosing presence touches only an Inactive fiber, which holds no
      undo item, and moves no binding ([xdecl_step], [xvalue_moves]).
    - Payload-indexed reactions: the instantiated tables declare the same
      keys ([idecl_step], [ivalue_moves]). *)

From Stdlib Require Import List PeanoNat Bool.
From Cordis Require Import Prelude Service Calculus Preservation Ordering Recovery Progress.
From Cordis Require Import Ext.Optional Ext.OptProgress Ext.Intersect.
Import ListNotations.

(** ** Optional dependencies *)
Section OptOrdering.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type}.
  Context (xprog : C -> @XComponent K Σ C).

  Local Notation CC := (@Optional.C' K C).
  Local Notation State := (@State K Σ CC).
  Local Notation Fiber := (@Fiber K Σ CC).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation prog' := (prog' K_eq_dec Σ xprog).
  Local Notation xstep := (xstep K_eq_dec Σ xprog).
  Local Notation recomp := (recomp Σ xprog).
  Local Notation WF := (WF K_eq_dec Σ prog').
  Local Notation Decl := (Decl K_eq_dec Σ prog').

  (** [k] is one of the keys the base component may read or provide. *)
  Definition XDeclares (f : Fiber) (k : K) : Prop :=
    let xc := xprog (fst (fcomp f)) in In k (xdeps Σ xc) \/ In k (xopt Σ xc) \/ In k (xprovs Σ xc).

  Lemma declares_x (f : Fiber) k : Declares K_eq_dec Σ prog' f k -> XDeclares f k.
  Proof.
    unfold Declares, XDeclares, Optional.prog'; cbn [deps provs].
    intros [H|H]; apply (kmem_In K_eq_dec) in H.
    - apply in_app_or in H as [H|H]; [left; exact H|].
      right; left; apply filter_In in H as [_ H].
      apply (kmem_In K_eq_dec) in H; exact H.
    - right; right; exact H.
  Qed.

  Lemma decl_recomp (γ : State) n f :
    Decl γ -> fibers γ n = Some f -> is_installed Σ (life f) = false -> Decl (recomp γ n f).
  Proof.
    intros D Hn Hi m fm H; rewrite fibers_recomp in H.
    destruct (Nat.eqb_spec m n) as [->|]; [|exact (D m fm H)].
    injection H as <-; intros k p t g Hin; cbn in Hin.
    destruct (life f); try discriminate; destruct Hin.
  Qed.

  Theorem xdecl_step (γ γ' : State) ℓ : WF γ -> Decl γ -> xstep γ ℓ = Some γ' -> Decl γ'.
  Proof.
    intros W D H.
    destruct (xstep_core K_eq_dec Σ xprog γ γ' ℓ H) as [S|[(m & f & _ & Hm & Hl & S)|(m & S)]].
    - exact (decl_step K_eq_dec Σ prog' γ γ' _ W D S).
    - assert (Hi : is_installed Σ (life f) = false) by (rewrite Hl; reflexivity).
      exact (decl_step K_eq_dec Σ prog' _ γ' _ (wf_recomp K_eq_dec Σ xprog γ m f W Hm Hi)
               (decl_recomp γ m f D Hm Hi) S).
    - exact (decl_step K_eq_dec Σ prog' γ γ' _ W D S).
  Qed.

  Corollary xdecl_reachable (γ : State) : XReachable K_eq_dec Σ xprog γ -> Decl γ.
  Proof.
    intros [ls H].
    assert (G : forall γ0, WF γ0 -> Decl γ0 -> xrun K_eq_dec Σ xprog γ0 ls = Some γ -> Decl γ).
    { clear H; induction ls as [|ℓ ls IH]; cbn; intros γ0 W0 D0 H0.
      - injection H0 as <-; exact D0.
      - destruct (xstep γ0 ℓ) as [γ1|] eqn:Hs; [|discriminate].
        exact (IH γ1 (xpreservation K_eq_dec Σ xprog γ0 γ1 ℓ W0 Hs) (xdecl_step γ0 γ1 ℓ W0 D0 Hs) H0). }
    exact (G _ (wf_init K_eq_dec Σ prog') (decl_init K_eq_dec Σ prog') H).
  Qed.

  (** Across an extended step that keeps a binding's pid, its value is
      unchanged or moved by an [L-Step] or [L-Undo] of a fiber whose base
      component reads or provides the key. *)
  Theorem xvalue_moves (γ γ' : State) ℓ k b b' :
    WF γ -> Decl γ -> xstep γ ℓ = Some γ' ->
    binds γ k = Some b -> binds γ' k = Some b' -> pid Σ b' = pid Σ b ->
    b' = b \/ exists n f, fibers γ n = Some f /\ (ℓ = LStep n \/ ℓ = LUndo n) /\ XDeclares f k.
  Proof.
    intros W D H Hb Hb' Hp.
    destruct (xstep_core K_eq_dec Σ xprog γ γ' ℓ H) as [S|[(m & f & -> & Hm & Hl & S)|(m & S)]].
    - destruct (value_moves K_eq_dec Σ prog' γ γ' _ k b b' W D S Hb Hb' Hp) as [E|(n & fn & Hn & Hlab & Hd)];
        [left; exact E | right; exists n, fn; split; [exact Hn|]; split; [|exact (declares_x fn k Hd)]].
      destruct ℓ; cbn [xlab] in Hlab; destruct Hlab as [E|E]; try discriminate E;
        injection E as ->; auto.
    - assert (Hi : is_installed Σ (life f) = false) by (rewrite Hl; reflexivity).
      destruct (value_moves K_eq_dec Σ prog' _ γ' _ k b b' (wf_recomp K_eq_dec Σ xprog γ m f W Hm Hi)
                  (decl_recomp γ m f D Hm Hi) S Hb Hb' Hp) as [E|(n & fn & _ & [E|E] & _)];
        [left; exact E | discriminate E | discriminate E].
    - destruct (value_moves K_eq_dec Σ prog' γ γ' _ k b b' W D S Hb Hb' Hp) as [E|(n & fn & _ & [E|E] & _)];
        [left; exact E | discriminate E | discriminate E].
  Qed.
End OptOrdering.

(** ** Payload-indexed reactions *)
Section IOrdering.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} {E : Type}.
  Context (iprog : C -> @IComponent K Σ C E).

  Local Notation State := (@State K Σ C).
  Local Notation progE := (progE Σ iprog).
  Local Notation progN := (progE None).
  Local Notation istep := (istep K_eq_dec Σ iprog).

  Lemma decl_tables x y (γ : State) : Decl K_eq_dec Σ (progE x) γ -> Decl K_eq_dec Σ (progE y) γ.
  Proof. intros D; exact D. Qed.

  Theorem idecl_step (γ γ' : State) ℓ :
    WF K_eq_dec Σ progN γ -> Decl K_eq_dec Σ progN γ -> istep γ ℓ = Some γ' -> Decl K_eq_dec Σ progN γ'.
  Proof.
    intros W D; destruct ℓ as [ℓ|n i e]; cbn [Intersect.istep]; intros H.
    - exact (decl_step K_eq_dec Σ progN γ γ' ℓ W D H).
    - apply (decl_tables (Some e) None).
      exact (decl_step K_eq_dec Σ (progE (Some e)) γ γ' _ (wf_tables K_eq_dec Σ iprog None (Some e) γ W)
               (decl_tables None (Some e) γ D) H).
  Qed.

  Corollary idecl_reachable (γ : State) : IReachable K_eq_dec Σ iprog γ -> Decl K_eq_dec Σ progN γ.
  Proof.
    intros R.
    assert (G : WF K_eq_dec Σ progN γ /\ Decl K_eq_dec Σ progN γ).
    { revert γ R; apply irun_inv.
      - split; [exact (wf_init K_eq_dec Σ progN) | exact (decl_init K_eq_dec Σ progN)].
      - intros γ0 γ1 ℓ [W D] H; split; [exact (ipreservation K_eq_dec Σ iprog γ0 γ1 ℓ W H)|].
        exact (idecl_step γ0 γ1 ℓ W D H). }
    exact (proj2 G).
  Qed.

  Theorem ivalue_moves (γ γ' : State) ℓ k b b' :
    WF K_eq_dec Σ progN γ -> Decl K_eq_dec Σ progN γ -> istep γ ℓ = Some γ' ->
    binds Σ γ k = Some b -> binds Σ γ' k = Some b' -> pid Σ b' = pid Σ b ->
    b' = b \/ exists n f, fibers Σ γ n = Some f /\ (ℓ = ICore (LStep n) \/ ℓ = ICore (LUndo n)) /\
                          Declares K_eq_dec Σ progN f k.
  Proof.
    intros W D; destruct ℓ as [ℓ|n i e]; cbn [Intersect.istep]; intros H Hb Hb' Hp.
    - destruct (value_moves K_eq_dec Σ progN γ γ' ℓ k b b' W D H Hb Hb' Hp) as [Eq|(n & f & Hn & [->| ->] & Hd)];
        [left; exact Eq | right; exists n, f; auto | right; exists n, f; auto].
    - destruct (value_moves K_eq_dec Σ (progE (Some e)) γ γ' _ k b b' (wf_tables K_eq_dec Σ iprog None (Some e) γ W)
                  (decl_tables None (Some e) γ D) H Hb Hb' Hp) as [Eq|(m & f & _ & [Eq|Eq] & _)];
        [left; exact Eq | discriminate Eq | discriminate Eq].
  Qed.
End IOrdering.
