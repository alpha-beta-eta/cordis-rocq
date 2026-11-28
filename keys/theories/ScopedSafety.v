(** * Hygienic keys: scopes are unique, so nothing conflicts

    Along every extended execution, the present fibers have pairwise
    different scopes ([si_reachable]). With [Scoped.conflict_scope] this
    turns the conflict checks of the core into dead code:
    - an insertion under an instance id not in use never conflicts
      ([insert_enabled]);
    - a spawn never conflicts ([spawn_ok]);
    - a reaction never conflicts ([react_enabled]);
    - a binding at a fiber's own scope is the fiber's own ([provide_self]),
      so [PProvide] meets a binding only when the same fiber provided the
      name before.

    The invariant [SI]:
    - [si_uniq]: scopes of present fibers are pairwise different;
    - [si_bound]: every root name and reaction stamp in a present scope is
      below [next], so the scopes made from [next] are new;
    - [si_parent]: a fiber of scope [Sp j :: s] has a present parent of
      scope [s];
    - [si_load]: a Loading fiber runs [lift x j Q] for its component [x],
      and its present children of the form [Sp j' :: scope x] have
      [j' < j], so the next spawn is new.

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service Calculus Preservation.
From CordisKeys Require Import Scoped.
Import ListNotations.

Section ScopedSafety.
  Context {N : Type} (N_eq_dec : forall x y : N, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (xprog : C -> @XComponent N Σ C).

  Local Notation XC := (@XC N C).
  Local Notation Key := (@Key N).
  Local Notation State := (@State Key Σ XC).
  Local Notation Fiber := (@Fiber Key Σ XC).
  Local Notation Label := (@Label XC).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation fparent := (Calculus.parent Σ).
  Local Notation next := (next Σ).
  Local Notation kdec := (key_eq_dec N_eq_dec).
  Local Notation prog' := (prog' N_eq_dec Σ xprog).
  Local Notation lift := (lift N_eq_dec Σ xprog).
  Local Notation child := (child N_eq_dec Σ xprog).
  Local Notation handlers := (handlers N_eq_dec Σ xprog).
  Local Notation inherit := (inherit N_eq_dec Σ xprog).
  Local Notation step := (step kdec Σ prog').
  Local Notation WF := (WF kdec Σ prog').
  Local Notation conflict := (conflict kdec Σ prog').
  Local Notation kstep := (kstep N_eq_dec Σ xprog).
  Local Notation KReachable := (KReachable N_eq_dec Σ xprog).

  (** ** The invariant *)
  Definition segb (g : Seg) : nat := match g with Rt _ => 0 | Sp _ => 0 | Re _ t => t end.

  Definition Bounded (nx : nat) (s : Scope) : Prop := forall g, In g s -> segb g < nx.

  (** The present children of the form [Sp j' :: s] have [j' < j]. *)
  Definition Kids (γ : State) (s : Scope) (j : nat) : Prop :=
    forall m fm j', fibers γ m = Some fm -> scope (fcomp fm) = Sp j' :: s -> j' < j.

  Definition LoadOK (γ : State) (f : Fiber) : Prop :=
    forall P acc w, life f = Loading Σ P acc w ->
      exists j Q, P = lift (fcomp f) j Q /\ Kids γ (scope (fcomp f)) j.

  Record SI (γ : State) : Prop := {
    si_uniq : forall m m' fm fm', fibers γ m = Some fm -> fibers γ m' = Some fm' ->
              scope (fcomp fm) = scope (fcomp fm') -> m = m';
    si_bound : forall m fm, fibers γ m = Some fm -> Bounded (next γ) (scope (fcomp fm));
    si_parent : forall m fm j s, fibers γ m = Some fm -> scope (fcomp fm) = Sp j :: s ->
              exists q fq, fparent fm = Some q /\ fibers γ q = Some fq /\ scope (fcomp fq) = s;
    si_load : forall m fm, fibers γ m = Some fm -> LoadOK γ fm;
    si_ne : forall m fm, fibers γ m = Some fm -> scope (fcomp fm) <> [];
    si_child : forall m fm q fq, fibers γ m = Some fm -> fparent fm = Some q -> fibers γ q = Some fq ->
               sel (fcomp fm) = inherit (fcomp fq) (base (fcomp fm))
  }.

  Lemma si_init : SI (@init Key Σ XC).
  Proof. split; cbn; intros; discriminate. Qed.

  Lemma bounded_mono nx nx' s : Bounded nx s -> nx <= nx' -> Bounded nx' s.
  Proof. intros B L g I; specialize (B g I); lia. Qed.

  Lemma not_loading_ok (γ : State) f :
    (forall P acc w, life f <> Loading Σ P acc w) -> LoadOK γ f.
  Proof. intros H P acc w L; exfalso; exact (H P acc w L). Qed.

  (** ** How a step changes the fibers *)

  (** [γ'] is [γ] with fibers changed in place (component and parent kept,
      life kept except at [n]), some removed, and possibly a new fiber at
      [next γ]. *)
  Definition Shape (γ γ' : State) (n : nat) (new : option Fiber) : Prop :=
    next γ <= next γ' /\
    (forall nf, new = Some nf -> next γ < next γ') /\
    forall m fm', fibers γ' m = Some fm' ->
      (exists nf, new = Some nf /\ m = next γ /\ fm' = nf) \/
      (exists fm, fibers γ m = Some fm /\ fcomp fm' = fcomp fm /\ fparent fm' = fparent fm /\
                  (m <> n -> life fm' = life fm)).

  (** What a new fiber must satisfy. *)
  Definition NewOK (γ γ' : State) (n : nat) (nf : Fiber) : Prop :=
    Bounded (next γ') (scope (fcomp nf)) /\
    (forall m fm, fibers γ m = Some fm -> scope (fcomp fm) <> scope (fcomp nf)) /\
    (forall j s, scope (fcomp nf) = Sp j :: s ->
       fparent nf = Some n /\ exists fn, fibers γ n = Some fn /\ scope (fcomp fn) = s) /\
    (forall P acc w, life nf <> Loading Σ P acc w) /\
    scope (fcomp nf) <> [] /\
    (fparent nf = None \/
     (fparent nf = Some n /\ exists fn, fibers γ n = Some fn /\ sel (fcomp nf) = inherit (fcomp fn) (base (fcomp nf)))).

  Lemma si_shape (γ γ' : State) n new :
    WF γ -> SI γ -> WF γ' -> Shape γ γ' n new ->
    (forall nf, new = Some nf -> NewOK γ γ' n nf) ->
    (forall fn', fibers γ' n = Some fn' -> LoadOK γ' fn') ->
    SI γ'.
  Proof.
    intros W S W' [Hle [Hlt Hsh]] Hnew Hn.
    assert (Hfresh : fibers γ (next γ) = None) by exact (fresh_none kdec Σ prog' γ W).
    assert (Hkids : forall s j, Kids γ s j ->
              (forall nf, new = Some nf -> forall j', scope (fcomp nf) = Sp j' :: s -> j' < j) ->
              Kids γ' s j).
    { intros s j K Kn m fm j' Hm Hs.
      destruct (Hsh m fm Hm) as [(nf & En & -> & ->)|(fm0 & H0 & Ec & _ & _)].
      - exact (Kn nf En j' Hs).
      - rewrite Ec in Hs; exact (K m fm0 j' H0 Hs). }
    split.
    - intros m m' fm fm' Hm Hm' Es.
      destruct (Hsh m fm Hm) as [(nf & En & -> & ->)|(fm0 & H0 & Ec & _ & _)];
      destruct (Hsh m' fm' Hm') as [(nf' & En' & -> & ->)|(fm0' & H0' & Ec' & _ & _)].
      + reflexivity.
      + exfalso; destruct (Hnew nf En) as (_ & D & _); apply (D _ fm0' H0'); congruence.
      + exfalso; destruct (Hnew nf' En') as (_ & D & _); apply (D _ fm0 H0); congruence.
      + apply (si_uniq γ S m m' fm0 fm0' H0 H0'); congruence.
    - intros m fm Hm.
      destruct (Hsh m fm Hm) as [(nf & En & -> & ->)|(fm0 & H0 & Ec & _ & _)].
      + destruct (Hnew nf En) as (B & _); exact B.
      + rewrite Ec; exact (bounded_mono _ _ _ (si_bound γ S m fm0 H0) Hle).
    - intros m fm j s Hm Hs.
      assert (Hpar : forall q fq, fibers γ q = Some fq -> fparent fm = Some q ->
                exists fq', fibers γ' q = Some fq' /\ scope (fcomp fq') = scope (fcomp fq)).
      { intros q fq Hq Pq.
        destruct (wf_parent _ _ _ _ W' m fm q Hm Pq) as (fq' & Hq' & _ & _).
        exists fq'; split; [exact Hq'|].
        destruct (Hsh q fq' Hq') as [(nf & En & Eq & ->)|(fq0 & H0 & Ec & _ & _)].
        - subst q; rewrite Hfresh in Hq; discriminate.
        - rewrite Hq in H0; injection H0 as <-; rewrite Ec; reflexivity. }
      destruct (Hsh m fm Hm) as [(nf & En & -> & ->)|(fm0 & H0 & Ec & Ep & _)].
      + destruct (Hnew nf En) as (_ & _ & Hsp & _).
        destruct (Hsp j s Hs) as (Pn & fn & Hn0 & En0).
        destruct (Hpar n fn Hn0 Pn) as (fq' & Hq' & Eq').
        exists n, fq'; split; [exact Pn|]; split; [exact Hq'|]; congruence.
      + rewrite Ec in Hs; destruct (si_parent γ S m fm0 j s H0 Hs) as (q & fq & Pq & Hq & Eq).
        rewrite <- Ep in Pq.
        destruct (Hpar q fq Hq Pq) as (fq' & Hq' & Eq').
        exists q, fq'; split; [exact Pq|]; split; [exact Hq'|]; congruence.
    - intros m fm Hm.
      destruct (Nat.eq_dec m n) as [->|Hne]; [exact (Hn fm Hm)|].
      destruct (Hsh m fm Hm) as [(nf & En & Em & ->)|(fm0 & H0 & Ec & _ & El)].
      + destruct (Hnew nf En) as (_ & _ & _ & NL & _); exact (not_loading_ok γ' nf NL).
      + intros P acc w L; rewrite (El Hne) in L.
        destruct (si_load γ S m fm0 H0 P acc w L) as (j & Q & EP & K).
        exists j, Q; rewrite Ec; split; [exact EP|].
        apply Hkids; [exact K|].
        intros nf En j' Hs.
        destruct (Hnew nf En) as (_ & _ & Hsp & _).
        destruct (Hsp j' _ Hs) as (_ & fn & Hn0 & En0).
        exfalso; apply Hne; exact (si_uniq γ S m n fm0 fn H0 Hn0 (eq_sym En0)).
    - intros m fm Hm.
      destruct (Hsh m fm Hm) as [(nf & En & -> & ->)|(fm0 & H0 & Ec & _ & _)].
      + destruct (Hnew nf En) as (_ & _ & _ & _ & Ne & _); exact Ne.
      + rewrite Ec; exact (si_ne γ S m fm0 H0).
    - intros m fm q fq Hm Hp Hq.
      destruct (Hsh m fm Hm) as [(nf & En & Em & ->)|(fm0 & H0 & Ec & Ep & _)].
      + destruct (Hnew nf En) as (_ & _ & _ & _ & _ & [Hc|(Hc & fn & Hn0 & Es)]); [congruence|].
        rewrite Hp in Hc; injection Hc as ->.
        destruct (Hsh n fq Hq) as [(nf' & En' & En2 & _)|(fn0 & Hn1 & Ecn & _)].
        * exfalso; rewrite En2, Hfresh in Hn0; discriminate.
        * rewrite Hn0 in Hn1; injection Hn1 as <-; rewrite Ecn; exact Es.
      + rewrite Ep in Hp.
        destruct (wf_parent _ _ _ _ W m fm0 q H0 Hp) as (fq0 & Hq0 & _ & _).
        destruct (Hsh q fq Hq) as [(nf' & En' & En2 & _)|(fq1 & Hq1 & Ecq & _)].
        * exfalso; rewrite En2, Hfresh in Hq0; discriminate.
        * rewrite Hq0 in Hq1; injection Hq1 as <-.
          rewrite Ec, Ecq; exact (si_child γ S m fm0 q fq0 H0 Hp Hq0).
  Qed.

  Lemma kids_none (γ γ' : State) n s j :
    Shape γ γ' n None -> Kids γ s j -> Kids γ' s j.
  Proof.
    intros (_ & _ & Hsh) K m fm j' Hm Hs.
    destruct (Hsh m fm Hm) as [(nf & En & _)|(fm0 & H0 & Ec & _)]; [discriminate|].
    rewrite Ec in Hs; exact (K m fm0 j' H0 Hs).
  Qed.

  Lemma kids_spawn (γ γ' : State) n nf s j :
    Shape γ γ' n (Some nf) -> scope (fcomp nf) = Sp j :: s -> Kids γ s j -> Kids γ' s (S j).
  Proof.
    intros (_ & _ & Hsh) En K m fm j' Hm Hs.
    destruct (Hsh m fm Hm) as [(nf' & En' & _ & ->)|(fm0 & H0 & Ec & _)].
    - injection En' as <-; rewrite En in Hs; injection Hs as ->; lia.
    - rewrite Ec in Hs; specialize (K m fm0 j' H0 Hs); lia.
  Qed.

  Lemma shape_life (γ γ1 : State) n f l :
    fibers γ1 = fibers γ -> next γ <= next γ1 -> fibers γ n = Some f ->
    Shape γ (set_life Σ γ1 n f l) n None.
  Proof.
    intros EF Le Hn; split; [exact Le|]; split; [discriminate|].
    intros m fm' H; right.
    apply (fibers_set_life_inv Σ) in H as [[-> ->]|[Hne H]].
    - exists f; split; [exact Hn|]; split; [reflexivity|]; split; [reflexivity|].
      intros E; exfalso; apply E; reflexivity.
    - rewrite EF in H; exists fm'; split; [exact H|]; split; [reflexivity|].
      split; [reflexivity|]; intros _; reflexivity.
  Qed.

  Lemma shape_new (γ : State) n f l nf :
    fibers γ n = Some f -> n <> next γ ->
    Shape γ (set_life Σ (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ) (Some nf)))) n f l)
          n (Some nf).
  Proof.
    intros Hn Hne; split; [cbn; lia|]; split; [intros; cbn; lia|].
    intros m fm' H; apply (fibers_set_life_inv Σ) in H as [[-> ->]|[Hm H]].
    - right; exists f; split; [exact Hn|]; split; [reflexivity|]; split; [reflexivity|].
      intros E; exfalso; apply E; reflexivity.
    - cbn in H; unfold fupd in H; destruct (Nat.eqb_spec m (next γ)) as [->|Hm'].
      + left; exists nf; injection H as <-; auto.
      + right; exists fm'; split; [exact H|]; split; [reflexivity|].
        split; [reflexivity|]; intros _; reflexivity.
  Qed.

  Lemma shape_insert (γ : State) n nf :
    Shape γ (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ) (Some nf)))) n (Some nf).
  Proof.
    split; [cbn; lia|]; split; [intros; cbn; lia|].
    intros m fm' H; cbn in H; unfold fupd in H; destruct (Nat.eqb_spec m (next γ)) as [->|Hm].
    - left; exists nf; injection H as <-; auto.
    - right; exists fm'; split; [exact H|]; split; [reflexivity|].
      split; [reflexivity|]; intros _; reflexivity.
  Qed.

  Lemma shape_remove (γ : State) n :
    Shape γ (with_fibers Σ γ (fupd Σ (fibers γ) n None)) n None.
  Proof.
    split; [cbn; lia|]; split; [discriminate|].
    intros m fm' H; cbn in H; unfold fupd in H; destruct (Nat.eqb_spec m n) as [->|Hm];
      [discriminate|].
    right; exists fm'; split; [exact H|]; split; [reflexivity|].
    split; [reflexivity|]; intros _; reflexivity.
  Qed.

  (** Re-marking a fiber's [disposed] flag. *)
  Lemma si_refiber (γ : State) m g b :
    WF γ -> SI γ -> fibers γ m = Some g ->
    WF (set_fiber Σ γ m (mkFiber Σ (fcomp g) (fparent g) b (life g))) ->
    SI (set_fiber Σ γ m (mkFiber Σ (fcomp g) (fparent g) b (life g))).
  Proof.
    intros W S Hm W'.
    assert (Sh : Shape γ (set_fiber Σ γ m (mkFiber Σ (fcomp g) (fparent g) b (life g))) m None).
    { split; [cbn; lia|]; split; [discriminate|].
      intros m' fm' H; right; apply (fibers_set_fiber_inv Σ) in H as [[-> ->]|[_ H]].
      - exists g; split; [exact Hm|]; cbn; auto.
      - exists fm'; split; [exact H|]; auto. }
    apply (si_shape γ _ m None W S W' Sh); [discriminate|].
    intros fn' E; apply (fibers_set_fiber_inv Σ) in E as [[_ ->]|[Hne _]]; [|congruence].
    intros P acc w L; cbn in L.
    destruct (si_load γ S m g Hm P acc w L) as (j & Q & EP & K).
    exists j, Q; split; [exact EP|]; exact (kids_none _ _ _ _ _ Sh K).
  Qed.

  Lemma loadok_set_life (γ1 γ' : State) n f l :
    (forall P acc w, l <> Loading Σ P acc w) ->
    forall fn', fibers (set_life Σ γ1 n f l) n = Some fn' -> LoadOK γ' fn'.
  Proof.
    intros H fn' E; rewrite (fibers_set_life Σ), Nat.eqb_refl in E; injection E as <-.
    apply not_loading_ok; exact H.
  Qed.

  Lemma loadok_loading (γ1 γ' : State) n f acc w j Q :
    Kids γ' (scope (fcomp f)) j ->
    forall fn', fibers (set_life Σ γ1 n f (Loading Σ (lift (fcomp f) j Q) acc w)) n = Some fn' ->
    LoadOK γ' fn'.
  Proof.
    intros K fn' E; rewrite (fibers_set_life Σ), Nat.eqb_refl in E; injection E as <-.
    intros P' acc' w' L; cbn in L; injection L as <- <- <-; exists j, Q; cbn; auto.
  Qed.

  (** ** One Loading step of a lifted program *)
  Lemma load_step_lift (γ : State) n f j Q acc w :
    (exists γ1 l, load_step kdec Σ prog' γ n f (lift (fcomp f) j Q) acc w = set_life Σ γ1 n f l /\
       fibers γ1 = fibers γ /\ next γ <= next γ1 /\
       ((forall P acc w, l <> Loading Σ P acc w) \/
        exists Q' acc', l = Loading Σ (lift (fcomp f) j Q') acc' w)) \/
    (exists c Q', conflict γ (child (fcomp f) (Sp j) c) = false /\
       load_step kdec Σ prog' γ n f (lift (fcomp f) j Q) acc w =
       set_life Σ (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ)
            (Some (mkFiber Σ (child (fcomp f) (Sp j) c) (Some n) false (Inactive Σ None))))))
            n f (Loading Σ (lift (fcomp f) (S j) Q') (USpawn Σ (next γ) :: acc) w)).
  Proof.
    Ltac done_l :=
      left; eexists _, _; split; [reflexivity|]; split; [reflexivity|]; split; [cbn; lia|];
      first [left; intros ? ? ?; discriminate | right; eexists _, _; reflexivity].
    destruct Q as [| |y a κ|y st Q'|c Q']; cbn [Scoped.lift load_step].
    - done_l.
    - done_l.
    - repeat match goal with
             | |- context [match ?e with _ => _ end] => destruct e
             end; done_l.
    - repeat match goal with
             | |- context [match ?e with _ => _ end] => destruct e
             end; done_l.
    - destruct (conflict γ (child (fcomp f) (Sp j) c)) eqn:Ec; [done_l|].
      right; exists c, Q'; split; [exact Ec | reflexivity].
  Qed.

  Lemma undo_next (γ γ' : State) n f u acc w z :
    undo_step kdec Σ γ n f u acc w z = Some γ' ->
    exists γ1, γ' = set_life Σ γ1 n f (Unloading Σ acc w z) /\
               fibers γ1 = fibers γ /\ next γ1 = next γ.
  Proof.
    destruct u as [k p t g|k p|m]; cbn [undo_step].
    - destruct (binds γ k) as [b|]; [destruct (Nat.eqb (pid Σ b) p)|];
        intros [= <-]; eexists; repeat split.
    - destruct (relied Σ γ n p); [discriminate|].
      destruct (binds γ k) as [b|]; [destruct (Nat.eqb (pid Σ b) p)|];
        intros [= <-]; eexists; repeat split.
    - destruct (fibers γ m); [discriminate|].
      intros [= <-]; eexists; repeat split.
  Qed.

  Lemma nth_handlers (x : XC) k cs i :
    nth_error (handlers x k cs) i = option_map (fun c => child x (Re (k + i) (tick x)) c) (nth_error cs i).
  Proof.
    revert k i; induction cs as [|c cs IH]; intros k [|i]; cbn; auto.
    - rewrite Nat.add_0_r; reflexivity.
    - rewrite IH, Nat.add_succ_r; reflexivity.
  Qed.

  (** ** Preservation by core steps *)

  (** The labels the extension sends to the core: an insertion at a root
      scope no present fiber has, a reaction at a fiber stamped with
      [next]. *)
  Definition Good (γ : State) (ℓ : Label) : Prop :=
    match ℓ with
    | OInsert x => (exists i, scope x = [Rt i]) /\
                   forall m f, fibers γ m = Some f -> scope (fcomp f) <> scope x
    | OReact n _ => exists f, fibers γ n = Some f /\ tick (fcomp f) = next γ
    | _ => True
    end.

  Theorem si_step (γ γ' : State) ℓ :
    WF γ -> SI γ -> Good γ ℓ -> step γ ℓ = Some γ' -> SI γ'.
  Proof.
    intros W S G H.
    pose proof (preservation kdec Σ prog' γ γ' ℓ W H) as W'.
    assert (Hfresh : fibers γ (next γ) = None) by exact (fresh_none kdec Σ prog' γ W).
    assert (Hne : forall m fm, fibers γ m = Some fm -> m <> next γ).
    { intros m fm Hm E; subst m; congruence. }
    assert (NotNew : forall s, Bounded (next γ) s -> forall i, ~ In (Re i (next γ)) s).
    { intros s B i I; specialize (B _ I); cbn in B; lia. }
    destruct ℓ as [x|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [Calculus.step] in H; cbn [Good] in G.
    - (* OInsert *)
      destruct (conflict γ x); [discriminate|]; injection H as <-.
      apply (si_shape γ _ (next γ) _ W S W' (shape_insert γ _ _)).
      + intros nf [= <-]; unfold NewOK; cbn [Calculus.comp Calculus.parent Calculus.life].
        destruct G as [(i & Ei) Fr]; split; [|split; [|split]].
        * rewrite Ei; intros g [<-|[]]; cbn; lia.
        * exact Fr.
        * rewrite Ei; discriminate.
        * split; [discriminate|]; split; [rewrite Ei; discriminate|]; left; reflexivity.
      + intros fn' E; cbn in E; unfold fupd in E; rewrite Nat.eqb_refl in E; injection E as <-.
        apply not_loading_ok; discriminate.
    - (* ODispose *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate]; injection H as <-.
      exact (si_refiber γ n f true W S Hn W').
    - (* OReset *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [[z|]| | |]; try discriminate; injection H as <-.
      apply (si_shape γ _ n None W S W' (shape_life γ γ n f _ eq_refl (le_n _) Hn)); [discriminate|].
      apply loadok_set_life; discriminate.
    - (* LBegin *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (target Σ prog' γ n) as [w|]; destruct (life f) as [[z|]| | |] eqn:Hl;
        try discriminate; injection H as <-.
      pose proof (shape_life γ γ n f (Loading Σ (body Σ (prog' (fcomp f))) [] w) eq_refl (le_n _) Hn) as Sh.
      apply (si_shape γ _ n None W S W' Sh); [discriminate|].
      apply (loadok_loading γ _ n f [] w 0 (xbody Σ (xprog (base (fcomp f))))).
      apply (kids_none γ _ n _ _ Sh).
      intros m fm j' Hm Hs; exfalso.
      destruct (si_parent γ S m fm j' _ Hm Hs) as (q & fq & Pq & Hq & Eq).
      pose proof (si_uniq γ S q n fq f Hq Hn Eq) as ->.
      destruct (wf_parent _ _ _ _ W m fm n Hm Pq) as (fq' & Hq' & I & _).
      rewrite Hn in Hq'; injection Hq' as <-; rewrite Hl in I; discriminate.
    - (* LStep *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      destruct (may_step kdec Σ prog' γ n P w); [|discriminate]; injection H as <-.
      destruct (si_load γ S n f Hn P acc w Hl) as (j & Q & -> & K).
      destruct (load_step_lift γ n f j Q acc w)
        as [(γ1 & l & E & EF & Le & Hl')|(c & Q' & Ec & E)]; rewrite E in W' |- *.
      + pose proof (shape_life γ γ1 n f l EF Le Hn) as Sh.
        apply (si_shape γ _ n None W S W' Sh); [discriminate|].
        destruct Hl' as [NL|(Q'' & acc' & ->)].
        * apply loadok_set_life; exact NL.
        * apply (loadok_loading γ1 _ n f acc' w j Q''); exact (kids_none _ _ _ _ _ Sh K).
      + pose proof (shape_new γ n f (Loading Σ (lift (fcomp f) (Datatypes.S j) Q') (USpawn Σ (next γ) :: acc) w)
                      (mkFiber Σ (child (fcomp f) (Sp j) c) (Some n) false (Inactive Σ None)) Hn (Hne n f Hn)) as Sh.
        apply (si_shape γ _ n _ W S W' Sh).
        * intros nf [= <-]; unfold NewOK; cbn [Calculus.comp Calculus.parent Calculus.life Scoped.child scope].
          split; [|split; [|split]].
          -- intros g [<-|I]; cbn [Calculus.next bump set_life set_fiber with_fibers].
             ++ cbn; lia.
             ++ pose proof (si_bound γ S n f Hn g I); lia.
          -- intros m fm Hm E0; specialize (K m fm j Hm E0); lia.
          -- intros j0 s0 Es; injection Es as <- <-; split; [reflexivity|]; exists f; auto.
          -- split; [discriminate|]; split; [discriminate|].
             right; split; [reflexivity|]; exists f; split; [exact Hn | reflexivity].
        * apply (loadok_loading _ _ n f _ w (Datatypes.S j) Q').
          exact (kids_spawn _ _ _ _ _ _ Sh eq_refl K).
    - (* LDivert *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [|P acc w| |]; try discriminate.
      destruct (target_is kdec Σ prog' γ n w); [discriminate|]; injection H as <-.
      apply (si_shape γ _ n None W S W' (shape_life γ γ n f _ eq_refl (le_n _) Hn)); [discriminate|].
      apply loadok_set_life; discriminate.
    - (* LLeave *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| |acc w|]; try discriminate.
      destruct (target_is kdec Σ prog' γ n w); [discriminate|]; injection H as <-.
      apply (si_shape γ _ n None W S W' (shape_life γ γ n f _ eq_refl (le_n _) Hn)); [discriminate|].
      apply loadok_set_life; discriminate.
    - (* LUndo *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z]; try discriminate.
      destruct (held Σ γ n (u :: acc)); [discriminate|].
      destruct (undo_next γ γ' n f u acc w z H) as (γ1 & -> & EF & En).
      apply (si_shape γ _ n None W S W' (shape_life γ γ1 n f _ EF (Nat.eq_le_incl _ _ (eq_sym En)) Hn));
        [discriminate|].
      apply loadok_set_life; discriminate.
    - (* LRetireChild *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|[k p t g|k p|m] acc] w z]; try discriminate.
      destruct (fibers γ m) as [g|] eqn:Hm; [|discriminate].
      destruct (held Σ γ n (USpawn Σ m :: acc) || Calculus.disposed Σ g); [discriminate|].
      injection H as <-; exact (si_refiber γ m g true W S Hm W').
    - (* LUnloaded *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z]; try discriminate; injection H as <-.
      apply (si_shape γ _ n None W S W' (shape_life γ γ n f _ eq_refl (le_n _) Hn)); [discriminate|].
      apply loadok_set_life; discriminate.
    - (* LRemove *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f); try discriminate.
      destruct (Calculus.disposed Σ f && negb (has_child Σ γ n)); [|discriminate]; injection H as <-.
      apply (si_shape γ _ n None W S W' (shape_remove γ n)); [discriminate|].
      intros fn' E; cbn in E; unfold fupd in E; rewrite Nat.eqb_refl in E; discriminate.
    - (* OReact *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct G as (f0 & Hn0 & Et); injection Hn0 as <-.
      destruct (life f) as [| |acc w|]; try discriminate.
      destruct (nth_error (reacts Σ (prog' (fcomp f))) i) as [y|] eqn:Hy; [|discriminate].
      destruct (Calculus.disposed Σ f || conflict γ y); [discriminate|]; injection H as <-.
      cbn [Scoped.prog' reacts] in Hy; rewrite nth_handlers in Hy.
      destruct (nth_error (xreacts Σ (xprog (base (fcomp f)))) i) as [c|]; [|discriminate].
      cbn in Hy; injection Hy as <-.
      pose proof (shape_new γ n f (Active Σ (USpawn Σ (next γ) :: acc) w)
                      (mkFiber Σ (child (fcomp f) (Re (0 + i) (tick (fcomp f))) c) (Some n) false (Inactive Σ None))
                      Hn (Hne n f Hn)) as Sh.
      apply (si_shape γ _ n _ W S W' Sh).
      + intros nf [= <-]; unfold NewOK; cbn [Calculus.comp Calculus.parent Calculus.life Scoped.child scope].
        rewrite Et; split; [|split; [|split]].
        * intros g [<-|I]; cbn [Calculus.next bump set_life set_fiber with_fibers].
          -- cbn; lia.
          -- pose proof (si_bound γ S n f Hn g I); lia.
        * intros m fm Hm E; apply (NotNew _ (si_bound γ S m fm Hm) (0 + i)).
          rewrite E; left; reflexivity.
        * discriminate.
        * split; [discriminate|]; split; [discriminate|].
          right; split; [reflexivity|]; exists f; split; [exact Hn | reflexivity].
      + apply loadok_set_life; discriminate.
    - (* ORestart *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (Calculus.disposed Σ f); [discriminate|].
      destruct (life f) as [|P acc w|acc w|]; try discriminate; injection H as <-;
        (apply (si_shape γ _ n None W S W' (shape_life γ γ n f _ eq_refl (le_n _) Hn)); [discriminate|];
         apply loadok_set_life; discriminate).
  Qed.

  (** ** Preservation by extended steps *)

  (** Replacing the component of a fiber that is not Loading by one of the
      same scope. *)
  Lemma inherit_sel (x1 x2 : XC) c : sel x1 = sel x2 -> inherit x1 c = inherit x2 c.
  Proof. intros E; unfold Scoped.inherit; rewrite E; reflexivity. Qed.

  (** Replacing the component of a fiber that is not Loading by one with
      the same base and scope, keeping its selection unless it is an
      Inactive root (which has no child and inherits nothing). *)
  Lemma si_recomp_gen (γ : State) n f x' :
    WF γ -> SI γ -> fibers γ n = Some f -> base x' = base (fcomp f) -> scope x' = scope (fcomp f) ->
    (forall P acc w, life f <> Loading Σ P acc w) ->
    (sel x' = sel (fcomp f) \/ (fparent f = None /\ is_installed Σ (life f) = false)) ->
    SI (set_fiber Σ γ n (mkFiber Σ x' (fparent f) (Calculus.disposed Σ f) (life f))).
  Proof.
    intros W S Hn Eb Es NL Hsel.
    set (f' := mkFiber Σ x' (fparent f) (Calculus.disposed Σ f) (life f)).
    assert (Hback : forall m fm, fibers (set_fiber Σ γ n f') m = Some fm ->
              exists fm0, fibers γ m = Some fm0 /\ scope (fcomp fm) = scope (fcomp fm0) /\
                fparent fm = fparent fm0 /\ life fm = life fm0 /\ (m <> n -> fm = fm0)).
    { intros m fm H; apply (fibers_set_fiber_inv Σ) in H as [[-> ->]|[Hm H]].
      - exists f; repeat split; auto. intros E; exfalso; apply E; reflexivity.
      - exists fm; repeat split; auto. }
    assert (Hfwd : forall m fm0, fibers γ m = Some fm0 ->
              exists fm, fibers (set_fiber Σ γ n f') m = Some fm /\ scope (fcomp fm) = scope (fcomp fm0)).
    { intros m fm0 H0; cbn; unfold fupd; destruct (Nat.eqb_spec m n) as [->|].
      - exists f'; split; [reflexivity|]; rewrite Hn in H0; injection H0 as <-; exact Es.
      - exists fm0; auto. }
    split; cbn [Calculus.next set_fiber with_fibers].
    - intros m m' fm fm' Hm Hm' E.
      destruct (Hback m fm Hm) as (fm0 & H0 & E0 & _).
      destruct (Hback m' fm' Hm') as (fm0' & H0' & E0' & _).
      apply (si_uniq γ S m m' fm0 fm0' H0 H0'); congruence.
    - intros m fm Hm; destruct (Hback m fm Hm) as (fm0 & H0 & E0 & _); rewrite E0.
      exact (si_bound γ S m fm0 H0).
    - intros m fm j s Hm Hs; destruct (Hback m fm Hm) as (fm0 & H0 & E0 & Ep & _).
      rewrite E0 in Hs; destruct (si_parent γ S m fm0 j s H0 Hs) as (q & fq & Pq & Hq & Eq).
      destruct (Hfwd q fq Hq) as (fq' & Hq' & Eq').
      exists q, fq'; split; [congruence|]; split; [exact Hq'|]; congruence.
    - intros m fm Hm; destruct (Hback m fm Hm) as (fm0 & H0 & E0 & _ & El & Eq).
      destruct (Nat.eq_dec m n) as [->|Hmn].
      + rewrite Hn in H0; injection H0 as <-; apply not_loading_ok; rewrite El; exact NL.
      + rewrite (Eq Hmn); intros P acc w L.
        destruct (si_load γ S m fm0 H0 P acc w L) as (j & Q & EP & K).
        exists j, Q; split; [exact EP|].
        intros m' fm' j' Hm' Hs; destruct (Hback m' fm' Hm') as (fm1 & H1 & E1 & _).
        rewrite E1 in Hs; exact (K m' fm1 j' H1 Hs).
    - intros m fm Hm; destruct (Hback m fm Hm) as (fm0 & H0 & E0 & _); rewrite E0.
      exact (si_ne γ S m fm0 H0).
    - intros m fm q fq Hm Hp Hq.
      apply (fibers_set_fiber_inv Σ) in Hm as [[-> ->]|[Hmn Hm]];
        apply (fibers_set_fiber_inv Σ) in Hq as [[-> ->]|[Hqn Hq]]; unfold f' in *; cbn [Calculus.comp Calculus.parent] in *.
      + destruct (wf_parent _ _ _ _ W n f n Hn Hp) as (fq0 & Hq0 & Iq & _).
        rewrite Hn in Hq0; injection Hq0 as <-.
        destruct Hsel as [Hs|[Hp' _]]; [|congruence].
        rewrite Hs, Eb, (inherit_sel x' (fcomp f) _ Hs); exact (si_child γ S n f n f Hn Hp Hn).
      + destruct Hsel as [Hs|[Hp' _]]; [|congruence].
        rewrite Hs, Eb; exact (si_child γ S n f q fq Hn Hp Hq).
      + destruct Hsel as [Hs|[_ Hi]].
        * rewrite (inherit_sel x' (fcomp f) _ Hs); exact (si_child γ S m fm n f Hm Hp Hn).
        * destruct (wf_parent _ _ _ _ W m fm n Hm Hp) as (fq0 & Hq0 & Iq & _).
          rewrite Hn in Hq0; injection Hq0 as <-; congruence.
      + exact (si_child γ S m fm q fq Hm Hp Hq).
  Qed.

  Lemma taken_free (γ : State) i :
    WF γ -> taken Σ γ i = false ->
    forall m f, fibers γ m = Some f -> scope (fcomp f) <> [Rt i].
  Proof.
    intros W Ht m f Hm E; unfold Scoped.taken in Ht.
    apply Bool.not_true_iff_false in Ht; apply Ht, existsb_exists.
    exists m; split; [exact (in_names kdec Σ prog' γ m f W Hm)|].
    rewrite Hm; unfold scope_eqb; destruct (scope_eq_dec _ _); [reflexivity | contradiction].
  Qed.

  Theorem si_kstep (γ γ' : State) ℓ : WF γ -> SI γ -> kstep γ ℓ = Some γ' -> SI γ'.
  Proof.
    intros W S H.
    pose proof (kpreservation N_eq_dec Σ xprog γ γ' ℓ W H) as W'.
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [Scoped.kstep klab] in H;
      try (refine (si_step γ γ' _ W S _ H); exact I).
    - destruct (taken Σ γ (xinst Σ (xprog c))) eqn:Ht; [discriminate|].
      refine (si_step γ γ' _ W S _ H); split; [eexists; reflexivity|].
      exact (taken_free γ _ W Ht).
    - (* X-Begin *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (fparent f) as [q|] eqn:Hp.
      { destruct (fresh N_eq_dec Σ xprog γ f); [refine (si_step γ γ' _ W S _ H); exact I|discriminate]. }
      destruct (all_selected N_eq_dec Σ xprog γ (base (fcomp f))); [|discriminate].
      apply (si_step (recomp N_eq_dec Σ xprog γ n f) γ' (LBegin n)); [| |exact I|exact H].
      + apply wf_recomp; auto; rewrite Hl; reflexivity.
      + apply si_recomp_gen; [exact W | exact S | exact Hn | reflexivity | reflexivity | rewrite Hl; discriminate | right; rewrite Hl; auto].
    - destruct (fibers γ n) as [f|]; [|discriminate].
      destruct (fresh N_eq_dec Σ xprog γ f); [refine (si_step γ γ' _ W S _ H); exact I|discriminate].
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (fresh N_eq_dec Σ xprog γ f); [refine (si_step γ γ' _ W S _ H); exact I|].
      destruct (life f) as [|P acc w| |]; try discriminate; injection H as <-.
      apply (si_shape γ _ n None W S W' (shape_life γ γ n f _ eq_refl (le_n _) Hn)); [discriminate|].
      apply loadok_set_life; discriminate.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (fresh N_eq_dec Σ xprog γ f); [refine (si_step γ γ' _ W S _ H); exact I|].
      destruct (life f) as [| |acc w|]; try discriminate; injection H as <-.
      apply (si_shape γ _ n None W S W' (shape_life γ γ n f _ eq_refl (le_n _) Hn)); [discriminate|].
      apply loadok_set_life; discriminate.
    - (* X-React *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      apply (si_step (retick Σ γ n f) γ' (OReact n i)); [| | |exact H].
      + apply wf_retick; auto.
      + apply si_recomp_gen; [exact W | exact S | exact Hn | reflexivity | reflexivity | rewrite Hl; discriminate | left; reflexivity].
      + eexists; split; [cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity | reflexivity].
  Qed.

  Theorem si_reachable (γ : State) : KReachable γ -> SI γ.
  Proof.
    intros [ls H].
    assert (G : forall γ0, WF γ0 -> SI γ0 -> krun N_eq_dec Σ xprog γ0 ls = Some γ -> SI γ).
    { clear H; induction ls as [|ℓ ls IH]; cbn; intros γ0 W0 S0 H0.
      - injection H0 as <-; exact S0.
      - destruct (kstep γ0 ℓ) as [γ1|] eqn:Hs; [|discriminate].
        exact (IH γ1 (kpreservation N_eq_dec Σ xprog γ0 γ1 ℓ W0 Hs) (si_kstep γ0 γ1 ℓ W0 S0 Hs) H0). }
    exact (G _ (wf_init kdec Σ prog') si_init H).
  Qed.

  (** ** Consequences: the core's conflict checks never fire *)

  (** Insertion is always enabled. *)
  Theorem insert_enabled (γ : State) c :
    KReachable γ -> taken Σ γ (xinst Σ (xprog c)) = false ->
    exists γ', kstep γ (OInsert c) = Some γ'.
  Proof.
    intros R Ht; pose proof (kwf_reachable N_eq_dec Σ xprog γ R) as W.
    cbn [Scoped.kstep]; rewrite Ht; cbn [klab Calculus.step].
    rewrite (conflict_scope N_eq_dec Σ xprog); [eauto|].
    intros m f Hm E; exact (taken_free γ _ W Ht m f Hm E).
  Qed.

  (** The component a Loading fiber is about to spawn never conflicts. *)
  Theorem spawn_ok (γ : State) n f y P' acc w :
    KReachable γ -> fibers γ n = Some f -> life f = Loading Σ (PSpawn y P') acc w ->
    conflict γ y = false.
  Proof.
    intros R Hn Hl; pose proof (si_reachable γ R) as S.
    destruct (si_load γ S n f Hn _ acc w Hl) as (j & Q & EP & K).
    destruct Q as [| | | |c Q']; cbn in EP; try discriminate; injection EP as -> _.
    apply (conflict_scope N_eq_dec Σ xprog); intros m fm Hm E; cbn in E.
    specialize (K m fm j Hm E); lia.
  Qed.

  (** A reaction is enabled whenever the fiber is Active, not disposed, and
      has the handler. *)
  Theorem react_enabled (γ : State) n f acc w i c :
    KReachable γ -> fibers γ n = Some f -> life f = Active Σ acc w ->
    Calculus.disposed Σ f = false -> nth_error (xreacts Σ (xprog (base (fcomp f)))) i = Some c ->
    exists γ', kstep γ (OReact n i) = Some γ'.
  Proof.
    intros R Hn Hl Hd Hc; pose proof (si_reachable γ R) as S.
    cbn [Scoped.kstep]; rewrite Hn, Hl.
    unfold retick; set (x' := mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f)) (sel (fcomp f)) (next γ)).
    set (γ1 := set_fiber Σ γ n (mkFiber Σ x' (fparent f) (Calculus.disposed Σ f) (life f))).
    assert (H1 : fibers γ1 n = Some (mkFiber Σ x' (fparent f) (Calculus.disposed Σ f) (life f))).
    { cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity. }
    cbn [Calculus.step]; rewrite H1; cbn [Calculus.life Calculus.comp Calculus.disposed].
    rewrite Hl, Hd; cbn [Scoped.prog' reacts]; rewrite nth_handlers; unfold x'; cbn [base tick]; rewrite Hc; cbn [option_map orb].
    rewrite (conflict_scope N_eq_dec Σ xprog); [eauto|].
    intros m fm Hm E.
    apply (fibers_set_fiber_inv Σ) in Hm as [[-> ->]|[_ Hm]].
    - cbn in E; subst x'; cbn in E.
      apply (f_equal (@length _)) in E; cbn in E; lia.
    - pose proof (si_bound γ S m fm Hm (Re (0 + i) (next γ))) as B.
      rewrite E in B; cbn in B; specialize (B (or_introl eq_refl)); lia.
  Qed.

  (** A binding at a fiber's own scope belongs to that fiber: [PProvide]
      meets a binding only when the same fiber provided the name before. *)
  Theorem provide_self (γ : State) n f y b :
    KReachable γ -> fibers γ n = Some f -> binds γ (scope (fcomp f), y) = Some b ->
    owner Σ b = n.
  Proof.
    intros R Hn Hb; pose proof (si_reachable γ R) as S.
    pose proof (kwf_reachable N_eq_dec Σ xprog γ R) as W.
    destruct (wf_bind _ _ _ _ W _ b Hb) as (fo & Ho & _ & Ko & _).
    unfold fprovs in Ko; cbn [Scoped.prog' provs] in Ko.
    apply (kmem_provs N_eq_dec Σ xprog) in Ko; cbn in Ko.
    exact (si_uniq γ S _ n fo f Ho Hn (eq_sym Ko)).
  Qed.
End ScopedSafety.
