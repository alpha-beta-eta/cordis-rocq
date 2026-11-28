(** * Hygienic keys: conservativity over the core (keys/DESIGN.md, K6)

    When every provided name is exported and no component depends on a
    private name, the extension and the core over the base table [bprog]
    make the same moves, a key [(s, x)] standing for the name [x]. The
    correspondence [R] reads a state of the extension as a state of the
    core: the same fibers with their base components, programs and undo
    items with the scope dropped from every key, and the binding of [x] is
    the one at [(s, x)], [s] the scope of its owner.

    The two calculi differ in exactly three places, each by design:
    - the core reports a conflict where the extension has none (two fibers
      providing one name, the cordis#358 family). An extended step that
      leads to such a state breaks [Disj], the runtime form of "each name
      has at most one provider";
    - the extension refuses an instance id already in use ([taken]);
    - the extension does not take an inertial step of a fiber whose
      selection is stale: one of the providers in its view is no longer
      visible ([displaced]); it reloads it instead, which the core may do
      too.

    Theorems:
    - [sim_back]: every extended step that keeps [Disj] is a core step of
      the base table, and [R] is kept; along executions, [back_run];
    - [sim_fwd]: every core step but those three is an extended step, and
      [R] is kept; along executions, [fwd_run].

    Hypotheses: no private name ([NoPriv]), no private dependency
    ([NoLocal]), and a parent declares the exported names its children
    depend on ([kSub], as in [ScopedSpawn]). The only axiom is functional
    extensionality, used to compare a program's continuations, as the
    weaker [kstep_conservative] of [Scoped.v] already does. *)

From Stdlib Require Import List PeanoNat Bool Lia FunctionalExtensionality.
From Cordis Require Import Prelude Service Calculus Preservation Progress Recovery.
From CordisKeys Require Import Scoped ScopedSafety ScopedTerm ScopedProgress.
Import ListNotations.

(** ** How a core step changes a state, for any keys *)
Section Frame.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).
  Local Notation step := (step K_eq_dec Σ prog).
  Local Notation WF := (WF K_eq_dec Σ prog).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation fparent := (Calculus.parent Σ).

  (** Fiber [n] is about to create a child of component [c]. *)
  Definition Spawner (γ : State) (n : nat) (c : C) : Prop :=
    exists fn, fibers γ n = Some fn /\
      ((exists P acc w, life fn = Loading Σ (PSpawn c P) acc w) \/
       (exists acc w i, life fn = Active Σ acc w /\ nth_error (reacts Σ (prog (fcomp fn))) i = Some c)).

  Definition FrameB (γ γ' : State) : Prop :=
    forall k b, binds γ' k = Some b ->
      (exists b0, binds γ k = Some b0 /\ pid Σ b0 = pid Σ b) \/ pid Σ b = next Σ γ.

  Definition FrameA (γ γ' : State) : Prop :=
    forall m f', fibers γ' m = Some f' -> forall k p t g, In (UOp Σ k p t g) (acc_of Σ (life f')) ->
      (exists m0 f0, fibers γ m0 = Some f0 /\ In (UOp Σ k p t g) (acc_of Σ (life f0))) \/
      (exists b, binds γ' k = Some b /\ pid Σ b = p).

  Definition FrameF (γ γ' : State) (ℓ : @Label C) : Prop :=
    forall m f', fibers γ' m = Some f' ->
      (exists f, fibers γ m = Some f /\ fcomp f' = fcomp f /\ fparent f' = fparent f /\
         (is_installed Σ (life f') = true -> is_installed Σ (life f) = true \/ ℓ = LBegin m)) \/
      (fibers γ m = None /\ life f' = Inactive Σ None /\
         ((ℓ = OInsert (fcomp f') /\ fparent f' = None) \/
          (exists n, fparent f' = Some n /\ Spawner γ n (fcomp f')))).

  Ltac dm H :=
    repeat match type of H with
    | context [match ?x with _ => _ end] => let E := fresh "E" in destruct x eqn:E
    | context [if ?x then _ else _] => let E := fresh "E" in destruct x eqn:E
    end; try discriminate H.

  Ltac fsimp := cbn [Calculus.fibers Calculus.binds Calculus.next set_life set_fiber with_fibers
                     with_binds bump log_op log_ini Calculus.life Calculus.comp Calculus.parent
                     Calculus.disposed acc_of] in *.

  (** Fibers after a step: the step's fiber [n] changed in place, others
      kept, possibly one removed or one new at [next]. *)
  Lemma fupd_inv (F : nat -> option (@Fiber K Σ C)) n o m f' :
    fupd Σ F n o m = Some f' -> (m = n /\ o = Some f') \/ (m <> n /\ F m = Some f').
  Proof. unfold fupd; destruct (Nat.eqb_spec m n) as [->|]; auto. Qed.

  Lemma bupd_inv (B : K -> option (Binding Σ)) k o k' b :
    bupd K_eq_dec Σ B k o k' = Some b -> (k' = k /\ o = Some b) \/ (k' <> k /\ B k' = Some b).
  Proof. unfold bupd, keqb; destruct (K_eq_dec k' k) as [->|]; auto. Qed.

  Ltac finv :=
    repeat match goal with
    | H : fupd _ _ _ _ _ = Some _ |- _ =>
        apply fupd_inv in H as [[? ?]|[? H]]; try subst
    | H : bupd _ _ _ _ _ _ = Some _ |- _ =>
        apply bupd_inv in H as [[? ?]|[? H]]; try subst
    | H : Some _ = Some _ |- _ => injection H as H; try subst
    | H : None = Some _ |- _ => discriminate H
    end.

  Ltac lifes := repeat match goal with H : Calculus.life _ ?f = _ |- context [Calculus.life _ ?f] => rewrite H end.

  Ltac closeB :=
    intros ?k ?b ?Hb; fsimp; finv;
    first [ left; eexists; split; [eassumption | reflexivity]
          | right; reflexivity
          | left; eexists; split; [eassumption|]; cbn; reflexivity ].

  Ltac closeA :=
    let Hin := fresh "Hin" in
    intros ?m ?f' ?Hm ?k ?p ?t ?g Hin; fsimp; finv;
    first [ cbn in Hin; contradiction
          | left; do 2 eexists; split; [eassumption|]; lifes; cbn in Hin |- *; tauto
          | left; do 2 eexists; split; [eassumption|]; exact Hin
          | idtac ].

  Ltac closeF :=
    intros ?m ?f' ?Hm; fsimp; finv;
    first [ left; eexists; split; [eassumption|]; cbn; split; [reflexivity|]; split; [reflexivity|];
            let I := fresh "I" in intros I;
            first [ left; lifes; reflexivity | right; reflexivity | cbn in I; discriminate I
                  | left; exact I | left; lifes; exact I ]
          | idtac ].

  Ltac closeAll := split; [lia|]; split; [closeB|]; split; [closeA|closeF].

  Lemma step_frame (γ γ' : State) ℓ :
    WF γ -> step γ ℓ = Some γ' ->
    next Σ γ <= next Σ γ' /\ FrameB γ γ' /\ FrameA γ γ' /\ FrameF γ γ' ℓ.
  Proof.
    intros W H.
    pose proof (fresh_none K_eq_dec Σ prog γ W) as Hfr.
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [Calculus.step] in H.
    - (* OInsert *)
      dm H; injection H as <-; fsimp; closeAll.
      right; cbn; auto.
    - dm H; injection H as <-; fsimp; closeAll.
    - dm H; injection H as <-; fsimp; closeAll.
    - dm H; injection H as <-; fsimp; closeAll.
    - (* LStep *)
      dm H; injection H as <-; unfold load_step in *.
      destruct P as [| |k a κ|k s P'|c P']; fsimp.
      + closeAll.
      + closeAll.
      + set (rp := if kmem K_eq_dec k (deps Σ (prog (fcomp f))) then lookup_view K_eq_dec k w
                   else match binds γ k with
                        | Some b => if Nat.eqb (owner Σ b) n then Some (pid Σ b) else None
                        | None => None end).
        fold rp.
        destruct rp as [p0|]; destruct (binds γ k) as [b0|] eqn:Hk; fsimp; try closeAll.
        destruct (Nat.eqb_spec (pid Σ b0) p0) as [Ep|]; fsimp; [|closeAll].
        destruct (run a (next Σ γ) (bst Σ b0)) as [[[s' g0] o]|]; fsimp; [|closeAll].
        split; [lia|]; split; [closeB|]; split; [|closeF].
        intros m f' Hm k1 p t g Hin; fsimp; finv.
        * cbn in Hin; destruct Hin as [Eu|Hin].
          -- injection Eu as <- <- <- <-; right; exists (mkBinding Σ (pid Σ b0) (owner Σ b0) s').
             cbn; unfold bupd, keqb; destruct (K_eq_dec k k); [auto|contradiction].
          -- left; exists n, f; split; [assumption|]; lifes; exact Hin.
        * left; eauto.
      + destruct (kmem K_eq_dec k (provs Σ (prog (fcomp f)))); [destruct (binds γ k) eqn:Hk|];
          fsimp; closeAll.
        cbn in Hin; destruct Hin as [Eu|Hin]; [discriminate|]; left; exists n, f; split; [assumption|]; lifes; exact Hin.
      + destruct (conflict K_eq_dec Σ prog γ c); fsimp; closeAll.
        * cbn in Hin; destruct Hin as [Eu|Hin]; [discriminate|]; left; exists n, f; split; [assumption|]; lifes; exact Hin.
        * right; cbn; split; [exact Hfr|]; split; [reflexivity|].
          right; exists n; split; [reflexivity|]; exists f; split; [assumption|].
          left; exists P', acc, w; assumption.
    - dm H; injection H as <-; fsimp; closeAll.
    - dm H; injection H as <-; fsimp; closeAll.
    - (* LUndo *)
      destruct (fibers γ n) as [f|] eqn:E; [|discriminate].
      destruct (life f) as [| | |[|u acc] w z] eqn:E0; try discriminate.
      destruct (held Σ γ n (u :: acc)); [discriminate|].
      unfold undo_step in H.
      destruct u as [k p0 t0 g0|k p0|m0].
      + destruct (binds γ k) as [b0|] eqn:Hk; [destruct (Nat.eqb_spec (pid Σ b0) p0)|];
          injection H as <-; fsimp; closeAll.
      + destruct (relied Σ γ n p0); [discriminate|].
        destruct (binds γ k) as [b0|] eqn:Hk; [destruct (Nat.eqb (pid Σ b0) p0)|];
          injection H as <-; fsimp; closeAll.
      + destruct (fibers γ m0); [discriminate|].
        injection H as <-; fsimp; closeAll.
    - dm H; injection H as <-; fsimp; closeAll.
    - dm H; injection H as <-; fsimp; closeAll.
    - dm H; injection H as <-; fsimp; closeAll.
    - (* OReact *)
      dm H; injection H as <-; fsimp; closeAll.
      + cbn in Hin; destruct Hin as [Eu|Hin]; [discriminate|]; left; exists n, f; split; [assumption|]; lifes; exact Hin.
      + right; cbn; split; [exact Hfr|]; split; [reflexivity|].
        right; exists n; split; [reflexivity|]; exists f; split; [assumption|].
        right; exists acc, w, i; auto.
    - dm H; injection H as <-; fsimp; closeAll.
  Qed.
End Frame.

(** ** An undo item for an operation names the key its pid lives at *)
Section OpKeys.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Local Notation State := (@State K Σ C).

  (** A binding whose pid an operation undo item records sits at the key
      the item names. *)
  Definition OpKey (γ : State) : Prop :=
    forall m f k p t g, fibers Σ γ m = Some f -> In (UOp Σ k p t g) (acc_of Σ (life Σ f)) ->
      forall k' b, binds Σ γ k' = Some b -> pid Σ b = p -> k' = k.

  Lemma opkey_init : OpKey (@init K Σ C).
  Proof. intros m f k p t g H; discriminate. Qed.

  Lemma opkey_frame (γ γ' : State) :
    Prov Σ prog γ -> OpKey γ -> PidUnique Σ γ' -> FrameB Σ γ γ' -> FrameA Σ γ γ' -> OpKey γ'.
  Proof.
    intros P O U' FB FA m f k p t g Hm Hin k' b Hb Ep.
    destruct (FA m f Hm k p t g Hin) as [(m0 & f0 & H0 & I0)|(b1 & Hb1 & Ep1)].
    - destruct (pv_fib Σ prog γ P m0 f0 H0) as [_ PF].
      destruct (PF k p t g I0) as (Hp & _).
      destruct (FB k' b Hb) as [(b0 & Hb0 & E0)|E].
      + exact (O m0 f0 k p t g H0 I0 k' b0 Hb0 (eq_trans E0 Ep)).
      + lia.
    - exact (U' k' k b b1 Hb Hb1 (eq_trans Ep (eq_sym Ep1))).
  Qed.

  Lemma opkey_step (γ γ' : State) ℓ :
    WF K_eq_dec Σ prog γ -> Prov Σ prog γ -> OpKey γ -> PidUnique Σ γ' ->
    step K_eq_dec Σ prog γ ℓ = Some γ' -> OpKey γ'.
  Proof.
    intros W P O U' H.
    destruct (step_frame K_eq_dec Σ prog γ γ' ℓ W H) as (_ & FB & FA & _).
    exact (opkey_frame γ γ' P O U' FB FA).
  Qed.
End OpKeys.

(** ** The correspondence *)
Section Cons.
  Context {N : Type} (N_eq_dec : forall x y : N, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (C_eq_dec : forall x y : C, {x = y} + {x <> y}).
  Context (xprog : C -> @XComponent N Σ C).

  Local Notation XC := (@XC N C).
  Local Notation Key := (@Key N).
  Local Notation KState := (@State Key Σ XC).
  Local Notation BState := (@State N Σ C).
  Local Notation KFiber := (@Fiber Key Σ XC).
  Local Notation BFiber := (@Fiber N Σ C).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation fparent := (Calculus.parent Σ).
  Local Notation disposed := (Calculus.disposed Σ).
  Local Notation next := (Calculus.next Σ).
  Local Notation kdec := (key_eq_dec N_eq_dec).
  Local Notation prog' := (prog' N_eq_dec Σ xprog).
  Local Notation kstep := (kstep N_eq_dec Σ xprog).
  Local Notation KInv := (KInv N_eq_dec Σ xprog).
  Local Notation globals := (globals Σ xprog).
  Local Notation xprovs := (xprovs Σ xprog).
  Local Notation select := (select N_eq_dec Σ xprog).
  Local Notation candidate := (candidate N_eq_dec Σ xprog).
  Local Notation fresh := (fresh N_eq_dec Σ xprog).
  Local Notation choose := (choose N_eq_dec Σ xprog).
  Local Notation assoc_or := (assoc_or N_eq_dec).
  Local Notation dkey := (dkey N_eq_dec).

  (** No private name, no private dependency; a parent declares the
      exported names its children depend on. *)
  Hypothesis NoPriv : forall c, xprivs Σ (xprog c) = [].
  Hypothesis NoLocal : forall c d, In d (xdeps Σ (xprog c)) -> exists y, d = Global y.
  Hypothesis kSub : forall c c', KSpawns Σ xprog c c' -> forall y, In y (globals c') -> In y (globals c).

  (** The base table: a component as the core sees it, names for keys. *)
  Definition bprog (c : C) : @Component N Σ C :=
    mkComponent (map dname (xdeps Σ (xprog c))) (xprovs c) (xbody Σ (xprog c)) (xreacts Σ (xprog c)).

  Local Notation bstep := (step N_eq_dec Σ bprog).
  Local Notation BWF := (WF N_eq_dec Σ bprog).
  Local Notation KWF := (WF kdec Σ prog').

  (** *** Reading a state of the extension as a state of the core *)
  Fixpoint unlift (P : @Prog Key Σ XC) : @Prog N Σ C :=
    match P with
    | PDone => PDone
    | PFail => PFail
    | POp k a κ => POp (snd k) a (fun o => unlift (κ o))
    | PProvide k s Q => PProvide (snd k) s (unlift Q)
    | PSpawn x Q => PSpawn (base x) (unlift Q)
    end.

  Definition pundo (u : @Undo Key Σ) : @Undo N Σ :=
    match u with
    | UOp _ k p t g => UOp Σ (snd k) p t g
    | UProv _ k p => UProv Σ (snd k) p
    | USpawn _ m => USpawn Σ m
    end.

  Definition pview (w : list (Key * nat)) : list (N * nat) := map (fun kp => (snd (fst kp), snd kp)) w.

  Definition plife (l : @Life Key Σ XC) : @Life N Σ C :=
    match l with
    | Inactive _ z => Inactive Σ z
    | Loading _ P acc w => Loading Σ (unlift P) (map pundo acc) (pview w)
    | Active _ acc w => Active Σ (map pundo acc) (pview w)
    | Unloading _ acc w z => Unloading Σ (map pundo acc) (pview w) z
    end.

  Definition pfib (f : KFiber) : BFiber :=
    mkFiber Σ (base (fcomp f)) (fparent f) (disposed f) (plife (life f)).

  (** The binding of a name is the one at the key [(s, x)], [s] the scope
      of its owner. *)
  Record R (γk : KState) (γb : BState) : Prop := {
    r_next : next γb = next γk;
    r_fib : forall m, fibers γb m = option_map pfib (fibers γk m);
    r_bind : forall y b, binds γb y = Some b <->
               exists fo, fibers γk (owner Σ b) = Some fo /\ binds γk (scope (fcomp fo), y) = Some b;
    r_op : oplog Σ γb = oplog Σ γk;
    r_ini : inilog Σ γb = inilog Σ γk
  }.

  Lemma R_init : R (@init Key Σ XC) (@init N Σ C).
  Proof.
    split; cbn; try reflexivity.
    intros y b; split; [discriminate|intros (fo & H & _); discriminate].
  Qed.

  Lemma unlift_lift (x : XC) j (P : @Prog N Σ C) : unlift (lift N_eq_dec Σ xprog x j P) = P.
  Proof.
    revert j; induction P as [| |y a κ IH|y s Q IH|c Q IH]; intros j; cbn; try reflexivity.
    - unfold keyof; destruct (find _ _) as [d|] eqn:Ef.
      + apply find_some in Ef as [_ Ed]; unfold neqb in Ed.
        destruct (N_eq_dec (dname d) y) as [<-|]; [|discriminate].
        f_equal; [destruct d; reflexivity|].
        apply functional_extensionality; intros o; apply IH.
      + f_equal; apply functional_extensionality; intros o; apply IH.
    - f_equal; apply IH.
    - f_equal; apply IH.
  Qed.

  (** *** Runtime disjointness: present fibers provide disjoint names *)
  Definition Disj (γ : KState) : Prop :=
    forall m m' fm fm', m <> m' -> fibers γ m = Some fm -> fibers γ m' = Some fm' ->
      overlaps N_eq_dec (xprovs (base (fcomp fm))) (xprovs (base (fcomp fm'))) = false.

  Lemma Disj_R (γk : KState) (γb : BState) : R γk γb -> BWF γb -> Disj γk.
  Proof.
    intros Rr W m m' fm fm' Hne Hm Hm'.
    pose proof (r_fib _ _ Rr m) as E; pose proof (r_fib _ _ Rr m') as E'.
    rewrite Hm in E; rewrite Hm' in E'; cbn in E, E'.
    exact (wf_disjoint _ _ _ _ W m m' _ _ Hne E E').
  Qed.

  (** *** The invariant of the extension used here *)

  (** A selection of the shape [choose] and [inherit] give. *)
  Definition Shaped (x : XC) : Prop :=
    exists F : N -> Scope, sel x = map (fun y => (y, F y)) (globals (base x)).

  Definition RootShaped (γ : KState) : Prop :=
    forall m f, fibers γ m = Some f -> fparent f = None -> is_installed Σ (life f) = true -> Shaped (fcomp f).

  (** A root's scope is its instance id; a child's scope is longer. *)
  Definition RootScope (γ : KState) : Prop :=
    forall m f, fibers γ m = Some f ->
      (fparent f = None -> scope (fcomp f) = [Rt (xinst Σ (xprog (base (fcomp f))))]) /\
      (fparent f <> None -> exists g g' s, scope (fcomp f) = g :: g' :: s).

  Record KI (γ : KState) : Prop := {
    ki_kinv : KInv γ;
    ki_opkey : OpKey Σ γ;
    ki_shaped : RootShaped γ;
    ki_roots : RootScope γ
  }.

  Lemma ki_init : KI (@init Key Σ XC).
  Proof.
    split; [exact (kinv_init N_eq_dec Σ xprog) | exact (opkey_init Σ) | |]; intros m f H; discriminate.
  Qed.

  (** The states [kstep] hands to the core: the state itself, or one with
      a root's selection chosen, or one with a fiber stamped. *)
  Definition Pre (γ γ0 : KState) : Prop :=
    γ0 = γ \/
    (exists n f, fibers γ n = Some f /\ life f = Inactive Σ None /\ fparent f = None /\
                 γ0 = recomp N_eq_dec Σ xprog γ n f) \/
    (exists n f acc w, fibers γ n = Some f /\ life f = Active Σ acc w /\ γ0 = retick Σ γ n f).

  Lemma pre_fibers (γ γ0 : KState) : Pre γ γ0 ->
    binds γ0 = binds γ /\ next γ0 = next γ /\
    (forall m, fibers γ0 m = None <-> fibers γ m = None) /\
    forall m f0, fibers γ0 m = Some f0 -> exists f, fibers γ m = Some f /\ life f0 = life f /\
       fparent f0 = fparent f /\ disposed f0 = disposed f /\ base (fcomp f0) = base (fcomp f) /\
       scope (fcomp f0) = scope (fcomp f) /\
       (sel (fcomp f0) = sel (fcomp f) \/ is_installed Σ (life f) = false).
  Proof.
    intros [->|[(n & f & Hn & Hl & Hp & ->)|(n & f & acc & w & Hn & Hl & ->)]].
    - split; [reflexivity|]; split; [reflexivity|]; split; [tauto|].
      intros m f0 H; exists f0; repeat split; auto.
    - unfold Scoped.recomp, set_fiber, with_fibers; cbn.
      split; [reflexivity|]; split; [reflexivity|]; split.
      + intros m; unfold fupd; destruct (Nat.eqb_spec m n) as [->|]; [rewrite Hn; split; discriminate | tauto].
      + intros m f0 H; unfold fupd in H; destruct (Nat.eqb_spec m n) as [->|].
        * injection H as <-; exists f; cbn; repeat split; auto; right; rewrite Hl; reflexivity.
        * exists f0; repeat split; auto.
    - unfold Scoped.retick, set_fiber, with_fibers; cbn.
      split; [reflexivity|]; split; [reflexivity|]; split.
      + intros m; unfold fupd; destruct (Nat.eqb_spec m n) as [->|]; [rewrite Hn; split; discriminate | tauto].
      + intros m f0 H; unfold fupd in H; destruct (Nat.eqb_spec m n) as [->|].
        * injection H as <-; exists f; cbn; repeat split; auto.
        * exists f0; repeat split; auto.
  Qed.

  Lemma kinv_pre (γ γ0 : KState) : KInv γ -> Pre γ γ0 -> KInv γ0.
  Proof.
    intros I [->|[(n & f & Hn & Hl & Hp & ->)|(n & f & acc & w & Hn & Hl & ->)]].
    - exact I.
    - exact (kinv_recomp N_eq_dec Σ xprog γ n f I Hn Hl Hp).
    - exact (kinv_retick N_eq_dec Σ xprog γ n f acc w I Hn Hl).
  Qed.

  Lemma opkey_pre (γ γ0 : KState) : OpKey Σ γ -> Pre γ γ0 -> OpKey Σ γ0.
  Proof.
    intros O P; destruct (pre_fibers γ γ0 P) as (Eb & _ & _ & Hf).
    intros m f0 k p t g Hm Hin k' b Hb Ep; rewrite Eb in Hb.
    destruct (Hf m f0 Hm) as (f & H & El & _).
    rewrite El in Hin; exact (O m f k p t g H Hin k' b Hb Ep).
  Qed.

  Lemma shaped_pre (γ γ0 : KState) : RootShaped γ -> Pre γ γ0 -> RootShaped γ0.
  Proof.
    intros Sh P m f0 Hm Hp Hi; destruct (pre_fibers γ γ0 P) as (_ & _ & _ & Hf).
    destruct (Hf m f0 Hm) as (f & H & El & Ep & _ & Eb & _ & [Es|Ei]).
    - rewrite El in Hi; rewrite Ep in Hp.
      destruct (Sh m f H Hp Hi) as [F EF].
      exists F; rewrite Es, Eb; exact EF.
    - rewrite El in Hi; congruence.
  Qed.

  Lemma roots_pre (γ γ0 : KState) : RootScope γ -> Pre γ γ0 -> RootScope γ0.
  Proof.
    intros Ro P m f0 Hm; destruct (pre_fibers γ γ0 P) as (_ & _ & _ & Hf).
    destruct (Hf m f0 Hm) as (f & H & _ & Ep & _ & Eb & Es & _).
    rewrite Ep, Eb, Es; exact (Ro m f H).
  Qed.

  Lemma choose_shaped (γ : KState) x :
    sel x = choose γ (base x) -> Shaped x.
  Proof.
    intros E; exists (fun y => match select γ y with Some s => s | None => [] end); exact E.
  Qed.

  (** Every extended step is a core step from a [Pre] state; an inserted
      root has its instance id for scope, and a root that begins has the
      selection it just chose. *)
  Lemma kstep_cases (γ γ' : KState) ℓ : KWF γ -> kstep γ ℓ = Some γ' ->
    exists γ0 ℓ0, Pre γ γ0 /\ step kdec Σ prog' γ0 ℓ0 = Some γ' /\
      (forall x, ℓ0 = OInsert x -> scope x = [Rt (xinst Σ (xprog (base x)))]) /\
      (forall m f, ℓ0 = LBegin m -> fibers γ0 m = Some f -> fparent f = None -> Shaped (fcomp f)).
  Proof.
    intros W H.
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [Scoped.kstep klab] in H;
      try (exists γ; eexists; split; [left; reflexivity|]; split; [exact H|];
           split; intros; discriminate).
    - destruct (taken Σ γ (xinst Σ (xprog c))); [discriminate|].
      exists γ; eexists; split; [left; reflexivity|]; split; [exact H|].
      split; [intros x E; injection E as <-; reflexivity | intros; discriminate].
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (fparent f) as [q|] eqn:Hp.
      + destruct (fresh γ f); [|discriminate].
        exists γ, (LBegin n); split; [left; reflexivity|]; split; [exact H|].
        split; [intros; discriminate|].
        intros m g E Hg Hpg; injection E as <-; rewrite Hn in Hg; injection Hg as <-; congruence.
      + destruct (all_selected N_eq_dec Σ xprog γ (base (fcomp f))); [|discriminate].
        exists (recomp N_eq_dec Σ xprog γ n f), (LBegin n).
        split; [right; left; exists n, f; auto|]; split; [exact H|].
        split; [intros; discriminate|].
        intros m g E Hg _; injection E as <-.
        unfold Scoped.recomp in Hg; cbn in Hg; unfold fupd in Hg; rewrite Nat.eqb_refl in Hg.
        injection Hg as <-; apply (choose_shaped γ); reflexivity.
    - destruct (fibers γ n) as [f|]; [|discriminate].
      destruct (fresh γ f); [|discriminate].
      exists γ, (LStep n); split; [left; reflexivity|]; split; [exact H|]; split; intros; discriminate.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (fresh γ f).
      + exists γ, (LDivert n); split; [left; reflexivity|]; split; [exact H|]; split; intros; discriminate.
      + destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
        injection H as <-; exists γ.
        destruct (disposed f) eqn:Hd.
        * exists (LDivert n); split; [left; reflexivity|]; split; [|split; intros; discriminate].
          cbn [Calculus.step]; rewrite Hn, Hl.
          unfold target_is; rewrite (target_disposed N_eq_dec Σ xprog γ n f Hn Hd); reflexivity.
        * exists (ORestart n); split; [left; reflexivity|]; split; [|split; intros; discriminate].
          cbn [Calculus.step]; rewrite Hn, Hd, Hl; reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (fresh γ f).
      + exists γ, (LLeave n); split; [left; reflexivity|]; split; [exact H|]; split; intros; discriminate.
      + destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
        injection H as <-; exists γ.
        destruct (disposed f) eqn:Hd.
        * exists (LLeave n); split; [left; reflexivity|]; split; [|split; intros; discriminate].
          cbn [Calculus.step]; rewrite Hn, Hl.
          unfold target_is; rewrite (target_disposed N_eq_dec Σ xprog γ n f Hn Hd); reflexivity.
        * exists (ORestart n); split; [left; reflexivity|]; split; [|split; intros; discriminate].
          cbn [Calculus.step]; rewrite Hn, Hd, Hl; reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      exists (retick Σ γ n f), (OReact n i); split; [right; right; exists n, f, acc, w; auto|].
      split; [exact H|]; split; intros; discriminate.
  Qed.

  Lemma shaped_step (γ0 γ' : KState) ℓ0 :
    KWF γ0 -> RootShaped γ0 -> step kdec Σ prog' γ0 ℓ0 = Some γ' ->
    (forall m f, ℓ0 = LBegin m -> fibers γ0 m = Some f -> fparent f = None -> Shaped (fcomp f)) ->
    RootShaped γ'.
  Proof.
    intros W Sh S Hb m f' Hm Hp Hi.
    destruct (step_frame kdec Σ prog' γ0 γ' ℓ0 W S) as (_ & _ & _ & FF).
    destruct (FF m f' Hm) as [(f & H & Ec & Ep & HI)|(_ & Hl & _)].
    - rewrite Ec; rewrite Ep in Hp.
      destruct (HI Hi) as [Hi0|E]; [exact (Sh m f H Hp Hi0) | exact (Hb m f E H Hp)].
    - rewrite Hl in Hi; discriminate.
  Qed.

  Lemma spawner_scope (γ0 : KState) n x :
    SI N_eq_dec Σ xprog γ0 -> Spawner Σ prog' γ0 n x -> exists g g' s, scope x = g :: g' :: s.
  Proof.
    intros S (fn & Hn & [(P & acc & w & Hl)|(acc & w & i & Hl & Hi)]).
    - destruct (si_load N_eq_dec Σ xprog γ0 S n fn Hn _ acc w Hl) as (j & Q & EP & _).
      destruct Q as [| | | |c Q']; cbn in EP; try discriminate; injection EP as -> _.
      pose proof (si_ne N_eq_dec Σ xprog γ0 S n fn Hn) as Ne.
      destruct (scope (fcomp fn)) as [|g' s] eqn:Es; [contradiction|].
      exists (Sp j), g', s; cbn; rewrite Es; reflexivity.
    - cbn [Scoped.prog' reacts] in Hi; rewrite nth_handlers in Hi.
      destruct (nth_error _ i) as [c|]; [|discriminate]; injection Hi as <-.
      pose proof (si_ne N_eq_dec Σ xprog γ0 S n fn Hn) as Ne.
      destruct (scope (fcomp fn)) as [|g' s] eqn:Es; [contradiction|].
      eexists _, g', s; cbn; rewrite Es; reflexivity.
  Qed.

  Lemma roots_step (γ0 γ' : KState) ℓ0 :
    KWF γ0 -> SI N_eq_dec Σ xprog γ0 -> RootScope γ0 -> step kdec Σ prog' γ0 ℓ0 = Some γ' ->
    (forall x, ℓ0 = OInsert x -> scope x = [Rt (xinst Σ (xprog (base x)))]) ->
    RootScope γ'.
  Proof.
    intros W S Ro St Hi m f' Hm.
    destruct (step_frame kdec Σ prog' γ0 γ' ℓ0 W St) as (_ & _ & _ & FF).
    destruct (FF m f' Hm) as [(f & H & Ec & Ep & _)|(_ & _ & [(E & Hp)|(q & Hp & Sp)])].
    - rewrite Ec, Ep; exact (Ro m f H).
    - split; [intros _; exact (Hi _ E) | congruence].
    - split; [congruence|]; intros _; exact (spawner_scope γ0 q _ S Sp).
  Qed.

  Theorem ki_step (γ γ' : KState) ℓ : KI γ -> kstep γ ℓ = Some γ' -> KI γ'.
  Proof.
    intros [I O Sh Ro] H.
    pose proof (kinv_step N_eq_dec Σ C_eq_dec xprog γ γ' ℓ I H) as I'.
    destruct (kstep_cases γ γ' ℓ (ki_wf _ _ _ _ I) H) as (γ0 & ℓ0 & P & St & Hi & Hb).
    pose proof (kinv_pre γ γ0 I P) as I0.
    split; [exact I'| | |].
    - exact (opkey_step kdec Σ prog' γ0 γ' ℓ0 (ki_wf _ _ _ _ I0) (ki_prov _ _ _ _ I0)
               (opkey_pre γ γ0 O P) (ki_pid _ _ _ _ I') St).
    - exact (shaped_step γ0 γ' ℓ0 (ki_wf _ _ _ _ I0) (shaped_pre γ γ0 Sh P) St Hb).
    - exact (roots_step γ0 γ' ℓ0 (ki_wf _ _ _ _ I0) (ki_si _ _ _ _ I0) (roots_pre γ γ0 Ro P) St Hi).
  Qed.

  Theorem ki_reachable (γ : KState) : KReachable N_eq_dec Σ xprog γ -> KI γ.
  Proof.
    intros [ls H].
    assert (G : forall γ0, KI γ0 -> krun N_eq_dec Σ xprog γ0 ls = Some γ -> KI γ).
    { clear H; induction ls as [|ℓ ls IH]; cbn; intros γ0 I0 H0.
      - injection H0 as <-; exact I0.
      - destruct (kstep γ0 ℓ) as [γ1|] eqn:Hs; [|discriminate].
        exact (IH γ1 (ki_step γ0 γ1 ℓ I0 Hs) H0). }
    exact (G _ ki_init H).
  Qed.

  (** *** Bindings and visibility on the two sides *)

  Lemma kmem_pair (s s' : Scope) y (l : list N) :
    kmem kdec (s', y) (map (pair s) l) = true <-> s' = s /\ In y l.
  Proof.
    unfold kmem; rewrite existsb_exists; split.
    - intros [k [Hin E]]; apply in_map_iff in Hin as [y' [<- Hy]].
      unfold keqb in E; destruct (kdec (s', y) (s, y')) as [Q|]; [|discriminate].
      injection Q as -> ->; auto.
    - intros [-> Hy]; exists (s, y); split; [apply in_map; exact Hy|].
      unfold keqb; destruct (kdec (s, y) (s, y)); [reflexivity | contradiction].
  Qed.

  Lemma kmem_name (y : N) (l : list N) : kmem N_eq_dec y l = true <-> In y l.
  Proof.
    unfold kmem; rewrite existsb_exists; split.
    - intros [y' [Hin E]]; unfold keqb in E; destruct (N_eq_dec y y') as [->|]; [exact Hin | discriminate].
    - intros Hy; exists y; split; [exact Hy|]; unfold keqb; destruct (N_eq_dec y y); [reflexivity | contradiction].
  Qed.

  Lemma nmem_in (y : N) (l : list N) : nmem N_eq_dec y l = true <-> In y l.
  Proof.
    unfold nmem; rewrite existsb_exists; split.
    - intros [y' [Hin E]]; unfold neqb in E; destruct (N_eq_dec y y') as [->|]; [exact Hin | discriminate].
    - intros Hy; exists y; split; [exact Hy|]; unfold neqb; destruct (N_eq_dec y y); [reflexivity | contradiction].
  Qed.

  Lemma owner_scope (γk : KState) s y b :
    KWF γk -> binds γk (s, y) = Some b ->
    exists fo, fibers γk (owner Σ b) = Some fo /\ is_installed Σ (life fo) = true /\
               scope (fcomp fo) = s /\ In y (xprovs (base (fcomp fo))).
  Proof.
    intros W Hb; destruct (wf_bind _ _ _ _ W _ b Hb) as (fo & Ho & Io & Ko & _).
    unfold fprovs in Ko; cbn [Scoped.prog' provs] in Ko.
    apply kmem_pair in Ko as [Es Hy]; exists fo; auto.
  Qed.

  Lemma fib_k2b (γk : KState) (γb : BState) m f :
    R γk γb -> fibers γk m = Some f -> fibers γb m = Some (pfib f).
  Proof. intros Rr H; rewrite (r_fib _ _ Rr m), H; reflexivity. Qed.

  Lemma fib_b2k (γk : KState) (γb : BState) m fb :
    R γk γb -> fibers γb m = Some fb -> exists f, fibers γk m = Some f /\ fb = pfib f.
  Proof.
    intros Rr H; rewrite (r_fib _ _ Rr m) in H.
    destruct (fibers γk m) as [f|]; [injection H as <-; eauto | discriminate].
  Qed.

  Lemma fib_none (γk : KState) (γb : BState) m :
    R γk γb -> (fibers γb m = None <-> fibers γk m = None).
  Proof.
    intros Rr; rewrite (r_fib _ _ Rr m); destruct (fibers γk m); cbn; split; congruence.
  Qed.

  Lemma bind_k2b (γk : KState) (γb : BState) s y b :
    KWF γk -> R γk γb -> binds γk (s, y) = Some b -> binds γb y = Some b.
  Proof.
    intros W Rr Hb; destruct (owner_scope γk s y b W Hb) as (fo & Ho & _ & Es & _).
    apply (r_bind _ _ Rr); exists fo; rewrite Es; auto.
  Qed.

  Lemma bind_own (γk : KState) (γb : BState) m fm y b :
    KI γk -> R γk γb -> fibers γk m = Some fm ->
    (binds γk (scope (fcomp fm), y) = Some b <-> binds γb y = Some b /\ owner Σ b = m).
  Proof.
    intros I Rr Hm; pose proof (ki_wf _ _ _ _ (ki_kinv _ I)) as W; split.
    - intros Hb; split; [exact (bind_k2b γk γb _ y b W Rr Hb)|].
      destruct (owner_scope γk _ y b W Hb) as (fo & Ho & _ & Es & _).
      exact (si_uniq _ _ _ _ (ki_si _ _ _ _ (ki_kinv _ I)) _ _ fo fm Ho Hm Es).
    - intros [Hb Eo]; apply (r_bind _ _ Rr) in Hb as (fo & Ho & Hb).
      rewrite Eo, Hm in Ho; injection Ho as <-; exact Hb.
  Qed.

  Lemma plife_active l : is_active Σ (plife l) = is_active Σ l.
  Proof. destruct l; reflexivity. Qed.
  Lemma plife_installed l : is_installed Σ (plife l) = is_installed Σ l.
  Proof. destruct l; reflexivity. Qed.
  Lemma plife_view l : view_of Σ (plife l) = pview (view_of Σ l).
  Proof. destruct l; reflexivity. Qed.
  Lemma plife_acc l : acc_of Σ (plife l) = map pundo (acc_of Σ l).
  Proof. destruct l; reflexivity. Qed.

  Lemma vis_k2b (γk : KState) (γb : BState) k p :
    KWF γk -> R γk γb -> visible Σ γk k = Some p -> visible Σ γb (snd k) = Some p.
  Proof.
    intros W Rr; destruct k as [s y]; unfold visible; cbn [snd].
    destruct (binds γk (s, y)) as [b|] eqn:Hb; [|discriminate].
    rewrite (bind_k2b γk γb s y b W Rr Hb).
    destruct (fibers γk (owner Σ b)) as [fo|] eqn:Ho; [|discriminate].
    rewrite (fib_k2b γk γb _ fo Rr Ho); cbn [pfib Calculus.life]; rewrite plife_active; auto.
  Qed.

  Lemma vis_b2k (γk : KState) (γb : BState) y p :
    R γk γb -> visible Σ γb y = Some p ->
    exists b fo, binds γb y = Some b /\ fibers γk (owner Σ b) = Some fo /\ pid Σ b = p /\
                 is_active Σ (life fo) = true /\ binds γk (scope (fcomp fo), y) = Some b /\
                 visible Σ γk (scope (fcomp fo), y) = Some p.
  Proof.
    intros Rr; unfold visible at 1.
    destruct (binds γb y) as [b|] eqn:Hb; [|discriminate].
    destruct (fibers γb (owner Σ b)) as [fb|] eqn:Ho; [|discriminate].
    destruct (is_active Σ (life fb)) eqn:Ha; [|discriminate]; intros [= <-].
    pose proof Hb as Hb'; apply (r_bind _ _ Rr) in Hb' as (fo & Ho' & Hk).
    rewrite (fib_k2b γk γb _ fo Rr Ho') in Ho; injection Ho as <-.
    cbn [pfib Calculus.life] in Ha; rewrite plife_active in Ha.
    exists b, fo; repeat split; auto.
    unfold visible; rewrite Hk, Ho', Ha; reflexivity.
  Qed.

  (** *** Exported names: at most one candidate *)
  Fixpoint in_omap {A B : Type} (g : A -> option B) (l : list A) (c : B) {struct l} :
    In c (omap g l) -> exists a, In a l /\ g a = Some c.
  Proof.
    destruct l as [|a l]; cbn; [tauto|].
    destruct (g a) as [b|] eqn:E.
    - intros [<-|H]; [exists a; auto|].
      destruct (in_omap A B g l c H) as (a' & I & G); exists a'; auto.
    - intros H; destruct (in_omap A B g l c H) as (a' & I & G); exists a'; auto.
  Qed.

  Lemma omap_nil {A B : Type} (g : A -> option B) (l : list A) :
    (forall a, In a l -> g a = None) -> omap g l = [].
  Proof.
    induction l as [|a l IH]; cbn; intros H; [reflexivity|].
    rewrite (H a (or_introl eq_refl)); apply IH; intros a' I; apply H; right; exact I.
  Qed.

  Lemma omap_single (g : nat -> option (Scope * nat)) (l : list nat) m0 c0 :
    NoDup l -> In m0 l -> g m0 = Some c0 ->
    (forall m c, In m l -> g m = Some c -> m = m0) -> omap g l = [c0].
  Proof.
    induction l as [|a l IH]; cbn; [tauto|]; intros ND I G U.
    inversion ND as [|a' l' Na ND']; subst.
    destruct (Nat.eq_dec a m0) as [->|Hne].
    - rewrite G; f_equal; apply omap_nil; intros a' Ia.
      destruct (g a') as [c|] eqn:Ga; [|reflexivity].
      exfalso; pose proof (U a' c (or_intror Ia) Ga); subst; contradiction.
    - destruct (g a) as [c|] eqn:Ga; [exfalso; exact (Hne (U a c (or_introl eq_refl) Ga))|].
      destruct I as [E|I]; [contradiction|].
      apply IH; auto; intros m c Im Gm; exact (U m c (or_intror Im) Gm).
  Qed.

  Lemma candidate_spec (γ : KState) y m c :
    candidate γ y m = Some c ->
    exists f p, fibers γ m = Some f /\ In y (xexports Σ (xprog (base (fcomp f)))) /\
                visible Σ γ (scope (fcomp f), y) = Some p /\ c = (scope (fcomp f), xprio Σ (xprog (base (fcomp f))) y).
  Proof.
    unfold Scoped.candidate; destruct (fibers γ m) as [f|]; [|discriminate].
    destruct (nmem N_eq_dec y _) eqn:E; [|discriminate].
    destruct (visible Σ γ _) as [p|] eqn:V; [|discriminate]; intros [= <-].
    apply nmem_in in E; exists f, p; auto.
  Qed.

  Lemma candidate_of (γ : KState) y m f p :
    fibers γ m = Some f -> In y (xexports Σ (xprog (base (fcomp f)))) ->
    visible Σ γ (scope (fcomp f), y) = Some p ->
    candidate γ y m = Some (scope (fcomp f), xprio Σ (xprog (base (fcomp f))) y).
  Proof.
    intros Hm Hy V; unfold Scoped.candidate; rewrite Hm.
    apply nmem_in in Hy; rewrite Hy, V; reflexivity.
  Qed.

  Lemma select_single (γ : KState) y c :
    candidates N_eq_dec Σ xprog γ y = [c] -> select γ y = Some (fst c).
  Proof.
    destruct c as [s pr]; intros E; unfold Scoped.select; rewrite E; cbn.
    rewrite Nat.max_0_r, Nat.eqb_refl; reflexivity.
  Qed.

  Lemma select_some (γ : KState) y s :
    select γ y = Some s -> exists m pr, candidate γ y m = Some (s, pr).
  Proof.
    unfold Scoped.select.
    destruct (filter _ _) as [|[s' pr] [|]] eqn:F; try discriminate; intros [= <-].
    assert (I : In (s', pr) (filter (fun c => Nat.eqb (snd c) (fold_right (fun c m => Nat.max (snd c) m) 0
                  (candidates N_eq_dec Σ xprog γ y))) (candidates N_eq_dec Σ xprog γ y)))
      by (rewrite F; left; reflexivity).
    apply filter_In in I as [I _]; unfold Scoped.candidates in I.
    destruct (in_omap _ _ _ I) as (m & _ & G); eauto.
  Qed.

  Lemma select_none (γ : KState) y :
    (forall m, candidate γ y m = None) -> select γ y = None.
  Proof.
    intros H; unfold Scoped.select, Scoped.candidates.
    rewrite omap_nil by (intros a _; apply H); reflexivity.
  Qed.

  (** Two candidates of one name are one fiber: their bindings are both
      the core's binding of the name. *)
  Lemma candidate_unique (γk : KState) (γb : BState) y m1 m2 c1 c2 :
    KI γk -> R γk γb -> candidate γk y m1 = Some c1 -> candidate γk y m2 = Some c2 -> m1 = m2.
  Proof.
    intros I Rr H1 H2.
    destruct (candidate_spec γk y m1 c1 H1) as (f1 & p1 & Hm1 & _ & V1 & _).
    destruct (candidate_spec γk y m2 c2 H2) as (f2 & p2 & Hm2 & _ & V2 & _).
    unfold visible in V1, V2.
    destruct (binds γk (scope (fcomp f1), y)) as [b1|] eqn:B1; [|discriminate].
    destruct (binds γk (scope (fcomp f2), y)) as [b2|] eqn:B2; [|discriminate].
    apply (bind_own γk γb m1 f1 y b1 I Rr Hm1) in B1 as [C1 O1].
    apply (bind_own γk γb m2 f2 y b2 I Rr Hm2) in B2 as [C2 O2].
    rewrite C1 in C2; injection C2 as ->; congruence.
  Qed.

  Lemma select_vis (γk : KState) (γb : BState) y p :
    KI γk -> R γk γb -> visible Σ γb y = Some p ->
    exists b fo, binds γb y = Some b /\ fibers γk (owner Σ b) = Some fo /\
                 select γk y = Some (scope (fcomp fo)) /\ visible Σ γk (scope (fcomp fo), y) = Some p.
  Proof.
    intros I Rr V; pose proof (ki_wf _ _ _ _ (ki_kinv _ I)) as W.
    destruct (vis_b2k γk γb y p Rr V) as (b & fo & Hb & Ho & Ep & Ha & Hk & Vk).
    exists b, fo; split; [exact Hb|]; split; [exact Ho|]; split; [|exact Vk].
    destruct (owner_scope γk _ y b W Hk) as (fo' & Ho' & _ & _ & Hy).
    rewrite Ho in Ho'; injection Ho' as <-.
    assert (Hx : In y (xexports Σ (xprog (base (fcomp fo))))).
    { unfold Scoped.xprovs in Hy; rewrite NoPriv in Hy; exact Hy. }
    pose proof (candidate_of γk y _ fo p Ho Hx Vk) as Cd.
    change (scope (fcomp fo)) with (fst (scope (fcomp fo), xprio Σ (xprog (base (fcomp fo))) y)).
    apply select_single; unfold Scoped.candidates.
    apply (omap_single _ _ (owner Σ b)); [apply seq_NoDup | exact (in_names kdec Σ prog' γk _ fo W Ho) | exact Cd|].
    intros m c _ Gm; exact (candidate_unique γk γb y m (owner Σ b) c _ I Rr Gm Cd).
  Qed.

  Lemma select_novis (γk : KState) (γb : BState) y :
    KI γk -> R γk γb -> visible Σ γb y = None -> select γk y = None.
  Proof.
    intros I Rr V; pose proof (ki_wf _ _ _ _ (ki_kinv _ I)) as W.
    apply select_none; intros m.
    destruct (candidate γk y m) as [c|] eqn:Cd; [|reflexivity].
    destruct (candidate_spec γk y m c Cd) as (f & p & _ & _ & Vk & _).
    pose proof (vis_k2b γk γb _ p W Rr Vk) as Vb; cbn in Vb; congruence.
  Qed.

  (** *** Selections, views and targets *)

  Lemma in_omap_intro {A B : Type} (g : A -> option B) (l : list A) a c :
    In a l -> g a = Some c -> In c (omap g l).
  Proof.
    induction l as [|a' l IH]; cbn; [tauto|]; intros [->|I] G.
    - rewrite G; left; reflexivity.
    - destruct (g a'); [right|]; auto.
  Qed.

  Lemma globals_in c y : In y (globals c) <-> In (Global y) (xdeps Σ (xprog c)).
  Proof.
    unfold Scoped.globals; split.
    - intros I; destruct (in_omap _ _ _ I) as ([z|z] & Iz & G); [discriminate|]; injection G as ->; exact Iz.
    - intros I; exact (in_omap_intro _ _ (Global y) y I eq_refl).
  Qed.

  Lemma dkey_dep (x : XC) d : In d (xdeps Σ (xprog (base x))) -> dkey x d = (assoc_or (dname d) (sel x), dname d).
  Proof. intros I; destruct (NoLocal _ d I) as [y ->]; reflexivity. Qed.

  Lemma snd_dkey (x : XC) d : snd (dkey x d) = dname d.
  Proof. destruct d; reflexivity. Qed.

  Lemma deps_keys (x : XC) :
    map snd (deps Σ (prog' x)) = deps Σ (bprog (base x)).
  Proof.
    cbn [Scoped.prog' bprog deps]; rewrite map_map; apply map_ext; intros d; apply snd_dkey.
  Qed.

  (** An installed fiber's view has an entry for each exported name it
      depends on, at the key its selection gives. *)
  Lemma view_has (γk : KState) n f y :
    KWF γk -> fibers γk n = Some f -> is_installed Σ (life f) = true ->
    In y (globals (base (fcomp f))) ->
    exists p, In ((assoc_or y (sel (fcomp f)), y), p) (view_of Σ (life f)).
  Proof.
    intros W Hn Hi Hy.
    pose proof (wf_view_keys _ _ _ _ W n f Hn Hi) as Ek.
    unfold fdeps in Ek; cbn [Scoped.prog' deps] in Ek.
    apply globals_in in Hy.
    assert (Ik : In (dkey (fcomp f) (Global y)) (map fst (view_of Σ (life f))))
      by (rewrite Ek; apply in_map; exact Hy).
    apply in_map_iff in Ik as ([k p] & Ef & Ik); cbn in Ef; subst k.
    exists p; exact Ik.
  Qed.

  Lemma view_entry (γk : KState) n f s y p :
    KWF γk -> fibers γk n = Some f -> In ((s, y), p) (view_of Σ (life f)) ->
    In y (globals (base (fcomp f))) /\ s = assoc_or y (sel (fcomp f)).
  Proof.
    intros W Hn I.
    assert (Hi : is_installed Σ (life f) = true) by (destruct (life f); cbn in I; tauto || reflexivity).
    pose proof (wf_view_keys _ _ _ _ W n f Hn Hi) as Ek.
    unfold fdeps in Ek; cbn [Scoped.prog' deps] in Ek.
    assert (Ik : In (s, y) (map fst (view_of Σ (life f)))) by (apply (in_map fst) in I; exact I).
    rewrite Ek in Ik; apply in_map_iff in Ik as (d & Ed & Id).
    rewrite (dkey_dep _ d Id) in Ed; injection Ed as Es Ey.
    destruct (NoLocal _ d Id) as [z ->]; cbn in Es, Ey; subst z.
    split; [apply globals_in; exact Id | symmetry; exact Es].
  Qed.

  Lemma shaped_installed (γk : KState) m f :
    KI γk -> fibers γk m = Some f -> is_installed Σ (life f) = true -> Shaped (fcomp f).
  Proof.
    intros I Hm Hi.
    destruct (fparent f) as [q|] eqn:Hp; [|exact (ki_shaped _ I m f Hm Hp Hi)].
    pose proof (ki_wf _ _ _ _ (ki_kinv _ I)) as W.
    destruct (wf_parent _ _ _ _ W m f q Hm Hp) as (fq & Hq & _).
    unfold Shaped; rewrite (si_child _ _ _ _ (ki_si _ _ _ _ (ki_kinv _ I)) m f q fq Hm Hp Hq).
    exists (fun y => assoc_or y (sel (fcomp fq))); reflexivity.
  Qed.

  Lemma shaped_assoc (x : XC) :
    Shaped x -> sel x = map (fun y => (y, assoc_or y (sel x))) (globals (base x)).
  Proof.
    intros [F EF]; rewrite EF at 1; apply map_ext_in; intros y Hy.
    unfold Scoped.assoc_or; rewrite EF, (assoc_map N_eq_dec F _ y Hy); reflexivity.
  Qed.

  (** A view entry whose provider is no longer visible. *)
  Definition displacedb (γb : BState) (w : list (N * nat)) : bool :=
    existsb (fun yp => match visible Σ γb (fst yp) with Some _ => false | None => true end) w.

  Lemma pview_in (w : list (Key * nat)) y p :
    In (y, p) (pview w) -> exists s, In ((s, y), p) w.
  Proof.
    unfold pview; intros I; apply in_map_iff in I as ([[s y'] p'] & E & I); cbn in E.
    injection E as -> ->; eauto.
  Qed.

  Lemma in_pview (w : list (Key * nat)) s y p : In ((s, y), p) w -> In (y, p) (pview w).
  Proof. intros I; exact (in_map (fun kp => (snd (fst kp), snd kp)) w _ I). Qed.

  (** An installed fiber's selection is current exactly when every
      provider in its view is still visible. *)
  Lemma fresh_iff (γk : KState) (γb : BState) n f :
    KI γk -> R γk γb -> fibers γk n = Some f -> is_installed Σ (life f) = true ->
    fresh γk f = negb (displacedb γb (pview (view_of Σ (life f)))).
  Proof.
    intros I Rr Hn Hi; pose proof (ki_wf _ _ _ _ (ki_kinv _ I)) as W.
    destruct (displacedb γb _) eqn:D; cbn [negb].
    - unfold displacedb in D; apply existsb_exists in D as ([y p] & Ip & Ev); cbn in Ev.
      destruct (visible Σ γb y) eqn:V; [discriminate|].
      destruct (pview_in _ y p Ip) as (s & Is).
      destruct (view_entry γk n f s y p W Hn Is) as [Hy _].
      unfold Scoped.fresh; apply andb_false_iff; left.
      unfold Scoped.all_selected; apply not_true_iff_false; intros A.
      rewrite forallb_forall in A; specialize (A y Hy).
      unfold Scoped.selected in A; rewrite (select_novis γk γb y I Rr V) in A; discriminate.
    - assert (Sel : forall y, In y (globals (base (fcomp f))) -> select γk y = Some (assoc_or y (sel (fcomp f)))).
      { intros y Hy.
        destruct (view_has γk n f y W Hn Hi Hy) as (p & Ip).
        destruct (visible Σ γb y) as [p'|] eqn:V.
        2:{ exfalso; apply not_true_iff_false in D; apply D, existsb_exists.
            exists (y, p); split; [exact (in_pview _ _ _ _ Ip)|]; cbn; rewrite V; reflexivity. }
        destruct (select_vis γk γb y p' I Rr V) as (b & fo & Hb & Ho & Es & _).
        destruct (wf_view _ _ _ _ W n f _ p Hn Ip) as (b0 & Hb0 & _ & _).
        rewrite (bind_k2b γk γb _ y b0 W Rr Hb0) in Hb; injection Hb as <-.
        destruct (owner_scope γk _ y b0 W Hb0) as (fo' & Ho' & _ & Es' & _).
        rewrite Ho in Ho'; injection Ho' as <-; rewrite Es, Es'; reflexivity. }
      unfold Scoped.fresh; apply andb_true_iff; split.
      + unfold Scoped.all_selected; apply forallb_forall; intros y Hy.
        unfold Scoped.selected; rewrite (Sel y Hy); reflexivity.
      + assert (E : sel (fcomp f) = choose γk (base (fcomp f))).
        { rewrite (shaped_assoc _ (shaped_installed γk n f I Hn Hi)) at 1.
          unfold Scoped.choose; apply map_ext_in; intros y Hy; rewrite (Sel y Hy); reflexivity. }
        destruct (list_eq_dec _ _ _) as [_|Q]; [reflexivity | contradiction].
  Qed.

  Lemma resolve_keys (γ : KState) ks t : resolve Σ γ ks = Some t -> map fst t = ks.
  Proof.
    revert t; induction ks as [|k ks IH]; cbn; intros t H; [injection H as <-; reflexivity|].
    destruct (visible Σ γ k), (resolve Σ γ ks) as [t'|] eqn:E; try discriminate.
    injection H as <-; cbn; f_equal; apply IH; reflexivity.
  Qed.

  Lemma resolve_k2b (γk : KState) (γb : BState) ks t :
    KWF γk -> R γk γb -> resolve Σ γk ks = Some t -> resolve Σ γb (map snd ks) = Some (pview t).
  Proof.
    intros W Rr; revert t; induction ks as [|k ks IH]; cbn; intros t H; [injection H as <-; reflexivity|].
    destruct (visible Σ γk k) as [p|] eqn:V; [|discriminate].
    destruct (resolve Σ γk ks) as [t'|] eqn:E; [|discriminate]; injection H as <-.
    rewrite (vis_k2b γk γb k p W Rr V), (IH t' eq_refl); reflexivity.
  Qed.

  Lemma resolve_b2k (γk : KState) (γb : BState) ks tb :
    (forall k p, In k ks -> visible Σ γb (snd k) = Some p -> visible Σ γk k = Some p) ->
    resolve Σ γb (map snd ks) = Some tb -> exists t, resolve Σ γk ks = Some t /\ pview t = tb.
  Proof.
    revert tb; induction ks as [|k ks IH]; cbn; intros tb Hv H; [injection H as <-; exists []; auto|].
    destruct (visible Σ γb (snd k)) as [p|] eqn:V; [|discriminate].
    destruct (resolve Σ γb (map snd ks)) as [tb'|] eqn:E; [|discriminate]; injection H as <-.
    destruct (IH tb' (fun k' p' I => Hv k' p' (or_intror I)) eq_refl) as (t & Ht & Et).
    rewrite (Hv k p (or_introl eq_refl) V), Ht; exists ((k, p) :: t); split; [reflexivity|].
    change (pview ((k, p) :: t)) with ((snd k, p) :: pview t); rewrite Et; reflexivity.
  Qed.

  Lemma resolve_all (γb : BState) ys tb :
    resolve Σ γb ys = Some tb -> forall y, In y ys -> exists p, visible Σ γb y = Some p.
  Proof.
    revert tb; induction ys as [|y' ys IH]; cbn; intros tb H y I; [contradiction|].
    destruct (visible Σ γb y') as [p|] eqn:V; [|discriminate].
    destruct (resolve Σ γb ys) as [tb'|] eqn:E; [|discriminate].
    destruct I as [<-|I]; [eauto | exact (IH tb' eq_refl y I)].
  Qed.

  Lemma target_k2b (γk : KState) (γb : BState) n f t :
    KWF γk -> R γk γb -> fibers γk n = Some f -> target Σ prog' γk n = Some t ->
    target Σ bprog γb n = Some (pview t).
  Proof.
    intros W Rr Hn; unfold target; rewrite Hn, (fib_k2b γk γb n f Rr Hn); cbn [pfib Calculus.disposed Calculus.comp].
    destruct (disposed f); [discriminate|]; intros H.
    rewrite <- deps_keys; exact (resolve_k2b γk γb _ t W Rr H).
  Qed.

  (** Under a current selection the two targets agree. *)
  Lemma target_fresh (γk : KState) (γb : BState) n f :
    KI γk -> R γk γb -> fibers γk n = Some f -> fresh γk f = true ->
    target Σ bprog γb n = option_map pview (target Σ prog' γk n).
  Proof.
    intros I Rr Hn Fr; pose proof (ki_wf _ _ _ _ (ki_kinv _ I)) as W.
    destruct (target Σ prog' γk n) as [t|] eqn:Ht; [exact (target_k2b γk γb n f t W Rr Hn Ht)|].
    unfold target in Ht |- *; rewrite Hn in Ht; rewrite (fib_k2b γk γb n f Rr Hn); cbn [pfib Calculus.disposed Calculus.comp].
    destruct (disposed f); [reflexivity|].
    destruct (resolve Σ γb (deps Σ (bprog (base (fcomp f))))) as [tb|] eqn:Hb; [|reflexivity].
    exfalso; rewrite <- deps_keys in Hb.
    unfold Scoped.fresh in Fr; apply andb_true_iff in Fr as [A Ec].
    destruct (list_eq_dec (ns_eq_dec N_eq_dec) (sel (fcomp f)) (choose γk (base (fcomp f)))) as [Es|]; [|discriminate].
    destruct (resolve_b2k γk γb (deps Σ (prog' (fcomp f))) tb) as (t & Ht' & _); [|exact Hb|congruence].
    intros k p Ik V; cbn [Scoped.prog' deps] in Ik.
    apply in_map_iff in Ik as (d & <- & Id).
    rewrite snd_dkey in V; rewrite (dkey_dep _ d Id).
    destruct (NoLocal _ d Id) as [y ->]; cbn [dname] in V |- *.
    destruct (select_vis γk γb y p I Rr V) as (b & fo & _ & _ & Es' & Vk).
    unfold Scoped.assoc_or; rewrite Es; unfold Scoped.choose.
    rewrite (assoc_map N_eq_dec (fun y => match select γk y with Some s => s | None => [] end) _ y)
      by (apply globals_in; exact Id).
    rewrite Es'; exact Vk.
  Qed.

  Lemma pview_inj (w t : list (Key * nat)) : map fst w = map fst t -> pview w = pview t -> w = t.
  Proof.
    revert t; induction w as [|[k p] w IH]; intros [|[k' p'] t]; cbn; try discriminate; [reflexivity|].
    intros Ek Ev; injection Ek as -> Ek; injection Ev as Ep Ev; subst p'; f_equal; auto.
  Qed.

  Lemma target_is_rel (γk : KState) (γb : BState) n f :
    KWF γk -> fibers γk n = Some f -> is_installed Σ (life f) = true ->
    target Σ bprog γb n = option_map pview (target Σ prog' γk n) ->
    target_is N_eq_dec Σ bprog γb n (pview (view_of Σ (life f))) =
    target_is kdec Σ prog' γk n (view_of Σ (life f)).
  Proof.
    intros W Hn Hi Et; unfold target_is; rewrite Et.
    destruct (target Σ prog' γk n) as [t|] eqn:Ht; cbn [option_map]; [|reflexivity].
    destruct (view_eq_dec kdec _ _) as [<-|Ne];
      destruct (view_eq_dec N_eq_dec _ _) as [Eb|Ne']; try reflexivity.
    - contradiction Ne'; reflexivity.
    - exfalso; apply Ne, pview_inj; [|exact Eb].
      rewrite (wf_view_keys _ _ _ _ W n f Hn Hi).
      unfold target in Ht; rewrite Hn in Ht; destruct (disposed f); [discriminate|].
      unfold fdeps; symmetry; exact (resolve_keys γk _ t Ht).
  Qed.

  (** *** [Pre] states read the same *)
  Lemma visible_pre (γ γ0 : KState) k : Pre γ γ0 -> visible Σ γ0 k = visible Σ γ k.
  Proof.
    intros P; destruct (pre_fibers γ γ0 P) as (Eb & _ & Hn & Hf); unfold visible; rewrite Eb.
    destruct (binds γ k) as [b|]; [|reflexivity].
    destruct (fibers γ0 (owner Σ b)) as [f0|] eqn:H0.
    - destruct (Hf _ f0 H0) as (f & H & El & _); rewrite H, El; reflexivity.
    - apply Hn in H0; rewrite H0; reflexivity.
  Qed.

  Lemma candidate_pre (γ γ0 : KState) y m : Pre γ γ0 -> candidate γ0 y m = candidate γ y m.
  Proof.
    intros P; destruct (pre_fibers γ γ0 P) as (_ & _ & Hn & Hf); unfold Scoped.candidate.
    destruct (fibers γ0 m) as [f0|] eqn:H0.
    - destruct (Hf _ f0 H0) as (f & H & _ & _ & _ & Eb & Es & _); rewrite H, Eb, Es.
      rewrite (visible_pre γ γ0 _ P); reflexivity.
    - apply Hn in H0; rewrite H0; reflexivity.
  Qed.

  Lemma select_pre (γ γ0 : KState) y : Pre γ γ0 -> select γ0 y = select γ y.
  Proof.
    intros P; destruct (pre_fibers γ γ0 P) as (_ & En & _).
    unfold Scoped.select, Scoped.candidates, names; rewrite En.
    assert (E : omap (candidate γ0 y) (seq 0 (next γ)) = omap (candidate γ y) (seq 0 (next γ))).
    { induction (seq 0 (next γ)) as [|a l IH]; cbn; [reflexivity|].
      rewrite (candidate_pre γ γ0 y a P), IH; reflexivity. }
    rewrite E; reflexivity.
  Qed.

  Lemma R_pre (γk γ0 : KState) (γb : BState) : R γk γb -> Pre γk γ0 -> R γ0 γb.
  Proof.
    intros Rr P; destruct (pre_fibers γk γ0 P) as (Eb & En & Hn & Hf).
    assert (Ef : forall m, option_map pfib (fibers γ0 m) = option_map pfib (fibers γk m)).
    { intros m; destruct (fibers γ0 m) as [f0|] eqn:H0.
      - destruct (Hf m f0 H0) as (f & H & El & Ep & Ed & Eb' & _); rewrite H; cbn.
        unfold pfib; rewrite El, Ep, Ed, Eb'; reflexivity.
      - apply Hn in H0; rewrite H0; reflexivity. }
    split.
    - rewrite (r_next _ _ Rr); unfold Calculus.next in En |- *; congruence.
    - intros m; rewrite Ef; exact (r_fib _ _ Rr m).
    - intros y b; rewrite (r_bind _ _ Rr); rewrite Eb; split.
      + intros (fo & Ho & Hb).
        destruct (fibers γ0 (owner Σ b)) as [f0|] eqn:H0.
        * destruct (Hf _ f0 H0) as (f & H & _ & _ & _ & _ & Es & _).
          rewrite Ho in H; injection H as <-; exists f0; rewrite Es; auto.
        * apply Hn in H0; congruence.
      + intros (f0 & H0 & Hb); destruct (Hf _ f0 H0) as (f & H & _ & _ & _ & _ & Es & _).
        exists f; rewrite <- Es; auto.
    - rewrite (r_op _ _ Rr); destruct P as [->|[(n & f & _ & _ & _ & ->)|(n & f & acc & w & _ & _ & ->)]]; reflexivity.
    - rewrite (r_ini _ _ Rr); destruct P as [->|[(n & f & _ & _ & _ & ->)|(n & f & acc & w & _ & _ & ->)]]; reflexivity.
  Qed.

  Lemma ki_pre (γ γ0 : KState) : KI γ -> Pre γ γ0 -> KI γ0.
  Proof.
    intros [I O Sh Ro] P; split.
    - exact (kinv_pre γ γ0 I P).
    - exact (opkey_pre γ γ0 O P).
    - exact (shaped_pre γ γ0 Sh P).
    - exact (roots_pre γ γ0 Ro P).
  Qed.

  (** *** Updates that keep the correspondence *)

  Lemma R_set_fiber (γk : KState) (γb : BState) n f f' :
    R γk γb -> fibers γk n = Some f -> scope (fcomp f') = scope (fcomp f) ->
    R (set_fiber Σ γk n f') (set_fiber Σ γb n (pfib f')).
  Proof.
    intros Rr Hn Es; unfold set_fiber, with_fibers.
    split; cbn [Calculus.fibers Calculus.binds Calculus.next Calculus.oplog Calculus.inilog].
    - exact (r_next _ _ Rr).
    - intros m; unfold fupd; destruct (Nat.eqb m n); [reflexivity | exact (r_fib _ _ Rr m)].
    - intros y b; rewrite (r_bind _ _ Rr); unfold fupd; split.
      + intros (fo & Ho & Hb); destruct (Nat.eqb_spec (owner Σ b) n) as [E|].
        * rewrite E, Hn in Ho; injection Ho as <-; exists f'; rewrite Es; auto.
        * exists fo; auto.
      + intros (fo' & Ho & Hb); destruct (Nat.eqb_spec (owner Σ b) n) as [E|].
        * injection Ho as <-; exists f; rewrite E, Hn, <- Es; auto.
        * exists fo'; auto.
    - exact (r_op _ _ Rr).
    - exact (r_ini _ _ Rr).
  Qed.

  Lemma R_set_life (γk : KState) (γb : BState) n f l :
    R γk γb -> fibers γk n = Some f -> R (set_life Σ γk n f l) (set_life Σ γb n (pfib f) (plife l)).
  Proof.
    intros Rr Hn; exact (R_set_fiber γk γb n f (mkFiber Σ (fcomp f) (fparent f) (disposed f) l) Rr Hn eq_refl).
  Qed.

  Lemma R_bump (γk : KState) (γb : BState) : R γk γb -> R (bump Σ γk) (bump Σ γb).
  Proof.
    intros Rr; split; cbn; [rewrite (r_next _ _ Rr); reflexivity | exact (r_fib _ _ Rr) | exact (r_bind _ _ Rr)
                           | exact (r_op _ _ Rr) | exact (r_ini _ _ Rr)].
  Qed.

  Lemma R_log_op (γk : KState) (γb : BState) t a : R γk γb -> R (log_op Σ γk t a) (log_op Σ γb t a).
  Proof.
    intros Rr; split; cbn; [exact (r_next _ _ Rr) | exact (r_fib _ _ Rr) | exact (r_bind _ _ Rr)
                           | rewrite (r_op _ _ Rr); reflexivity | exact (r_ini _ _ Rr)].
  Qed.

  Lemma R_log_ini (γk : KState) (γb : BState) p s : R γk γb -> R (log_ini Σ γk p s) (log_ini Σ γb p s).
  Proof.
    intros Rr; split; cbn; [exact (r_next _ _ Rr) | exact (r_fib _ _ Rr) | exact (r_bind _ _ Rr)
                           | exact (r_op _ _ Rr) | rewrite (r_ini _ _ Rr); reflexivity].
  Qed.

  (** Writing the binding of [y], owned by [o], at [o]'s key. *)
  Lemma R_bupd (γk : KState) (γb : BState) o fo y ob :
    R γk γb -> fibers γk o = Some fo ->
    (forall b0, binds γb y = Some b0 -> owner Σ b0 = o) -> (forall b, ob = Some b -> owner Σ b = o) ->
    R (with_binds Σ γk (bupd kdec Σ (binds γk) (scope (fcomp fo), y) ob))
      (with_binds Σ γb (bupd N_eq_dec Σ (binds γb) y ob)).
  Proof.
    intros Rr Ho Hold Hnew; unfold with_binds.
    split; cbn [Calculus.fibers Calculus.binds Calculus.next Calculus.oplog Calculus.inilog];
      [exact (r_next _ _ Rr) | exact (r_fib _ _ Rr) | | exact (r_op _ _ Rr) | exact (r_ini _ _ Rr)].
    intros y' b'; unfold bupd, keqb.
    destruct (N_eq_dec y' y) as [->|Ny].
    - split.
      + intros Eb; subst ob; rewrite (Hnew b' eq_refl); exists fo; split; [exact Ho|].
        destruct (kdec _ _); [reflexivity | contradiction].
      + intros (fo' & Ho' & Hb).
        destruct (kdec (scope (fcomp fo'), y) (scope (fcomp fo), y)) as [_|Ne]; [exact Hb|].
        exfalso; assert (Cb : binds γb y = Some b') by (apply (r_bind _ _ Rr); eauto).
        rewrite (Hold b' Cb), Ho in Ho'; injection Ho' as <-; contradiction Ne; reflexivity.
    - rewrite (r_bind _ _ Rr); split.
      + intros (fo' & Ho' & Hb); exists fo'; split; [exact Ho'|].
        destruct (kdec _ _) as [E|]; [injection E as _ E; contradiction | exact Hb].
      + intros (fo' & Ho' & Hb); exists fo'; split; [exact Ho'|].
        destruct (kdec _ _) as [E|]; [injection E as _ E; contradiction | exact Hb].
  Qed.

  (** A new fiber at [next]. *)
  Lemma R_add (γk : KState) (γb : BState) fk :
    R γk γb -> (forall k b, binds γk k = Some b -> fibers γk (owner Σ b) <> None) ->
    fibers γk (next γk) = None ->
    R (bump Σ (with_fibers Σ γk (fupd Σ (fibers γk) (next γk) (Some fk))))
      (bump Σ (with_fibers Σ γb (fupd Σ (fibers γb) (next γb) (Some (pfib fk))))).
  Proof.
    intros Rr Ho Hf; rewrite (r_next _ _ Rr).
    split; cbn [Calculus.fibers Calculus.binds Calculus.next Calculus.oplog Calculus.inilog bump with_fibers].
    - rewrite (r_next _ _ Rr); reflexivity.
    - intros m; unfold fupd; destruct (Nat.eqb m (next γk)); [reflexivity | exact (r_fib _ _ Rr m)].
    - intros y b; rewrite (r_bind _ _ Rr); unfold fupd; split.
      + intros (fo & H & Hb); exists fo; destruct (Nat.eqb_spec (owner Σ b) (next γk)) as [E|]; [|auto].
        rewrite E, Hf in H; discriminate.
      + intros (fo & H & Hb); destruct (Nat.eqb_spec (owner Σ b) (next γk)) as [E|]; [|eauto].
        exfalso; apply (Ho _ b Hb); rewrite E; exact Hf.
    - exact (r_op _ _ Rr).
    - exact (r_ini _ _ Rr).
  Qed.

  Lemma R_remove (γk : KState) (γb : BState) n :
    R γk γb -> (forall k b, binds γk k = Some b -> owner Σ b <> n) ->
    R (with_fibers Σ γk (fupd Σ (fibers γk) n None)) (with_fibers Σ γb (fupd Σ (fibers γb) n None)).
  Proof.
    intros Rr Ho.
    split; cbn [Calculus.fibers Calculus.binds Calculus.next Calculus.oplog Calculus.inilog with_fibers].
    - exact (r_next _ _ Rr).
    - intros m; unfold fupd; destruct (Nat.eqb m n); [reflexivity | exact (r_fib _ _ Rr m)].
    - intros y b; rewrite (r_bind _ _ Rr); unfold fupd; split.
      + intros (fo & H & Hb); exists fo; destruct (Nat.eqb_spec (owner Σ b) n) as [E|]; [|auto].
        exfalso; exact (Ho _ b Hb E).
      + intros (fo & H & Hb); destruct (Nat.eqb_spec (owner Σ b) n); [discriminate | eauto].
    - exact (r_op _ _ Rr).
    - exact (r_ini _ _ Rr).
  Qed.

  (** *** Guards read the same on both sides *)
  Lemma existsb_ext' {A : Type} (f g : A -> bool) (l : list A) :
    (forall a, f a = g a) -> existsb f l = existsb g l.
  Proof. intros H; induction l as [|a l IH]; cbn; [reflexivity | rewrite H, IH; reflexivity]. Qed.

  Lemma existsb_map' {A B : Type} (f : B -> bool) (g : A -> B) (l : list A) :
    existsb f (map g l) = existsb (fun a => f (g a)) l.
  Proof. induction l as [|a l IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma resolves_R (γk : KState) (γb : BState) m p :
    R γk γb -> resolves Σ γk m p = resolves Σ γb m p.
  Proof.
    intros Rr; unfold resolves; rewrite (r_fib _ _ Rr m).
    destruct (fibers γk m) as [f|]; cbn; [|reflexivity].
    rewrite plife_installed, plife_view; f_equal; unfold pview; rewrite existsb_map'; reflexivity.
  Qed.

  Lemma relied_R (γk : KState) (γb : BState) n p :
    R γk γb -> relied Σ γk n p = relied Σ γb n p.
  Proof.
    intros Rr; unfold relied, names; rewrite (r_next _ _ Rr).
    apply existsb_ext'; intros m; rewrite (resolves_R γk γb m p Rr); reflexivity.
  Qed.

  Lemma held_R (γk : KState) (γb : BState) n acc :
    R γk γb -> held Σ γk n acc = held Σ γb n (map pundo acc).
  Proof.
    intros Rr; unfold held; rewrite existsb_map'; apply existsb_ext'; intros [k p t g|k p|m]; cbn; auto.
    apply relied_R; exact Rr.
  Qed.

  Lemma has_child_R (γk : KState) (γb : BState) n :
    R γk γb -> has_child Σ γk n = has_child Σ γb n.
  Proof.
    intros Rr; unfold has_child, names; rewrite (r_next _ _ Rr).
    apply existsb_ext'; intros m; rewrite (r_fib _ _ Rr m); destruct (fibers γk m); reflexivity.
  Qed.

  (** *** A child begins exactly when the core lets it *)
  Lemma child_begin (γk : KState) (γb : BState) n f q tb :
    KI γk -> R γk γb -> fibers γk n = Some f -> fparent f = Some q ->
    target Σ bprog γb n = Some tb -> fresh γk f = true.
  Proof.
    intros I Rr Hn Hp Ht; pose proof (ki_wf _ _ _ _ (ki_kinv _ I)) as W.
    unfold target in Ht; rewrite (fib_k2b γk γb n f Rr Hn) in Ht; cbn [pfib Calculus.disposed Calculus.comp] in Ht.
    destruct (disposed f); [discriminate|].
    pose proof (resolve_all γb _ tb Ht) as Hv.
    destruct (wf_parent _ _ _ _ W n f q Hn Hp) as (fq & Hq & Iq & Uq).
    pose proof (ki_spawn _ _ _ _ (ki_kinv _ I) q fq n f Hq Uq Hn) as Ks.
    pose proof (si_child _ _ _ _ (ki_si _ _ _ _ (ki_kinv _ I)) n f q fq Hn Hp Hq) as Ei.
    assert (Sel : forall y, In y (globals (base (fcomp f))) -> select γk y = Some (assoc_or y (sel (fcomp fq)))).
    { intros y Hy.
      destruct (Hv y) as (p & V).
      { cbn [bprog deps]; apply globals_in in Hy; exact (in_map dname _ (Global y) Hy). }
      destruct (view_has γk q fq y W Hq Iq (kSub _ _ Ks y Hy)) as (p0 & Ip).
      destruct (select_vis γk γb y p I Rr V) as (b & fo & Hb & Ho & Es & _).
      destruct (wf_view _ _ _ _ W q fq _ p0 Hq Ip) as (b0 & Hb0 & _ & _).
      rewrite (bind_k2b γk γb _ y b0 W Rr Hb0) in Hb; injection Hb as <-.
      destruct (owner_scope γk _ y b0 W Hb0) as (fo' & Ho' & _ & Es' & _).
      rewrite Ho in Ho'; injection Ho' as <-; rewrite Es, Es'; reflexivity. }
    unfold Scoped.fresh; apply andb_true_iff; split.
    - unfold Scoped.all_selected; apply forallb_forall; intros y Hy.
      unfold Scoped.selected; rewrite (Sel y Hy); reflexivity.
    - assert (E : sel (fcomp f) = choose γk (base (fcomp f))).
      { rewrite Ei; unfold Scoped.inherit, Scoped.choose; apply map_ext_in; intros y Hy.
        rewrite (Sel y Hy); reflexivity. }
      destruct (list_eq_dec _ _ _) as [_|Q]; [reflexivity | contradiction].
  Qed.

  (** *** Looking up a view *)
  Lemma lookup_proj (x : XC) (w : list (Key * nat)) y :
    (forall k p, In (k, p) w -> fst k = assoc_or (snd k) (sel x)) ->
    lookup_view kdec (assoc_or y (sel x), y) w = lookup_view N_eq_dec y (pview w).
  Proof.
    induction w as [|[[s z] p] w IH]; cbn; intros H; [reflexivity|].
    unfold keqb; destruct (N_eq_dec y z) as [<-|Ne].
    - pose proof (H (s, y) p (or_introl eq_refl)) as Hs; cbn in Hs; subst s.
      destruct (kdec _ _); [reflexivity | contradiction].
    - destruct (kdec _ _) as [E|]; [injection E as _ E; contradiction|].
      apply IH; intros k p' I; exact (H k p' (or_intror I)).
  Qed.

  Lemma kmem_deps_none (x : XC) y :
    find (fun d => neqb N_eq_dec (dname d) y) (xdeps Σ (xprog (base x))) = None ->
    kmem kdec (scope x, y) (deps Σ (prog' x)) = false /\
    kmem N_eq_dec y (deps Σ (bprog (base x))) = false.
  Proof.
    intros Hf; pose proof (find_none _ _ Hf) as Hn; split.
    - apply not_true_iff_false; intros K; unfold kmem in K; apply existsb_exists in K as (k & Ik & Ek).
      cbn [Scoped.prog' deps] in Ik; apply in_map_iff in Ik as (d & <- & Id).
      unfold keqb in Ek; destruct (kdec _ _) as [E|]; [|discriminate].
      specialize (Hn d Id); unfold neqb in Hn.
      pose proof (f_equal snd E) as E2; cbn in E2; rewrite snd_dkey in E2.
      destruct (N_eq_dec (dname d) y); [discriminate | congruence].
    - apply not_true_iff_false; intros K; apply kmem_name in K.
      cbn [bprog deps] in K; apply in_map_iff in K as (d & Ed & Id).
      specialize (Hn d Id); unfold neqb in Hn; destruct (N_eq_dec (dname d) y); [discriminate | congruence].
  Qed.

  (** *** The extension's spawns and reactions never conflict *)
  Lemma spawn_noconf (γk : KState) n f x P acc w :
    SI N_eq_dec Σ xprog γk -> fibers γk n = Some f -> life f = Loading Σ (PSpawn x P) acc w ->
    conflict kdec Σ prog' γk x = false.
  Proof.
    intros S Hn Hl.
    destruct (si_load _ _ _ _ S n f Hn _ acc w Hl) as (j & Q & EP & K).
    destruct Q as [| | | |c Q']; cbn in EP; try discriminate; injection EP as -> _.
    apply (conflict_scope N_eq_dec Σ xprog); intros m fm Hm E; cbn in E.
    specialize (K m fm j Hm E); lia.
  Qed.

  Lemma react_noconf (γk : KState) n f c i :
    SI N_eq_dec Σ xprog γk -> fibers γk n = Some f ->
    conflict kdec Σ prog' (retick Σ γk n f)
      (child N_eq_dec Σ xprog (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f)) (sel (fcomp f)) (next γk))
             (Re (0 + i) (next γk)) c) = false.
  Proof.
    intros S Hn; apply (conflict_scope N_eq_dec Σ xprog); intros m fm Hm E.
    unfold Scoped.retick in Hm; apply (fibers_set_fiber_inv Σ) in Hm as [[-> ->]|[_ Hm]].
    - cbn in E; apply (f_equal (@length _)) in E; cbn in E; lia.
    - pose proof (si_bound _ _ _ _ S m fm Hm (Re (0 + i) (next γk))) as B.
      rewrite E in B; cbn in B; specialize (B (or_introl eq_refl)); lia.
  Qed.

  (** *** One step of a Loading fiber, one undo item *)

  Lemma kmem_in_k (k : Key) (l : list Key) : In k l -> kmem kdec k l = true.
  Proof.
    intros I; unfold kmem; apply existsb_exists; exists k; split; [exact I|].
    unfold keqb; destruct (kdec k k); [reflexivity | contradiction].
  Qed.

  Lemma lookup_in (k : Key) (w : list (Key * nat)) p : lookup_view kdec k w = Some p -> In (k, p) w.
  Proof.
    induction w as [|[k' p'] w IH]; cbn; [discriminate|].
    unfold keqb; destruct (kdec k k') as [<-|]; [intros [= <-]; left; reflexivity | intros H; right; auto].
  Qed.

  Lemma overlaps_in (y : N) (l1 l2 : list N) :
    In y l1 -> In y l2 -> overlaps N_eq_dec l1 l2 = true.
  Proof.
    intros I1 I2; unfold overlaps; apply existsb_exists; exists y; split; [exact I1|].
    apply kmem_name; exact I2.
  Qed.

  Lemma load_sim (γk : KState) (γb : BState) n f P acc w :
    KI γk -> BWF γb -> R γk γb -> fibers γk n = Some f -> life f = Loading Σ P acc w ->
    (forall x Q, P = PSpawn x Q -> conflict N_eq_dec Σ bprog γb (base x) = false) ->
    R (load_step kdec Σ prog' γk n f P acc w)
      (load_step N_eq_dec Σ bprog γb n (pfib f) (unlift P) (map pundo acc) (pview w)).
  Proof.
    intros I Wb Rr Hn Hl Hc.
    pose proof (ki_wf _ _ _ _ (ki_kinv _ I)) as W; pose proof (ki_si _ _ _ _ (ki_kinv _ I)) as Si.
    destruct (si_load _ _ _ _ Si n f Hn P acc w Hl) as (j & Q & EP & _); subst P.
    rewrite unlift_lift.
    assert (Hfin : forall γ1 γ2 l, R γ1 γ2 -> fibers γ1 n = Some f ->
               R (set_life Σ γ1 n f l) (set_life Σ γ2 n (pfib f) (plife l)))
      by (intros γ1 γ2 l R1 H1; exact (R_set_life γ1 γ2 n f l R1 H1)).
    destruct Q as [| |y a κ|y st Q'|c Q']; unfold load_step; cbn [Scoped.lift]; try rewrite (r_next _ _ Rr).
    - exact (Hfin γk γb _ Rr Hn).
    - exact (Hfin γk γb _ Rr Hn).
    - (* an operation *)
      assert (Hop : forall k b o0 fo,
                binds γk k = Some b -> binds γb y = Some b -> snd k = y ->
                fibers γk o0 = Some fo -> owner Σ b = o0 -> scope (fcomp fo) = fst k ->
                R (match run a (next γk) (bst Σ b) with
                   | Some (s', g, o) =>
                       set_life Σ (bump Σ (log_op Σ (with_binds Σ γk (bupd kdec Σ (binds γk) k
                         (Some (mkBinding Σ (pid Σ b) (owner Σ b) s')))) (next γk) a)) n f
                         (Loading Σ (lift N_eq_dec Σ xprog (fcomp f) j (κ o)) (UOp Σ k (pid Σ b) (next γk) g :: acc) w)
                   | None => set_life Σ (bump Σ γk) n f (Unloading Σ acc w (Some EOp))
                   end)
                  (match run a (next γk) (bst Σ b) with
                   | Some (s', g, o) =>
                       set_life Σ (bump Σ (log_op Σ (with_binds Σ γb (bupd N_eq_dec Σ (binds γb) y
                         (Some (mkBinding Σ (pid Σ b) (owner Σ b) s')))) (next γk) a)) n (pfib f)
                         (Loading Σ (κ o) (UOp Σ y (pid Σ b) (next γk) g :: map pundo acc) (pview w))
                   | None => set_life Σ (bump Σ γb) n (pfib f) (Unloading Σ (map pundo acc) (pview w) (Some EOp))
                   end)).
      { intros [s0 y0] b o0 fo Hk Hb Ey Ho Eo Es; cbn in Ey, Es; subst y0 s0.
        destruct (run a (next γk) (bst Σ b)) as [[[s' g] o]|].
        - assert (R1 := R_bupd γk γb o0 fo y (Some (mkBinding Σ (pid Σ b) (owner Σ b) s')) Rr Ho
                          (fun b0 H0 => ltac:(rewrite Hb in H0; injection H0 as <-; exact Eo))
                          (fun b1 E => ltac:(injection E as <-; exact Eo))).
          pose proof (Hfin _ _ (Loading Σ (lift N_eq_dec Σ xprog (fcomp f) j (κ o)) (UOp Σ (scope (fcomp fo), y) (pid Σ b) (next γk) g :: acc) w)
                        (R_bump _ _ (R_log_op _ _ (next γk) a R1)) Hn) as R2.
          cbn [plife map pundo snd] in R2; rewrite unlift_lift in R2; exact R2.
        - exact (Hfin _ _ _ (R_bump _ _ Rr) Hn). }
      cbn [Calculus.comp pfib bprog deps].
      unfold keyof; destruct (find (fun d => neqb N_eq_dec (dname d) y) (xdeps Σ (xprog (base (fcomp f))))) as [d|] eqn:Ef.
      + apply find_some in Ef as [Id Ed]; unfold neqb in Ed.
        destruct (N_eq_dec (dname d) y) as [Edy|]; [|discriminate].
        rewrite (dkey_dep _ d Id), Edy.
        assert (K1 : kmem kdec (assoc_or y (sel (fcomp f)), y) (deps Σ (prog' (fcomp f))) = true).
        { apply kmem_in_k; cbn [Scoped.prog' deps]; rewrite <- Edy, <- (dkey_dep _ d Id); apply in_map; exact Id. }
        assert (K2 : kmem N_eq_dec y (map dname (xdeps Σ (xprog (base (fcomp f))))) = true).
        { apply kmem_name; rewrite <- Edy; apply in_map; exact Id. }
        rewrite K1, K2.
        rewrite (lookup_proj (fcomp f) w y).
        2:{ intros [s z] p I0; exact (proj2 (view_entry γk n f s z p W Hn ltac:(rewrite Hl; exact I0))). }
        destruct (lookup_view N_eq_dec y (pview w)) as [p0|] eqn:Lk.
        * rewrite <- (lookup_proj (fcomp f) w y) in Lk.
          2:{ intros [s z] p I0; exact (proj2 (view_entry γk n f s z p W Hn ltac:(rewrite Hl; exact I0))). }
          apply lookup_in in Lk.
          destruct (wf_view _ _ _ _ W n f _ p0 Hn ltac:(rewrite Hl; exact Lk)) as (b0 & Hb0 & Ep & _).
          pose proof (bind_k2b γk γb _ y b0 W Rr Hb0) as Hbb.
          rewrite Hb0, Hbb; subst p0; cbv beta iota; rewrite Nat.eqb_refl.
          destruct (owner_scope γk _ y b0 W Hb0) as (fo & Ho & _ & Es & _).
          exact (Hop _ b0 (owner Σ b0) fo Hb0 Hbb eq_refl Ho eq_refl Es).
        * exact (Hfin γk γb _ Rr Hn).
      + destruct (kmem_deps_none (fcomp f) y Ef) as [K1 K2].
        cbn [bprog deps] in K2; rewrite K1, K2.
        destruct (binds γk (scope (fcomp f), y)) as [b0|] eqn:Hk.
        * destruct (proj1 (bind_own γk γb n f y b0 I Rr Hn) Hk) as [Hb Eo].
          rewrite Hb, (proj2 (Nat.eqb_eq _ _) Eo); cbv beta iota; rewrite Nat.eqb_refl.
          exact (Hop _ b0 n f Hk Hb eq_refl Hn Eo eq_refl).
        * destruct (binds γb y) as [b1|] eqn:Hb.
          -- destruct (Nat.eqb_spec (owner Σ b1) n) as [Eo|Ne].
             ++ exfalso; pose proof (proj2 (bind_own γk γb n f y b1 I Rr Hn) (conj Hb Eo)) as C1; congruence.
             ++ exact (Hfin γk γb _ Rr Hn).
          -- exact (Hfin γk γb _ Rr Hn).
    - (* a provision *)
      cbn [Calculus.comp pfib bprog Scoped.prog' provs].
      assert (Ek : kmem kdec (scope (fcomp f), y) (map (pair (scope (fcomp f))) (xprovs (base (fcomp f))))
                   = kmem N_eq_dec y (xprovs (base (fcomp f)))).
      { destruct (kmem N_eq_dec y _) eqn:Km.
        - apply kmem_pair; split; [reflexivity|]; apply kmem_name; exact Km.
        - apply not_true_iff_false; intros K; apply kmem_pair in K as [_ K].
          apply kmem_name in K; congruence. }
      rewrite Ek; destruct (kmem N_eq_dec y (xprovs (base (fcomp f)))) eqn:Km; [|exact (Hfin γk γb _ Rr Hn)].
      destruct (binds γk (scope (fcomp f), y)) as [b0|] eqn:Hk.
      + rewrite (proj1 (proj1 (bind_own γk γb n f y b0 I Rr Hn) Hk)); exact (Hfin γk γb _ Rr Hn).
      + assert (Hb : binds γb y = None).
        { destruct (binds γb y) as [b1|] eqn:Hb; [exfalso|reflexivity].
          destruct (Nat.eq_dec (owner Σ b1) n) as [Eo|Ne].
          - pose proof (proj2 (bind_own γk γb n f y b1 I Rr Hn) (conj Hb Eo)); congruence.
          - destruct (wf_bind _ _ _ _ Wb y b1 Hb) as (fo & Ho & _ & Ko & _).
            pose proof (wf_disjoint _ _ _ _ Wb n (owner Σ b1) (pfib f) fo (fun E => Ne (eq_sym E))
                          (fib_k2b γk γb n f Rr Hn) Ho) as D.
            unfold fprovs in D, Ko; cbn [pfib Calculus.comp bprog provs] in D, Ko.
            apply kmem_name in Km, Ko; rewrite (overlaps_in y _ _ Km Ko) in D; discriminate. }
        rewrite Hb.
        assert (R1 := R_bupd γk γb n f y (Some (mkBinding Σ (next γk) n st)) Rr Hn
                        (fun b0 H0 => ltac:(congruence)) (fun b1 E => ltac:(injection E as <-; reflexivity))).
        pose proof (Hfin _ _ (Loading Σ (lift N_eq_dec Σ xprog (fcomp f) j Q') (UProv Σ (scope (fcomp f), y) (next γk) :: acc) w)
                      (R_bump _ _ (R_log_ini _ _ (next γk) st R1)) Hn) as R2.
        cbn [plife map pundo snd] in R2; rewrite unlift_lift in R2; exact R2.
    - (* a spawn *)
      cbn in Hl.
      rewrite (spawn_noconf γk n f _ _ acc w Si Hn Hl).
      pose proof (Hc (child N_eq_dec Σ xprog (fcomp f) (Sp j) c) _ eq_refl) as Hc'; cbn [base Scoped.child] in Hc'; rewrite Hc'.
      pose proof (fresh_none _ _ _ _ W) as Hfr.
      assert (Ho : forall k b, binds γk k = Some b -> fibers γk (owner Σ b) <> None).
      { intros k b Hb; destruct (wf_bind _ _ _ _ W k b Hb) as (fo & Ho & _); congruence. }
      pose proof (R_add γk γb (mkFiber Σ (child N_eq_dec Σ xprog (fcomp f) (Sp j) c) (Some n) false (Inactive Σ None))
                    Rr Ho Hfr) as R1.
      rewrite (r_next _ _ Rr) in R1.
      assert (Hn1 : fibers (bump Σ (with_fibers Σ γk (fupd Σ (fibers γk) (next γk)
                      (Some (mkFiber Σ (child N_eq_dec Σ xprog (fcomp f) (Sp j) c) (Some n) false (Inactive Σ None)))))) n = Some f).
      { cbn; unfold fupd; destruct (Nat.eqb_spec n (next γk)) as [E|]; [|exact Hn].
        rewrite E, Hfr in Hn; discriminate. }
      pose proof (Hfin _ _ (Loading Σ (lift N_eq_dec Σ xprog (fcomp f) (S j) Q') (USpawn Σ (next γk) :: acc) w) R1 Hn1) as R2.
      cbn [plife map pundo] in R2; rewrite unlift_lift in R2.
      exact R2.
  Qed.

  Definition ORel (o1 : option KState) (o2 : option BState) : Prop :=
    match o1, o2 with
    | Some a, Some b => R a b
    | None, None => True
    | _, _ => False
    end.

  Lemma undo_sim (γk : KState) (γb : BState) n f u acc w z :
    KI γk -> R γk γb -> fibers γk n = Some f -> life f = Unloading Σ (u :: acc) w z ->
    ORel (undo_step kdec Σ γk n f u acc w z)
         (undo_step N_eq_dec Σ γb n (pfib f) (pundo u) (map pundo acc) (pview w) z).
  Proof.
    intros I Rr Hn Hl; pose proof (ki_wf _ _ _ _ (ki_kinv _ I)) as W.
    assert (Hfin : forall γ1 γ2, R γ1 γ2 -> fibers γ1 n = Some f ->
               R (set_life Σ γ1 n f (Unloading Σ acc w z)) (set_life Σ γ2 n (pfib f) (Unloading Σ (map pundo acc) (pview w) z)))
      by (intros γ1 γ2 R1 H1; exact (R_set_life γ1 γ2 n f _ R1 H1)).
    destruct u as [[s y] p t g|[s y] p|m]; unfold undo_step; cbn [pundo snd ORel].
    - destruct (binds γk (s, y)) as [b|] eqn:Hk.
      + rewrite (bind_k2b γk γb s y b W Rr Hk).
        destruct (Nat.eqb (pid Σ b) p); cbn [ORel]; [|exact (Hfin _ _ Rr Hn)].
        destruct (owner_scope γk s y b W Hk) as (fo & Ho & _ & Es & _).
        pose proof (R_bupd γk γb (owner Σ b) fo y (Some (mkBinding Σ (pid Σ b) (owner Σ b) (g (bst Σ b)))) Rr Ho
                      (fun b0 H0 => ltac:(rewrite (bind_k2b γk γb s y b W Rr Hk) in H0; injection H0 as <-; reflexivity))
                      (fun b1 E => ltac:(injection E as <-; reflexivity))) as R1.
        rewrite Es in R1; exact (Hfin _ _ R1 Hn).
      + destruct (binds γb y) as [b1|] eqn:Hb; [destruct (Nat.eqb_spec (pid Σ b1) p) as [Ep|]|]; cbn [ORel];
          try exact (Hfin _ _ Rr Hn).
        exfalso; apply (r_bind _ _ Rr) in Hb as (fo & Ho & Hk1).
        assert (Iu : In (UOp Σ (s, y) p t g) (acc_of Σ (life f))) by (rewrite Hl; left; reflexivity).
        pose proof (ki_opkey _ I n f (s, y) p t g Hn Iu _ b1 Hk1 Ep) as E.
        injection E as Es; rewrite Es in Hk1; congruence.
    - rewrite <- (relied_R γk γb n p Rr).
      destruct (relied Σ γk n p); cbn [ORel]; [exact Logic.I|].
      assert (Iu : In (UProv Σ (s, y) p) (acc_of Σ (life f))) by (rewrite Hl; left; reflexivity).
      destruct (wf_uprov _ _ _ _ W n f _ p Hn Iu) as (b & Hk & Ep & Eo).
      pose proof (bind_k2b γk γb s y b W Rr Hk) as Hb.
      rewrite Hk, Hb, Ep, Nat.eqb_refl; cbn [ORel].
      destruct (owner_scope γk s y b W Hk) as (fo & Ho & _ & Es & _).
      rewrite Eo, Hn in Ho; injection Ho as <-.
      pose proof (R_bupd γk γb n f y None Rr Hn
                    (fun b0 H0 => ltac:(rewrite Hb in H0; injection H0 as <-; exact Eo))
                    (fun b1 E => ltac:(discriminate E))) as R1.
      rewrite Es in R1; exact (Hfin _ _ R1 Hn).
    - rewrite (r_fib _ _ Rr m); destruct (fibers γk m); cbn [option_map ORel]; [exact Logic.I | exact (Hfin _ _ Rr Hn)].
  Qed.

  (** *** Where the two calculi part *)

  (** The core meets a conflict at a spawn or a reaction. *)
  Definition spawn_conflict (γb : BState) n : bool :=
    match fibers γb n with
    | Some f => match life f with
                | Loading _ (PSpawn c _) _ _ => conflict N_eq_dec Σ bprog γb c
                | _ => false
                end
    | None => false
    end.

  Definition react_conflict (γb : BState) n i : bool :=
    match fibers γb n with
    | Some f => match nth_error (reacts Σ (bprog (fcomp f))) i with
                | Some c => conflict N_eq_dec Σ bprog γb c
                | None => false
                end
    | None => false
    end.

  (** Some provider in the fiber's view is no longer visible. *)
  Definition displaced (γb : BState) n : bool :=
    match fibers γb n with
    | Some f => displacedb γb (view_of Σ (life f))
    | None => false
    end.

  (** The steps the two calculi make alike. *)
  Definition ok (γk : KState) (γb : BState) (ℓ : @Label C) : bool :=
    match ℓ with
    | OInsert c => negb (taken Σ γk (xinst Σ (xprog c))) && negb (conflict N_eq_dec Σ bprog γb c)
    | OReact n i => negb (react_conflict γb n i)
    | LStep n => negb (spawn_conflict γb n) && negb (displaced γb n)
    | _ => true
    end.

  Lemma resolve_in (γ : BState) ys t y p : resolve Σ γ ys = Some t -> In (y, p) t -> visible Σ γ y = Some p.
  Proof.
    revert t; induction ys as [|y' ys IH]; cbn; intros t H I; [injection H as <-; contradiction|].
    destruct (visible Σ γ y') as [p'|] eqn:V; [|discriminate].
    destruct (resolve Σ γ ys) as [t'|] eqn:E; [|discriminate]; injection H as <-.
    destruct I as [Q|I]; [injection Q as -> ->; exact V | exact (IH t' eq_refl I)].
  Qed.

  (** A stale selection: the core target has turned too. *)
  Lemma stale_target (γk : KState) (γb : BState) n f :
    KI γk -> R γk γb -> fibers γk n = Some f -> is_installed Σ (life f) = true -> fresh γk f = false ->
    target_is N_eq_dec Σ bprog γb n (pview (view_of Σ (life f))) = false.
  Proof.
    intros I Rr Hn Hi Fr.
    rewrite (fresh_iff γk γb n f I Rr Hn Hi) in Fr; apply negb_false_iff in Fr.
    unfold displacedb in Fr; apply existsb_exists in Fr as ([y p] & Ip & Ev); cbn in Ev.
    destruct (visible Σ γb y) eqn:V; [discriminate|].
    unfold target_is; destruct (target Σ bprog γb n) as [t|] eqn:Ht; [|reflexivity].
    destruct (view_eq_dec N_eq_dec _ _) as [E|]; [|reflexivity].
    exfalso; unfold target in Ht; destruct (fibers γb n) as [fb|]; [|discriminate].
    destruct (disposed fb); [discriminate|].
    rewrite E in Ip; rewrite (resolve_in γb _ t y p Ht Ip) in V; discriminate.
  Qed.

  Lemma may_step_rel (γk : KState) (γb : BState) n f P acc w :
    KI γk -> R γk γb -> fibers γk n = Some f -> life f = Loading Σ P acc w -> fresh γk f = true ->
    may_step N_eq_dec Σ bprog γb n (unlift P) (pview w) = may_step kdec Σ prog' γk n P w.
  Proof.
    intros I Rr Hn Hl Fr; pose proof (ki_wf _ _ _ _ (ki_kinv _ I)) as W.
    destruct P; cbn [unlift may_step]; try reflexivity.
    assert (Hi : is_installed Σ (life f) = true) by (rewrite Hl; reflexivity).
    pose proof (target_is_rel γk γb n f W Hn Hi (target_fresh γk γb n f I Rr Hn Fr)) as E.
    rewrite Hl in E; exact E.
  Qed.

  Lemma all_selected_pre (γ γ0 : KState) c : Pre γ γ0 ->
    all_selected N_eq_dec Σ xprog γ0 c = all_selected N_eq_dec Σ xprog γ c.
  Proof.
    intros P; unfold Scoped.all_selected, Scoped.selected.
    induction (globals c) as [|y l IH]; cbn; [reflexivity|]; rewrite (select_pre γ γ0 y P), IH; reflexivity.
  Qed.

  Lemma choose_pre (γ γ0 : KState) c : Pre γ γ0 -> choose γ0 c = choose γ c.
  Proof.
    intros P; unfold Scoped.choose; apply map_ext; intros y; rewrite (select_pre γ γ0 y P); reflexivity.
  Qed.

  Lemma not_all_selected (γk : KState) (γb : BState) n f :
    KI γk -> R γk γb -> fibers γk n = Some f ->
    all_selected N_eq_dec Σ xprog γk (base (fcomp f)) = false -> target Σ bprog γb n = None.
  Proof.
    intros I Rr Hn A; unfold target; rewrite (fib_k2b γk γb n f Rr Hn); cbn [pfib Calculus.disposed Calculus.comp].
    destruct (disposed f); [reflexivity|].
    destruct (resolve Σ γb _) as [tb|] eqn:Ht; [exfalso|reflexivity].
    apply not_true_iff_false in A; apply A; unfold Scoped.all_selected; apply forallb_forall; intros y Hy.
    destruct (resolve_all γb _ tb Ht y) as (p & V).
    { cbn [bprog deps]; apply globals_in in Hy; exact (in_map dname _ (Global y) Hy). }
    destruct (select_vis γk γb y p I Rr V) as (b & fo & _ & _ & Es & _).
    unfold Scoped.selected; rewrite Es; reflexivity.
  Qed.

  (** *** Unfolding the core rules, for any keys *)
  Section Unfold.
    Context {K' C' : Type} (Kd : forall x y : K', {x = y} + {x <> y}) (pr : C' -> @Component K' Σ C').
    Local Notation St := (@State K' Σ C').

    Lemma step_begin (γ : St) n f :
      fibers γ n = Some f -> life f = Inactive Σ None ->
      step Kd Σ pr γ (LBegin n) =
      option_map (fun w => set_life Σ γ n f (Loading Σ (body Σ (pr (fcomp f))) [] w)) (target Σ pr γ n).
    Proof. intros Hn Hl; cbn [Calculus.step]; rewrite Hn, Hl; destruct (target Σ pr γ n); reflexivity. Qed.

    Lemma step_lstep (γ : St) n f P acc w :
      fibers γ n = Some f -> life f = Loading Σ P acc w ->
      step Kd Σ pr γ (LStep n) = if may_step Kd Σ pr γ n P w then Some (load_step Kd Σ pr γ n f P acc w) else None.
    Proof. intros Hn Hl; cbn [Calculus.step]; rewrite Hn, Hl; reflexivity. Qed.

    Lemma step_lstep_none (γ : St) n f :
      fibers γ n = Some f -> (forall P acc w, life f <> Loading Σ P acc w) -> step Kd Σ pr γ (LStep n) = None.
    Proof.
      intros Hn Hl; cbn [Calculus.step]; rewrite Hn.
      destruct (life f) eqn:E; try reflexivity; exfalso; eapply Hl; reflexivity.
    Qed.

    Lemma step_divert (γ : St) n f P acc w :
      fibers γ n = Some f -> life f = Loading Σ P acc w ->
      step Kd Σ pr γ (LDivert n) = if target_is Kd Σ pr γ n w then None else Some (set_life Σ γ n f (Unloading Σ acc w None)).
    Proof. intros Hn Hl; cbn [Calculus.step]; rewrite Hn, Hl; reflexivity. Qed.

    Lemma step_divert_none (γ : St) n f :
      fibers γ n = Some f -> (forall P acc w, life f <> Loading Σ P acc w) -> step Kd Σ pr γ (LDivert n) = None.
    Proof.
      intros Hn Hl; cbn [Calculus.step]; rewrite Hn.
      destruct (life f) eqn:E; try reflexivity; exfalso; eapply Hl; reflexivity.
    Qed.

    Lemma step_leave (γ : St) n f acc w :
      fibers γ n = Some f -> life f = Active Σ acc w ->
      step Kd Σ pr γ (LLeave n) = if target_is Kd Σ pr γ n w then None else Some (set_life Σ γ n f (Unloading Σ acc w None)).
    Proof. intros Hn Hl; cbn [Calculus.step]; rewrite Hn, Hl; reflexivity. Qed.

    Lemma step_leave_none (γ : St) n f :
      fibers γ n = Some f -> (forall acc w, life f <> Active Σ acc w) -> step Kd Σ pr γ (LLeave n) = None.
    Proof.
      intros Hn Hl; cbn [Calculus.step]; rewrite Hn.
      destruct (life f) eqn:E; try reflexivity; exfalso; eapply Hl; reflexivity.
    Qed.

    Lemma step_react (γ : St) n f acc w i :
      fibers γ n = Some f -> life f = Active Σ acc w ->
      step Kd Σ pr γ (OReact n i) =
      match nth_error (reacts Σ (pr (fcomp f))) i with
      | Some c =>
          if disposed f || conflict Kd Σ pr γ c then None
          else Some (set_life Σ (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ)
                       (Some (mkFiber Σ c (Some n) false (Inactive Σ None)))))) n f
                       (Active Σ (USpawn Σ (next γ) :: acc) w))
      | None => None
      end.
    Proof. intros Hn Hl; cbn [Calculus.step]; rewrite Hn, Hl; reflexivity. Qed.
  End Unfold.

  Lemma life_pfib f : life (pfib f) = plife (life f).
  Proof. reflexivity. Qed.

  (** *** The two calculi make the same moves where [ok] holds *)
  Theorem sim (γk : KState) (γb : BState) ℓ :
    KI γk -> BWF γb -> R γk γb -> ok γk γb ℓ = true -> ORel (kstep γk ℓ) (bstep γb ℓ).
  Proof.
    intros I Wb Rr Ok.
    pose proof (ki_wf _ _ _ _ (ki_kinv _ I)) as W; pose proof (ki_si _ _ _ _ (ki_kinv _ I)) as Si.
    assert (Hown : forall k b, binds γk k = Some b -> fibers γk (owner Σ b) <> None).
    { intros k b Hb; destruct (wf_bind _ _ _ _ W k b Hb) as (fo & Ho & _); congruence. }
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [ok] in Ok; cbn [Scoped.kstep klab].
    - (* OInsert *)
      apply andb_true_iff in Ok as [T Cf]; apply negb_true_iff in T, Cf.
      rewrite T; cbn [Calculus.step].
      rewrite (conflict_scope N_eq_dec Σ xprog γk (mkXC c [Rt (xinst Σ (xprog c))] [] [] 0)
                 (taken_free N_eq_dec Σ xprog γk _ W T)), Cf.
      exact (R_add γk γb _ Rr Hown (fresh_none _ _ _ _ W)).
    - (* ODispose *)
      cbn [Calculus.step]; rewrite (r_fib _ _ Rr n).
      destruct (fibers γk n) as [f|] eqn:Hn; cbn [option_map]; [|exact Logic.I].
      exact (R_set_fiber γk γb n f (mkFiber Σ (fcomp f) (fparent f) true (life f)) Rr Hn eq_refl).
    - (* OReset *)
      cbn [Calculus.step]; rewrite (r_fib _ _ Rr n).
      destruct (fibers γk n) as [f|] eqn:Hn; cbn [option_map]; [|exact Logic.I].
      rewrite life_pfib; destruct (life f) as [[z|]| | |] eqn:Hl; cbn [plife]; cbv beta iota; try exact Logic.I.
      exact (R_set_life γk γb n f (Inactive Σ None) Rr Hn).
    - (* LBegin *)
      pose proof (r_fib _ _ Rr n) as Fn.
      destruct (fibers γk n) as [f|] eqn:Hn; cbn [option_map] in Fn; cbv beta iota.
      2:{ cbn [Calculus.step]; rewrite Fn; exact Logic.I. }
      destruct (life f) as [[z|]|P acc w|acc w|acc w z] eqn:Hl; cbv beta iota;
        try (cbn [Calculus.step]; rewrite Fn, life_pfib, Hl; cbn [plife]; exact Logic.I).
      assert (Hlb : life (pfib f) = Inactive Σ None) by (rewrite life_pfib, Hl; reflexivity).
      rewrite (step_begin N_eq_dec bprog γb n (pfib f) Fn Hlb).
      destruct (fparent f) as [q|] eqn:Hp.
      + destruct (fresh γk f) eqn:Fr.
        * rewrite (step_begin kdec prog' γk n f Hn Hl).
          rewrite (target_fresh γk γb n f I Rr Hn Fr).
          destruct (target Σ prog' γk n) as [t|]; cbn [option_map ORel]; [|exact Logic.I].
          pose proof (R_set_life γk γb n f (Loading Σ (body Σ (prog' (fcomp f))) [] t) Rr Hn) as R1.
          cbn [plife map Scoped.prog' body] in R1; rewrite unlift_lift in R1; exact R1.
        * destruct (target Σ bprog γb n) as [tb|] eqn:Ht; cbn [option_map ORel]; [|exact Logic.I].
          rewrite (child_begin γk γb n f q tb I Rr Hn Hp Ht) in Fr; discriminate.
      + destruct (all_selected N_eq_dec Σ xprog γk (base (fcomp f))) eqn:A.
        * assert (P0 : Pre γk (recomp N_eq_dec Σ xprog γk n f)) by (right; left; exists n, f; auto).
          pose proof (R_pre γk _ γb Rr P0) as R0; pose proof (ki_pre γk _ I P0) as I0.
          assert (H0 : fibers (recomp N_eq_dec Σ xprog γk n f) n =
                       Some (mkFiber Σ (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f))
                               (choose γk (base (fcomp f))) (tick (fcomp f))) (fparent f) (disposed f) (life f))).
          { unfold Scoped.recomp; cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity. }
          assert (Fr0 : fresh (recomp N_eq_dec Σ xprog γk n f)
                          (mkFiber Σ (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f))
                             (choose γk (base (fcomp f))) (tick (fcomp f))) (fparent f) (disposed f) (life f)) = true).
          { unfold Scoped.fresh; cbn [Calculus.comp base sel].
            rewrite (all_selected_pre γk _ _ P0), A, (choose_pre γk _ _ P0); cbn [andb].
            destruct (list_eq_dec _ _ _) as [_|Q]; [reflexivity | contradiction Q; reflexivity]. }
          rewrite (step_begin kdec prog' _ n _ H0 Hl).
          rewrite (target_fresh _ γb n _ I0 R0 H0 Fr0).
          destruct (target Σ prog' (recomp N_eq_dec Σ xprog γk n f) n) as [t|]; cbn [option_map ORel]; [|exact Logic.I].
          pose proof (R_set_life _ γb n _ (Loading Σ (body Σ (prog' (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f))
                               (choose γk (base (fcomp f))) (tick (fcomp f))))) [] t) R0 H0) as R1.
          cbn [plife map Scoped.prog' body base] in R1; rewrite unlift_lift in R1; exact R1.
        * rewrite (not_all_selected γk γb n f I Rr Hn A); exact Logic.I.
    - (* LStep *)
      apply andb_true_iff in Ok as [Sc Dp]; apply negb_true_iff in Sc, Dp.
      pose proof (r_fib _ _ Rr n) as Fn.
      destruct (fibers γk n) as [f|] eqn:Hn; cbn [option_map] in Fn; cbv beta iota.
      2:{ cbn [Calculus.step]; rewrite Fn; exact Logic.I. }
      assert (Dp' : displacedb γb (pview (view_of Σ (life f))) = false).
      { unfold displaced in Dp; rewrite Fn, life_pfib, plife_view in Dp; exact Dp. }
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl.
      2:{ assert (Fr : fresh γk f = true).
          { rewrite (fresh_iff γk γb n f I Rr Hn ltac:(rewrite Hl; reflexivity)), Hl, Dp'; reflexivity. }
          rewrite Fr, (step_lstep kdec prog' γk n f P acc w Hn Hl).
          rewrite (step_lstep N_eq_dec bprog γb n (pfib f) (unlift P) (map pundo acc) (pview w) Fn
                     ltac:(rewrite life_pfib, Hl; reflexivity)).
          rewrite (may_step_rel γk γb n f P acc w I Rr Hn Hl Fr).
          destruct (may_step kdec Σ prog' γk n P w); cbn [ORel]; [|exact Logic.I].
          apply (load_sim γk γb n f P acc w I Wb Rr Hn Hl).
          intros x Q ->; unfold spawn_conflict in Sc; rewrite Fn, life_pfib, Hl in Sc; exact Sc. }
      all: assert (NL : forall P acc w, life f <> Loading Σ P acc w) by (intros P' acc' w' E; rewrite Hl in E; discriminate).
      all: assert (NLb : forall P acc w, life (pfib f) <> Loading Σ P acc w)
             by (intros P' acc' w' E; rewrite life_pfib, Hl in E; discriminate).
      all: rewrite (step_lstep_none N_eq_dec bprog γb n (pfib f) Fn NLb).
      all: destruct (fresh γk f); [rewrite (step_lstep_none kdec prog' γk n f Hn NL)|]; exact Logic.I.
    - (* LDivert *)
      pose proof (r_fib _ _ Rr n) as Fn.
      destruct (fibers γk n) as [f|] eqn:Hn; cbn [option_map] in Fn; cbv beta iota.
      2:{ cbn [Calculus.step]; rewrite Fn; exact Logic.I. }
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl.
      2:{ assert (Hi : is_installed Σ (life f) = true) by (rewrite Hl; reflexivity).
          rewrite (step_divert N_eq_dec bprog γb n (pfib f) (unlift P) (map pundo acc) (pview w) Fn
                     ltac:(rewrite life_pfib, Hl; reflexivity)).
          destruct (fresh γk f) eqn:Fr.
          - rewrite (step_divert kdec prog' γk n f P acc w Hn Hl).
            pose proof (target_is_rel γk γb n f W Hn Hi (target_fresh γk γb n f I Rr Hn Fr)) as E.
            rewrite Hl in E; cbn [view_of] in E; rewrite E.
            destruct (target_is kdec Σ prog' γk n w); cbn [ORel]; [exact Logic.I | exact (R_set_life γk γb n f _ Rr Hn)].
          - cbv beta iota.
            pose proof (stale_target γk γb n f I Rr Hn Hi Fr) as E; rewrite Hl in E; cbn [view_of] in E; rewrite E.
            exact (R_set_life γk γb n f _ Rr Hn). }
      all: assert (NL : forall P acc w, life f <> Loading Σ P acc w) by (intros P' acc' w' E; rewrite Hl in E; discriminate).
      all: assert (NLb : forall P acc w, life (pfib f) <> Loading Σ P acc w)
             by (intros P' acc' w' E; rewrite life_pfib, Hl in E; discriminate).
      all: rewrite (step_divert_none N_eq_dec bprog γb n (pfib f) Fn NLb).
      all: destruct (fresh γk f); [rewrite (step_divert_none kdec prog' γk n f Hn NL)|cbv beta iota]; exact Logic.I.
    - (* LLeave *)
      pose proof (r_fib _ _ Rr n) as Fn.
      destruct (fibers γk n) as [f|] eqn:Hn; cbn [option_map] in Fn; cbv beta iota.
      2:{ cbn [Calculus.step]; rewrite Fn; exact Logic.I. }
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl.
      3:{ assert (Hi : is_installed Σ (life f) = true) by (rewrite Hl; reflexivity).
          rewrite (step_leave N_eq_dec bprog γb n (pfib f) (map pundo acc) (pview w) Fn
                     ltac:(rewrite life_pfib, Hl; reflexivity)).
          destruct (fresh γk f) eqn:Fr.
          - rewrite (step_leave kdec prog' γk n f acc w Hn Hl).
            pose proof (target_is_rel γk γb n f W Hn Hi (target_fresh γk γb n f I Rr Hn Fr)) as E.
            rewrite Hl in E; cbn [view_of] in E; rewrite E.
            destruct (target_is kdec Σ prog' γk n w); cbn [ORel]; [exact Logic.I | exact (R_set_life γk γb n f _ Rr Hn)].
          - cbv beta iota.
            pose proof (stale_target γk γb n f I Rr Hn Hi Fr) as E; rewrite Hl in E; cbn [view_of] in E; rewrite E.
            exact (R_set_life γk γb n f _ Rr Hn). }
      all: assert (NL : forall acc w, life f <> Active Σ acc w) by (intros acc' w' E; rewrite Hl in E; discriminate).
      all: assert (NLb : forall acc w, life (pfib f) <> Active Σ acc w)
             by (intros acc' w' E; rewrite life_pfib, Hl in E; discriminate).
      all: rewrite (step_leave_none N_eq_dec bprog γb n (pfib f) Fn NLb).
      all: destruct (fresh γk f); [rewrite (step_leave_none kdec prog' γk n f Hn NL)|cbv beta iota]; exact Logic.I.
    - (* LUndo *)
      cbn [Calculus.step]; rewrite (r_fib _ _ Rr n).
      destruct (fibers γk n) as [f|] eqn:Hn; cbn [option_map]; [|exact Logic.I].
      rewrite life_pfib; destruct (life f) as [z|P acc w|acc w|[|u acc] w z] eqn:Hl; cbn [plife map]; cbv beta iota;
        try exact Logic.I.
      change (pundo u :: map pundo acc) with (map pundo (u :: acc)); rewrite <- (held_R γk γb n (u :: acc) Rr).
      destruct (held Σ γk n (u :: acc)); [exact Logic.I | exact (undo_sim γk γb n f u acc w z I Rr Hn Hl)].
    - (* LRetireChild *)
      cbn [Calculus.step]; rewrite (r_fib _ _ Rr n).
      destruct (fibers γk n) as [f|] eqn:Hn; cbn [option_map]; [|exact Logic.I].
      rewrite life_pfib; destruct (life f) as [z|P acc w|acc w|[|[k p t g|k p|m] acc] w z] eqn:Hl;
        cbn [plife map pundo]; cbv beta iota; try exact Logic.I.
      rewrite (r_fib _ _ Rr m); destruct (fibers γk m) as [g|] eqn:Hm; cbn [option_map]; [|exact Logic.I].
      change (USpawn Σ m :: map pundo acc) with (map pundo (USpawn Σ m :: acc)).
      rewrite <- (held_R γk γb n (USpawn Σ m :: acc) Rr).
      change (disposed (pfib g)) with (disposed g).
      destruct (held Σ γk n (USpawn Σ m :: acc) || disposed g); [exact Logic.I|].
      exact (R_set_fiber γk γb m g (mkFiber Σ (fcomp g) (fparent g) true (life g)) Rr Hm eq_refl).
    - (* LUnloaded *)
      cbn [Calculus.step]; rewrite (r_fib _ _ Rr n).
      destruct (fibers γk n) as [f|] eqn:Hn; cbn [option_map]; [|exact Logic.I].
      rewrite life_pfib; destruct (life f) as [z|P acc w|acc w|[|u acc] w z] eqn:Hl; cbn [plife map]; cbv beta iota;
        try exact Logic.I.
      exact (R_set_life γk γb n f (Inactive Σ z) Rr Hn).
    - (* LRemove *)
      cbn [Calculus.step]; rewrite (r_fib _ _ Rr n).
      destruct (fibers γk n) as [f|] eqn:Hn; cbn [option_map]; [|exact Logic.I].
      rewrite life_pfib; destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; cbn [plife]; cbv beta iota;
        try exact Logic.I.
      change (disposed (pfib f)) with (disposed f); rewrite <- (has_child_R γk γb n Rr).
      destruct (disposed f && negb (has_child Σ γk n)); [|exact Logic.I].
      apply R_remove; [exact Rr|]; intros k b Hb E.
      destruct (wf_bind _ _ _ _ W k b Hb) as (fo & Ho & Io & _).
      rewrite E, Hn in Ho; injection Ho as <-; rewrite Hl in Io; discriminate.
    - (* OReact *)
      apply negb_true_iff in Ok.
      pose proof (r_fib _ _ Rr n) as Fn.
      destruct (fibers γk n) as [f|] eqn:Hn; cbn [option_map] in Fn; cbv beta iota.
      2:{ cbn [Calculus.step]; rewrite Fn; exact Logic.I. }
      destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; cbv beta iota;
        try (cbn [Calculus.step]; rewrite Fn, life_pfib, Hl; cbn [plife]; exact Logic.I).
      assert (P0 : Pre γk (retick Σ γk n f)) by (right; right; exists n, f, acc, w; auto).
      pose proof (R_pre γk _ γb Rr P0) as R0.
      pose proof (wf_retick N_eq_dec Σ xprog γk n f W Hn) as W0.
      assert (H0 : fibers (retick Σ γk n f) n =
                   Some (mkFiber Σ (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f)) (sel (fcomp f)) (next γk))
                                 (fparent f) (disposed f) (life f))).
      { unfold Scoped.retick; cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity. }
      rewrite (step_react kdec prog' _ n _ acc w i H0 Hl).
      rewrite (step_react N_eq_dec bprog γb n (pfib f) (map pundo acc) (pview w) i Fn
                 ltac:(rewrite life_pfib, Hl; reflexivity)).
      change (reacts Σ (prog' (fcomp (mkFiber Σ (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f)) (sel (fcomp f)) (next γk))
                                 (fparent f) (disposed f) (life f)))))
        with (handlers N_eq_dec Σ xprog (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f)) (sel (fcomp f)) (next γk))
                       0 (xreacts Σ (xprog (base (fcomp f))))).
      rewrite nth_handlers.
      change (reacts Σ (bprog (fcomp (pfib f)))) with (xreacts Σ (xprog (base (fcomp f)))).
      assert (Cb : forall c, nth_error (xreacts Σ (xprog (base (fcomp f)))) i = Some c ->
                             conflict N_eq_dec Σ bprog γb c = false).
      { intros c Hc; unfold react_conflict in Ok; rewrite Fn in Ok.
        change (reacts Σ (bprog (fcomp (pfib f)))) with (xreacts Σ (xprog (base (fcomp f)))) in Ok.
        rewrite Hc in Ok; exact Ok. }
      destruct (nth_error (xreacts Σ (xprog (base (fcomp f)))) i) as [c|] eqn:Hc; cbn [option_map]; [|exact Logic.I].
      cbn [tick Calculus.disposed]; rewrite (react_noconf γk n f c i Si Hn), (Cb c eq_refl).
      change (disposed (pfib f)) with (disposed f); cbn [Calculus.disposed].
      rewrite !orb_false_r; destruct (disposed f) eqn:Hd; [exact Logic.I|].
      assert (Ho0 : forall k b, binds (retick Σ γk n f) k = Some b -> fibers (retick Σ γk n f) (owner Σ b) <> None).
      { intros k b Hb; destruct (wf_bind _ _ _ _ W0 k b Hb) as (fo & Ho & _); congruence. }
      pose proof (R_add _ γb (mkFiber Σ (child N_eq_dec Σ xprog (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f)) (sel (fcomp f)) (next γk))
                                   (Re (0 + i) (next γk)) c) (Some n) false (Inactive Σ None))
                    R0 Ho0 (fresh_none _ _ _ _ W0)) as R1.
      assert (Hn1 : fibers (bump Σ (with_fibers Σ (retick Σ γk n f) (fupd Σ (fibers (retick Σ γk n f)) (next (retick Σ γk n f))
                      (Some (mkFiber Σ (child N_eq_dec Σ xprog (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f)) (sel (fcomp f)) (next γk))
                                   (Re (0 + i) (next γk)) c) (Some n) false (Inactive Σ None)))))) n =
                    Some (mkFiber Σ (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f)) (sel (fcomp f)) (next γk))
                                 (fparent f) false (life f))).
      { cbn [Calculus.fibers bump with_fibers]; unfold fupd.
        destruct (Nat.eqb_spec n (next (retick Σ γk n f))) as [E|]; [|exact H0].
        exfalso; pose proof (fresh_none _ _ _ _ W0) as Fz; rewrite <- E, H0 in Fz; discriminate. }
      pose proof (R_set_life _ _ n _ (Active Σ (USpawn Σ (next (retick Σ γk n f)) :: acc) w) R1 Hn1) as R2.
      cbn [plife map pundo] in R2; unfold pfib in R2 |- *; cbn [Calculus.disposed Calculus.comp Calculus.parent Calculus.life base Scoped.child plife map pundo] in R2 |- *; rewrite ?Hl, ?Hd in R2 |- *.
      rewrite (r_next _ _ Rr) in R2 |- *; try rewrite Hd; exact R2.
    - (* ORestart *)
      cbn [Calculus.step]; rewrite (r_fib _ _ Rr n).
      destruct (fibers γk n) as [f|] eqn:Hn; cbn [option_map]; [|exact Logic.I].
      change (disposed (pfib f)) with (disposed f); destruct (disposed f); [exact Logic.I|].
      rewrite life_pfib; destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; cbn [plife]; cbv beta iota;
        try exact Logic.I; exact (R_set_life γk γb n f (Unloading Σ acc w None) Rr Hn).
  Qed.

  (** *** From the extension to the core *)

  (** A step that adds a fiber of base component [c] and keeps every other
      fiber leaves [c] in conflict with nobody when the result is disjoint. *)
  Lemma disj_new (γk γk' : KState) (γb : BState) fnew :
    R γk γb -> Disj γk' -> fibers γk (next γk) = None -> fibers γk' (next γk) = Some fnew ->
    (forall m fm, fibers γk m = Some fm -> exists fm', fibers γk' m = Some fm' /\ base (fcomp fm') = base (fcomp fm)) ->
    conflict N_eq_dec Σ bprog γb (base (fcomp fnew)) = false.
  Proof.
    intros Rr D Hf Hnew Hkeep.
    apply not_true_iff_false; intros Cf; unfold conflict in Cf.
    apply existsb_exists in Cf as (m & _ & Cm).
    rewrite (r_fib _ _ Rr m) in Cm; destruct (fibers γk m) as [fm|] eqn:Hm; [|discriminate].
    cbn [option_map pfib Calculus.comp bprog provs] in Cm.
    destruct (Hkeep m fm Hm) as (fm' & Hm' & Eb).
    assert (Ne : next γk <> m) by (intros E; rewrite E, Hm in Hf; discriminate).
    pose proof (D _ _ _ _ Ne Hnew Hm') as Dz; rewrite Eb in Dz; congruence.
  Qed.

  Lemma keep_add (γ : KState) nf m fm :
    fibers γ (next γ) = None -> fibers γ m = Some fm ->
    fibers (bump Σ (with_fibers Σ γ (fupd Σ (fibers γ) (next γ) (Some nf)))) m = Some fm.
  Proof.
    intros Hf Hm; cbn; unfold fupd; destruct (Nat.eqb_spec m (next γ)) as [E|]; [|exact Hm].
    rewrite E, Hf in Hm; discriminate.
  Qed.

  Lemma keep_life (γ : KState) n f l m fm :
    fibers γ n = Some f -> fibers γ m = Some fm ->
    exists fm', fibers (set_life Σ γ n f l) m = Some fm' /\ base (fcomp fm') = base (fcomp fm).
  Proof.
    intros Hn Hm; rewrite fibers_set_life; destruct (Nat.eqb_spec m n) as [->|].
    - rewrite Hn in Hm; injection Hm as <-; eexists; split; reflexivity.
    - exists fm; auto.
  Qed.

  (** Every extended step that keeps [Disj] is a core step of the base
      table, and the correspondence is kept. *)
  Theorem sim_back (γk γk' : KState) (γb : BState) ℓ :
    KI γk -> BWF γb -> R γk γb -> kstep γk ℓ = Some γk' -> Disj γk' ->
    exists γb', bstep γb ℓ = Some γb' /\ R γk' γb'.
  Proof.
    intros I Wb Rr H D.
    pose proof (ki_wf _ _ _ _ (ki_kinv _ I)) as W; pose proof (ki_si _ _ _ _ (ki_kinv _ I)) as Si.
    pose proof (fresh_none _ _ _ _ W) as Hfr.
    assert (Ok : ok γk γb ℓ = true).
    { destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [ok]; try reflexivity.
      - (* OInsert *)
        cbn [Scoped.kstep] in H; destruct (taken Σ γk (xinst Σ (xprog c))) eqn:T; [discriminate|].
        cbn [klab Calculus.step] in H; destruct (conflict kdec Σ prog' γk _); [discriminate|].
        injection H as <-; cbn [negb andb]; apply negb_true_iff.
        refine (disj_new γk _ γb (mkFiber Σ (mkXC c [Rt (xinst Σ (xprog c))] [] [] 0) None false (Inactive Σ None))
                  Rr D Hfr _ _).
        + cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity.
        + intros m fm Hm; exists fm; split; [exact (keep_add γk _ m fm Hfr Hm) | reflexivity].
      - (* LStep *)
        cbn [Scoped.kstep] in H; destruct (fibers γk n) as [f|] eqn:Hn; [|discriminate].
        destruct (fresh γk f) eqn:Fr; [|discriminate].
        destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl;
          try (rewrite (step_lstep_none kdec prog' γk n f Hn ltac:(intros P' acc' w' E; rewrite Hl in E; discriminate)) in H;
               discriminate).
        pose proof (r_fib _ _ Rr n) as Fn; rewrite Hn in Fn; cbn [option_map] in Fn.
        apply andb_true_iff; split; apply negb_true_iff.
        + unfold spawn_conflict; rewrite Fn, life_pfib, Hl; cbn [plife].
          destruct P as [| | | |x Q]; cbn [unlift]; try reflexivity.
          rewrite (step_lstep kdec prog' γk n f _ acc w Hn Hl) in H; cbn [may_step] in H.
          unfold load_step in H; rewrite (spawn_noconf γk n f x Q acc w Si Hn Hl) in H.
          injection H as <-.
          refine (disj_new γk _ γb (mkFiber Σ x (Some n) false (Inactive Σ None)) Rr D Hfr _ _).
          * rewrite fibers_set_life; destruct (Nat.eqb_spec (next γk) n) as [E|].
            -- rewrite <- E, Hfr in Hn; discriminate.
            -- cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity.
          * intros m fm Hm.
            exact (keep_life _ n f _ m fm (keep_add γk _ n f Hfr Hn) (keep_add γk _ m fm Hfr Hm)).
        + unfold displaced; rewrite Fn, life_pfib, plife_view.
          rewrite (fresh_iff γk γb n f I Rr Hn ltac:(rewrite Hl; reflexivity)) in Fr.
          apply negb_true_iff in Fr; exact Fr.
      - (* OReact *)
        cbn [Scoped.kstep] in H; destruct (fibers γk n) as [f|] eqn:Hn; [|discriminate].
        destruct (life f) as [z|P acc w|acc w|acc w z] eqn:Hl; try discriminate.
        pose proof (r_fib _ _ Rr n) as Fn; rewrite Hn in Fn; cbn [option_map] in Fn.
        assert (H0 : fibers (retick Σ γk n f) n =
                     Some (mkFiber Σ (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f)) (sel (fcomp f)) (next γk))
                                   (fparent f) (disposed f) (life f))).
        { unfold Scoped.retick; cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity. }
        rewrite (step_react kdec prog' _ n _ acc w i H0 Hl) in H.
        change (reacts Σ (prog' (fcomp (mkFiber Σ (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f)) (sel (fcomp f)) (next γk))
                                   (fparent f) (disposed f) (life f)))))
          with (handlers N_eq_dec Σ xprog (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f)) (sel (fcomp f)) (next γk))
                         0 (xreacts Σ (xprog (base (fcomp f))))) in H.
        rewrite nth_handlers in H.
        unfold react_conflict; rewrite Fn.
        change (reacts Σ (bprog (fcomp (pfib f)))) with (xreacts Σ (xprog (base (fcomp f)))).
        destruct (nth_error (xreacts Σ (xprog (base (fcomp f)))) i) as [c|] eqn:Hc; [|reflexivity].
        cbn [option_map] in H.
        destruct (_ || _) in H; [discriminate|]; injection H as <-.
        apply negb_true_iff.
        pose proof (wf_retick N_eq_dec Σ xprog γk n f W Hn) as W0.
        pose proof (fresh_none _ _ _ _ W0) as Hfr0.
        refine (disj_new γk _ γb (mkFiber Σ (child N_eq_dec Σ xprog (mkXC (base (fcomp f)) (scope (fcomp f)) (env (fcomp f)) (sel (fcomp f)) (next γk))
                                     (Re (0 + i) (next γk)) c) (Some n) false (Inactive Σ None)) Rr D Hfr _ _).
        + rewrite fibers_set_life; destruct (Nat.eqb_spec (next γk) n) as [E|].
          * rewrite <- E, Hfr in Hn; discriminate.
          * cbn; unfold fupd; rewrite Nat.eqb_refl; reflexivity.
        + intros m fm Hm; rewrite fibers_set_life.
          destruct (Nat.eqb_spec m n) as [->|Ne].
          * rewrite Hn in Hm; injection Hm as <-; eexists; split; reflexivity.
          * exists fm; split; [|reflexivity].
            unfold Scoped.retick; cbn [Calculus.fibers Calculus.next bump with_fibers set_fiber]; unfold fupd.
            destruct (Nat.eqb_spec m (next γk)) as [E|]; [rewrite E, Hfr in Hm; discriminate|].
            destruct (Nat.eqb_spec m n); [contradiction | exact Hm]. }
    pose proof (sim γk γb ℓ I Wb Rr Ok) as Sm; rewrite H in Sm.
    destruct (bstep γb ℓ) as [γb'|]; [exists γb'; auto | contradiction].
  Qed.

  (** *** From the core to the extension *)

  (** A root of the core state with this instance id. *)
  Definition btaken (γb : BState) (i : nat) : bool :=
    existsb (fun m => match fibers γb m with
                      | Some f => match fparent f with
                                  | None => Nat.eqb (xinst Σ (xprog (fcomp f))) i
                                  | Some _ => false
                                  end
                      | None => false
                      end) (names Σ γb).

  Lemma taken_btaken (γk : KState) (γb : BState) i :
    KI γk -> R γk γb -> taken Σ γk i = btaken γb i.
  Proof.
    intros I Rr; unfold taken, btaken, names; rewrite (r_next _ _ Rr).
    apply existsb_ext'; intros m; rewrite (r_fib _ _ Rr m).
    destruct (fibers γk m) as [f|] eqn:Hm; cbn [option_map pfib Calculus.parent Calculus.comp]; [|reflexivity].
    destruct (ki_roots _ I m f Hm) as [Hr Hc].
    destruct (fparent f) as [q|] eqn:Hp.
    - destruct (Hc ltac:(discriminate)) as (g & g' & s & Es); rewrite Es.
      unfold scope_eqb; destruct (scope_eq_dec _ _) as [E|]; [discriminate | reflexivity].
    - rewrite (Hr eq_refl); unfold scope_eqb.
      destruct (scope_eq_dec _ _) as [E|Ne].
      + injection E as ->; rewrite Nat.eqb_refl; reflexivity.
      + symmetry; apply Nat.eqb_neq; intros E'; apply Ne; rewrite E'; reflexivity.
  Qed.

  (** The core moves the extension does not make: inserting under an
      instance id in use, a conflict at a spawn, an inertial step of a
      displaced fiber. (A conflict at insertion or at a reaction stops the
      core itself.) *)
  Definition excluded (γb : BState) (ℓ : @Label C) : bool :=
    match ℓ with
    | OInsert c => btaken γb (xinst Σ (xprog c))
    | LStep n => spawn_conflict γb n || displaced γb n
    | _ => false
    end.

  Theorem sim_fwd (γk : KState) (γb γb' : BState) ℓ :
    KI γk -> BWF γb -> R γk γb -> bstep γb ℓ = Some γb' -> excluded γb ℓ = false ->
    exists γk', kstep γk ℓ = Some γk' /\ R γk' γb'.
  Proof.
    intros I Wb Rr H Ex.
    assert (Ok : ok γk γb ℓ = true).
    { destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [ok excluded] in Ex |- *; try reflexivity.
      - rewrite (taken_btaken γk γb _ I Rr), Ex; cbn [negb andb].
        cbn [Calculus.step] in H; destruct (conflict N_eq_dec Σ bprog γb c); [discriminate | reflexivity].
      - apply orb_false_iff in Ex as [E1 E2]; rewrite E1, E2; reflexivity.
      - apply negb_true_iff; unfold react_conflict.
        cbn [Calculus.step] in H; destruct (fibers γb n) as [fb|]; [|discriminate].
        destruct (life fb); try discriminate.
        destruct (nth_error (reacts Σ (bprog (fcomp fb))) i) as [c|]; [|reflexivity].
        destruct (conflict N_eq_dec Σ bprog γb c); [rewrite orb_true_r in H; discriminate | reflexivity]. }
    pose proof (sim γk γb ℓ I Wb Rr Ok) as Sm; rewrite H in Sm.
    destruct (kstep γk ℓ) as [γk'|]; [exists γk'; auto | contradiction].
  Qed.

  (** *** Along executions *)

  (** Present fibers provide disjoint names, as a test. *)
  Definition disjb (γ : KState) : bool :=
    forallb (fun m => forallb (fun m' =>
      Nat.eqb m m' ||
      match fibers γ m, fibers γ m' with
      | Some fm, Some fm' => negb (overlaps N_eq_dec (xprovs (base (fcomp fm))) (xprovs (base (fcomp fm'))))
      | _, _ => true
      end) (names Σ γ)) (names Σ γ).

  Lemma disjb_spec (γ : KState) : KWF γ -> disjb γ = true -> Disj γ.
  Proof.
    intros W Db m m' fm fm' Ne Hm Hm'.
    unfold disjb in Db; rewrite forallb_forall in Db.
    specialize (Db m (in_names _ _ _ _ m fm W Hm)); rewrite forallb_forall in Db.
    specialize (Db m' (in_names _ _ _ _ m' fm' W Hm')).
    rewrite Hm, Hm' in Db; destruct (Nat.eqb_spec m m'); [contradiction|].
    cbn [orb] in Db; apply negb_true_iff in Db; exact Db.
  Qed.

  (** An extended execution that keeps every state disjoint. *)
  Fixpoint krund (γ : KState) (ls : list (@Label C)) : option KState :=
    match ls with
    | [] => Some γ
    | ℓ :: ls' => match kstep γ ℓ with
                  | Some γ' => if disjb γ' then krund γ' ls' else None
                  | None => None
                  end
    end.

  (** A core execution that avoids the three excluded moves. *)
  Fixpoint brunx (γ : BState) (ls : list (@Label C)) : option BState :=
    match ls with
    | [] => Some γ
    | ℓ :: ls' => if excluded γ ℓ then None
                  else match bstep γ ℓ with
                       | Some γ' => brunx γ' ls'
                       | None => None
                       end
    end.

  (** Every disjoint extended execution is a core execution of the base
      table, under the correspondence; so the core theorems hold of it. *)
  Theorem back_run (γk : KState) ls :
    krund (@init Key Σ XC) ls = Some γk ->
    exists γb, run_labels N_eq_dec Σ bprog (@init N Σ C) ls = Some γb /\ R γk γb.
  Proof.
    assert (G : forall γk0 (γb0 : BState), KI γk0 -> BWF γb0 -> R γk0 γb0 -> krund γk0 ls = Some γk ->
                exists γb, run_labels N_eq_dec Σ bprog γb0 ls = Some γb /\ R γk γb).
    { induction ls as [|ℓ ls IH]; cbn; intros γk0 γb0 I0 W0 R0 H.
      - injection H as <-; exists γb0; auto.
      - destruct (kstep γk0 ℓ) as [γk1|] eqn:Hs; [|discriminate].
        destruct (disjb γk1) eqn:Db; [|discriminate].
        pose proof (ki_step γk0 γk1 ℓ I0 Hs) as I1.
        pose proof (disjb_spec γk1 (ki_wf _ _ _ _ (ki_kinv _ I1)) Db) as D1.
        destruct (sim_back γk0 γk1 γb0 ℓ I0 W0 R0 Hs D1) as (γb1 & Hb & R1).
        rewrite Hb.
        exact (IH γk1 γb1 I1 (preservation N_eq_dec Σ bprog γb0 γb1 ℓ W0 Hb) R1 H). }
    intros H; exact (G _ _ ki_init (wf_init N_eq_dec Σ bprog) R_init H).
  Qed.

  (** Every core execution of the base table that avoids the excluded
      moves is an extended execution, under the correspondence. *)
  Theorem fwd_run (γb : BState) ls :
    brunx (@init N Σ C) ls = Some γb ->
    exists γk, krun N_eq_dec Σ xprog (@init Key Σ XC) ls = Some γk /\ R γk γb.
  Proof.
    assert (G : forall γk0 (γb0 : BState), KI γk0 -> BWF γb0 -> R γk0 γb0 -> brunx γb0 ls = Some γb ->
                exists γk, krun N_eq_dec Σ xprog γk0 ls = Some γk /\ R γk γb).
    { induction ls as [|ℓ ls IH]; cbn; intros γk0 γb0 I0 W0 R0 H.
      - injection H as <-; exists γk0; auto.
      - destruct (excluded γb0 ℓ) eqn:Ex; [discriminate|].
        destruct (bstep γb0 ℓ) as [γb1|] eqn:Hb; [|discriminate].
        destruct (sim_fwd γk0 γb0 γb1 ℓ I0 W0 R0 Hb Ex) as (γk1 & Hs & R1).
        rewrite Hs.
        exact (IH γk1 γb1 (ki_step γk0 γk1 ℓ I0 Hs) (preservation N_eq_dec Σ bprog γb0 γb1 ℓ W0 Hb) R1 H). }
    intros H; exact (G _ _ ki_init (wf_init N_eq_dec Σ bprog) R_init H).
  Qed.
End Cons.
