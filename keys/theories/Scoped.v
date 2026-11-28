(** * Hygienic keys: private by default, exported explicitly (keys/DESIGN.md)

    A component provides names. A private name is seen only by the
    provider's subtree. An exported name is resolved like a contribution
    key: among the fibers that export it and whose key is visible (bound,
    provider Active), the one with the unique highest priority wins. With
    none, or with a tie, the name is unresolved; a tie is a conflict, a
    value and not a failure.

    The extension is not a new calculus. Runtime keys are instance scoped:
    a key is a pair [(s, x)], [s] the provider's scope and [x] a name. A
    scope is a canonical path: a root inserted under instance id [i] (given
    by the orchestrator) has scope [[Rt i]], the [j]-th spawn in the body of a fiber of scope [s]
    has scope [Sp j :: s], and a firing of its [i]-th reaction handler that
    creates the fiber named [t] has scope [Re i t :: s]. A fiber's component
    is a record [XC]: the base component, its scope, the environment of
    private names its ancestors provide ([env], nearest first), the
    selection of its exported dependencies ([sel]) and a stamp ([tick]):
    the name the next reaction child will get, set just before the core
    [O-React] fires. The
    core table [prog'] reads such a record as a component over keys
    [Scope * N]:
    - [PProvide x] writes [(scope, x)], so two instances never meet;
    - a dependency [Local x] is [(s, x)] for the nearest ancestor scope [s]
      in [env] that privately provides [x], decided when the fiber is
      spawned;
    - a dependency [Global x] is [(sel x, x)], [sel] chosen at [X-Begin].

    Then every extended step is
    - a core step of [prog'], or
    - [X-Begin]: for an Inactive root, choosing the selection when every
      exported dependency is resolved, then the core [L-Begin]. A child
      never chooses: it inherits its parent's selection when spawned
      ([inherit]) and begins as in the core once that is current; or
    - a reload because a selection changed (another candidate won, or a
      tie appeared): the core [O-Restart]; or
    - [X-React]: stamping an Active fiber, then the core [O-React]
    ([kstep_core]). Choosing a selection keeps the core invariant [WF]
    ([wf_recomp]), so the core [preservation] gives safety for every
    extended execution ([kwf_reachable]). Two different scopes never share
    a key ([conflict_scope]), which is what later removes the conflict
    checks of the core. With no exported dependency anywhere the extended
    step is the core step ([kstep_conservative]).

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service Calculus Preservation.
Import ListNotations.

Section Scoped.
  Context {N : Type} (N_eq_dec : forall x y : N, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type}.

  (** ** Scopes and keys *)
  Inductive Seg : Type :=
  | Rt (n : nat)     (* inserted by the orchestrator as name n *)
  | Sp (j : nat)     (* the j-th spawn of the parent's body *)
  | Re (i t : nat).  (* the parent's i-th reaction handler, fired as name t *)

  Definition Scope : Type := list Seg.

  Definition seg_eq_dec : forall a b : Seg, {a = b} + {a <> b}.
  Proof. decide equality; apply Nat.eq_dec. Defined.

  Definition scope_eq_dec : forall a b : Scope, {a = b} + {a <> b} := list_eq_dec seg_eq_dec.

  Definition Key : Type := (Scope * N)%type.

  Definition key_eq_dec : forall a b : Key, {a = b} + {a <> b}.
  Proof. decide equality; first [apply N_eq_dec | apply scope_eq_dec]. Defined.

  Definition neqb (x y : N) : bool := if N_eq_dec x y then true else false.
  Definition nmem (x : N) (xs : list N) : bool := existsb (neqb x) xs.
  Definition scope_eqb (a b : Scope) : bool := if scope_eq_dec a b then true else false.

  (** ** Components *)
  Inductive Dep : Type :=
  | Local (x : N)     (* the nearest ancestor that privately provides x *)
  | Global (x : N).   (* the exported name x *)

  Definition dname (d : Dep) : N := match d with Local x | Global x => x end.

  Record XComponent : Type := mkX {
    xdeps : list Dep;
    xprivs : list N;                  (* provided, seen by the subtree only *)
    xexports : list N;                (* provided and exported *)
    xprio : N -> nat;                 (* priority of an exported name *)
    xbody : @Prog N Σ C;
    xreacts : list C;
    xinst : nat                       (* the instance id the orchestrator inserts it under *)
  }.

  Context (xprog : C -> XComponent).

  (** Names to scopes; the first entry for a name wins. *)
  Definition Env : Type := list (N * Scope).

  Fixpoint assoc (x : N) (e : Env) : option Scope :=
    match e with
    | [] => None
    | (y, s) :: e' => if neqb x y then Some s else assoc x e'
    end.

  (** A missing entry reads as the empty scope, which no fiber has. *)
  Definition assoc_or (x : N) (e : Env) : Scope :=
    match assoc x e with Some s => s | None => [] end.

  (** A fiber's component. *)
  Record XC : Type := mkXC {
    base : C;
    scope : Scope;
    env : Env;     (* private names of the ancestors, nearest first *)
    sel : Env;     (* the selection of the exported dependencies *)
    tick : nat     (* the name the next reaction child will get *)
  }.

  Local Notation Prog' := (@Prog Key Σ XC).
  Local Notation State := (@State Key Σ XC).
  Local Notation Fiber := (@Fiber Key Σ XC).
  Local Notation Label := (@Label XC).
  Local Notation fibers := (fibers Σ).
  Local Notation binds := (binds Σ).
  Local Notation life := (life Σ).
  Local Notation fcomp := (Calculus.comp Σ).
  Local Notation fparent := (Calculus.parent Σ).
  Local Notation disposed := (Calculus.disposed Σ).

  Definition xprovs (c : C) : list N := xprivs (xprog c) ++ xexports (xprog c).

  (** The key a dependency stands for. *)
  Definition dkey (x : XC) (d : Dep) : Key :=
    match d with
    | Local y => (assoc_or y (env x), y)
    | Global y => (assoc_or y (sel x), y)
    end.

  (** The key an operation on name [y] addresses: a dependency if one is
      declared for [y] (the core also reads dependencies first), otherwise
      the fiber's own key. *)
  Definition keyof (x : XC) (y : N) : Key :=
    match find (fun d => neqb (dname d) y) (xdeps (xprog (base x))) with
    | Some d => dkey x d
    | None => (scope x, y)
    end.

  (** The environment the fiber's children start with. *)
  Definition child_env (x : XC) : Env :=
    map (fun y => (y, scope x)) (xprivs (xprog (base x))) ++ env x.

  Fixpoint omap {A B : Type} (g : A -> option B) (l : list A) : list B :=
    match l with
    | [] => []
    | a :: l' => match g a with Some b => b :: omap g l' | None => omap g l' end
    end.

  (** The names a component depends on through the exported namespace. *)
  Definition globals (c : C) : list N :=
    omap (fun d => match d with Global y => Some y | Local _ => None end) (xdeps (xprog c)).

  (** A child takes its parent's selection for its exported dependencies
      (which its parent must declare too) and never re-chooses it. *)
  Definition inherit (x : XC) (c : C) : Env :=
    map (fun y => (y, assoc_or y (sel x))) (globals c).

  Definition child (x : XC) (s : Seg) (c : C) : XC :=
    mkXC c (s :: scope x) (child_env x) (inherit x c) 0.

  (** The body of [x] over keys; [j] counts the spawns so far, so the
      children of one body have distinct scopes. *)
  Fixpoint lift (x : XC) (j : nat) (P : @Prog N Σ C) : Prog' :=
    match P with
    | PDone => PDone
    | PFail => PFail
    | POp y a κ => POp (keyof x y) a (fun o => lift x j (κ o))
    | PProvide y st Q => PProvide (scope x, y) st (lift x j Q)
    | PSpawn c Q => PSpawn (child x (Sp j) c) (lift x (S j) Q)
    end.

  Fixpoint handlers (x : XC) (i : nat) (cs : list C) : list XC :=
    match cs with
    | [] => []
    | c :: cs' => child x (Re i (tick x)) c :: handlers x (S i) cs'
    end.

  Definition prog' (x : XC) : @Component Key Σ XC :=
    let xc := xprog (base x) in
    mkComponent (map (dkey x) (xdeps xc)) (map (pair (scope x)) (xprovs (base x)))
                (lift x 0 (xbody xc)) (handlers x 0 (xreacts xc)).

  Local Notation step := (step key_eq_dec Σ prog').
  Local Notation target := (target Σ prog').
  Local Notation WF := (WF key_eq_dec Σ prog').
  Local Notation conflict := (conflict key_eq_dec Σ prog').

  (** ** Exported names: resolution like a contribution key *)

  (** Fiber [m] is a candidate for [y]: it exports [y] and its key is
      visible. Then its scope and its priority for [y]. *)
  Definition candidate (γ : State) (y : N) (m : nat) : option (Scope * nat) :=
    match fibers γ m with
    | Some f =>
        let x := fcomp f in
        if nmem y (xexports (xprog (base x))) then
          match visible Σ γ (scope x, y) with
          | Some _ => Some (scope x, xprio (xprog (base x)) y)
          | None => None
          end
        else None
    | None => None
    end.

  Definition candidates (γ : State) (y : N) : list (Scope * nat) :=
    omap (candidate γ y) (names Σ γ).

  (** The unique candidate of highest priority; [None] when there is no
      candidate or the highest priority is tied (a conflict). *)
  Definition select (γ : State) (y : N) : option Scope :=
    let cs := candidates γ y in
    let top := fold_right (fun c m => Nat.max (snd c) m) 0 cs in
    match filter (fun c => Nat.eqb (snd c) top) cs with
    | [(s, _)] => Some s
    | _ => None
    end.

  (** A conflict, reported as a diagnostic: two candidates or more share
      the highest priority. *)
  Definition tied (γ : State) (y : N) : bool :=
    let cs := candidates γ y in
    let top := fold_right (fun c m => Nat.max (snd c) m) 0 cs in
    Nat.ltb 1 (length (filter (fun c => Nat.eqb (snd c) top) cs)).

  Definition selected (γ : State) (y : N) : bool :=
    match select γ y with Some _ => true | None => false end.

  (** Every exported dependency of [c] is resolved. *)
  Definition all_selected (γ : State) (c : C) : bool := forallb (selected γ) (globals c).

  Definition choose (γ : State) (c : C) : Env :=
    map (fun y => (y, match select γ y with Some s => s | None => [] end)) (globals c).

  Definition ns_eq_dec (a b : N * Scope) : {a = b} + {a <> b}.
  Proof. decide equality; first [apply scope_eq_dec | apply N_eq_dec]. Defined.

  (** The selection made when [f] began loading is what choosing would give
      now, and every exported dependency is resolved. *)
  Definition fresh (γ : State) (f : Fiber) : bool :=
    all_selected γ (base (fcomp f)) &&
    (if list_eq_dec ns_eq_dec (sel (fcomp f)) (choose γ (base (fcomp f))) then true else false).

  (** Choose the selection of fiber [n]. *)
  Definition recomp (γ : State) (n : nat) (f : Fiber) : State :=
    let x := fcomp f in
    set_fiber Σ γ n (mkFiber Σ (mkXC (base x) (scope x) (env x) (choose γ (base x)) (tick x))
                             (fparent f) (disposed f) (life f)).

  (** Stamp fiber [n] with the name its next reaction child will get, so
      that two firings of one handler have different scopes. *)
  Definition retick (γ : State) (n : nat) (f : Fiber) : State :=
    let x := fcomp f in
    set_fiber Σ γ n (mkFiber Σ (mkXC (base x) (scope x) (env x) (sel x) (next Σ γ))
                             (fparent f) (disposed f) (life f)).

  (** ** Rules *)

  (** Some present fiber already has the root scope [[Rt i]]. *)
  Definition taken (γ : State) (i : nat) : bool :=
    existsb (fun m => match fibers γ m with
                      | Some f => scope_eqb (scope (fcomp f)) [Rt i]
                      | None => false
                      end) (names Σ γ).

  (** Labels name base components; an inserted fiber's scope is its
      instance id, given by the orchestrator ([xinst]), not a runtime
      name, so it does not depend on the schedule. *)
  Definition klab (γ : State) (ℓ : @Calculus.Label C) : Label :=
    match ℓ with
    | OInsert c => OInsert (mkXC c [Rt (xinst (xprog c))] [] [] 0)
    | ODispose n => ODispose n
    | OReset n => OReset n
    | LBegin n => LBegin n
    | LStep n => LStep n
    | LDivert n => LDivert n
    | LLeave n => LLeave n
    | LUndo n => LUndo n
    | LRetireChild n => LRetireChild n
    | LUnloaded n => LUnloaded n
    | LRemove n => LRemove n
    | OReact n i => OReact n i
    | ORestart n => ORestart n
    end.

  (** - [X-Begin n]: an Inactive fiber whose exported dependencies are all
        resolved chooses its selection, then begins as in the core.
      - [X-Step n]: the core step, while the selection is unchanged.
      - [X-Divert n], [X-Leave n]: the core rule, or, when the selection
        has changed though the core target has not, the same move to
        Unloading.
      - [X-React n i]: the core rule, after stamping [n] with the name the
        child will get.
      - [X-Insert c]: the core rule, unless the instance id of [c] is
        already in use.
      - every other label: the core rule. *)
  Definition kstep (γ : State) (ℓ : @Calculus.Label C) : option State :=
    match ℓ with
    | OInsert c => if taken γ (xinst (xprog c)) then None else step γ (klab γ ℓ)
    | LBegin n =>
        match fibers γ n with
        | Some f =>
            match life f with
            | Inactive _ None =>
                match fparent f with
                | Some _ => if fresh γ f then step γ (LBegin n) else None
                | None => if all_selected γ (base (fcomp f)) then step (recomp γ n f) (LBegin n) else None
                end
            | _ => None
            end
        | None => None
        end
    | LStep n =>
        match fibers γ n with
        | Some f => if fresh γ f then step γ (LStep n) else None
        | None => None
        end
    | LDivert n =>
        match fibers γ n with
        | Some f =>
            if fresh γ f then step γ (LDivert n)
            else match life f with
                 | Loading _ _ acc w => Some (set_life Σ γ n f (Unloading Σ acc w None))
                 | _ => None
                 end
        | None => None
        end
    | LLeave n =>
        match fibers γ n with
        | Some f =>
            if fresh γ f then step γ (LLeave n)
            else match life f with
                 | Active _ acc w => Some (set_life Σ γ n f (Unloading Σ acc w None))
                 | _ => None
                 end
        | None => None
        end
    | OReact n i =>
        match fibers γ n with
        | Some f => match life f with Active _ _ _ => step (retick γ n f) (OReact n i) | _ => None end
        | None => None
        end
    | _ => step γ (klab γ ℓ)
    end.

  Fixpoint krun (γ : State) (ls : list (@Calculus.Label C)) : option State :=
    match ls with
    | [] => Some γ
    | ℓ :: ls' => match kstep γ ℓ with Some γ' => krun γ' ls' | None => None end
    end.

  Definition KReachable (γ : State) : Prop := exists ls, krun (@init Key Σ XC) ls = Some γ.

  (** ** Correspondence with the core *)

  Lemma target_disposed (γ : State) n f :
    fibers γ n = Some f -> disposed f = true -> target γ n = None.
  Proof. intros Hn Hd; unfold Calculus.target; rewrite Hn, Hd; reflexivity. Qed.

  (** Every extended step is a core step of [prog'], a core [L-Begin]
      after choosing the selection, a core [O-Restart], or a core
      [O-React] after stamping. *)
  Theorem kstep_core (γ γ' : State) ℓ :
    kstep γ ℓ = Some γ' ->
    step γ (klab γ ℓ) = Some γ' \/
    (exists n f, ℓ = LBegin n /\ fibers γ n = Some f /\ life f = Inactive Σ None /\
                 all_selected γ (base (fcomp f)) = true /\ fparent f = None /\
                 step (recomp γ n f) (LBegin n) = Some γ') \/
    (exists n, step γ (ORestart n) = Some γ') \/
    (exists n i f, ℓ = OReact n i /\ fibers γ n = Some f /\
                   step (retick γ n f) (OReact n i) = Some γ').
  Proof.
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [kstep klab]; intros H;
      try (left; exact H).
    - (* OInsert *)
      destruct (taken γ (xinst (xprog c))); [discriminate | left; exact H].
    - (* LBegin *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f) as [[z|]| | |] eqn:Hl; try discriminate.
      destruct (fparent f) as [q|] eqn:Hp.
      + destruct (fresh γ f); [left; exact H | discriminate].
      + destruct (all_selected γ (base (fcomp f))) eqn:Ha; [|discriminate].
        right; left; exists n, f; repeat split; auto.
    - (* LStep *)
      destruct (fibers γ n) as [f|]; [|discriminate].
      destruct (fresh γ f); [left; exact H | discriminate].
    - (* LDivert *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (fresh γ f); [left; exact H|].
      destruct (life f) as [|P acc w| |] eqn:Hl; try discriminate.
      injection H as <-.
      destruct (disposed f) eqn:Hd.
      + left; cbn [Calculus.step]; rewrite Hn, Hl.
        unfold target_is; rewrite (target_disposed γ n f Hn Hd); reflexivity.
      + right; right; left; exists n; cbn [Calculus.step]; rewrite Hn, Hd, Hl; reflexivity.
    - (* LLeave *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (fresh γ f); [left; exact H|].
      destruct (life f) as [| |acc w|] eqn:Hl; try discriminate.
      injection H as <-.
      destruct (disposed f) eqn:Hd.
      + left; cbn [Calculus.step]; rewrite Hn, Hl.
        unfold target_is; rewrite (target_disposed γ n f Hn Hd); reflexivity.
      + right; right; left; exists n; cbn [Calculus.step]; rewrite Hn, Hd, Hl; reflexivity.
    - (* OReact *)
      destruct (fibers γ n) as [f|] eqn:Hn; [|discriminate].
      destruct (life f); try discriminate.
      right; right; right; exists n, i, f; auto.
  Qed.

  (** Conversely, at a fiber whose selection is unchanged the extended
      step is the core step. *)
  Theorem kstep_fresh (γ : State) ℓ n f :
    fibers γ n = Some f -> fresh γ f = true ->
    (ℓ = LStep n \/ ℓ = LDivert n \/ ℓ = LLeave n) ->
    kstep γ ℓ = step γ (klab γ ℓ).
  Proof.
    intros Hn Hf Hl; destruct Hl as [E|[E|E]]; subst ℓ; cbn [kstep klab];
      rewrite Hn, Hf; reflexivity.
  Qed.

  (** ** Hygiene: different scopes never share a key *)

  Lemma kmem_provs (s : Scope) (c : C) k :
    kmem key_eq_dec k (map (pair s) (xprovs c)) = true -> fst k = s.
  Proof.
    unfold kmem; rewrite existsb_exists; intros [k' [Hin E]].
    apply in_map_iff in Hin as [y [<- _]].
    unfold keqb in E; destruct (key_eq_dec k (s, y)) as [->|]; [reflexivity | discriminate].
  Qed.

  Lemma overlaps_scope (x1 x2 : XC) :
    scope x1 <> scope x2 ->
    overlaps key_eq_dec (provs Σ (prog' x1)) (provs Σ (prog' x2)) = false.
  Proof.
    intros Hne; cbn [prog' provs].
    destruct (overlaps key_eq_dec (map (pair (scope x1)) (xprovs (base x1)))
                (map (pair (scope x2)) (xprovs (base x2)))) eqn:E; [|reflexivity].
    unfold overlaps in E; apply existsb_exists in E as [k [Hin M]].
    apply in_map_iff in Hin as [y [<- _]].
    apply kmem_provs in M; cbn in M; congruence.
  Qed.

  (** A component whose scope no present fiber has never conflicts: the
      core's conflict checks at [O-Insert], [PSpawn] and [O-React] reduce
      to the uniqueness of scopes. *)
  Theorem conflict_scope (γ : State) (x : XC) :
    (forall m f, fibers γ m = Some f -> scope (fcomp f) <> scope x) ->
    conflict γ x = false.
  Proof.
    intros Hs; unfold Calculus.conflict.
    apply not_true_iff_false; intros E; apply existsb_exists in E as [m [_ E]].
    destruct (fibers γ m) as [f|] eqn:Hm; [|discriminate].
    rewrite overlaps_scope in E; [discriminate|].
    intros Q; exact (Hs m f Hm (eq_sym Q)).
  Qed.

  (** ** Conservativity: no exported dependency *)

  (** When no component has an exported dependency, choosing a selection
      changes nothing and the extended step is the core step of [prog'] at
      every state whose fibers have selected nothing. (A component may
      still export names; only resolving them by selection is absent.) *)
  Definition NoGlobal : Prop := forall c, globals c = [].

  Definition Plain (γ : State) : Prop := forall n f, fibers γ n = Some f -> sel (fcomp f) = [].

  Lemma fresh_noglobal (γ : State) f : NoGlobal -> sel (fcomp f) = [] -> fresh γ f = true.
  Proof.
    intros G E; unfold fresh, all_selected, choose; rewrite G, E; cbn [forallb map andb].
    destruct (list_eq_dec ns_eq_dec [] []) as [_|Q]; [reflexivity | contradiction Q; reflexivity].
  Qed.

  Lemma all_selected_noglobal (γ : State) c : NoGlobal -> all_selected γ c = true.
  Proof. intros G; unfold all_selected; rewrite G; reflexivity. Qed.

  Lemma recomp_plain (γ : State) n f :
    NoGlobal -> fibers γ n = Some f -> sel (fcomp f) = [] -> recomp γ n f = γ.
  Proof.
    intros G Hn E; unfold recomp, choose; rewrite G; cbn.
    destruct γ as [nx F B ol il]; cbn in *; unfold set_fiber, with_fibers; cbn.
    f_equal; apply functional_extensionality; intros m.
    unfold fupd; destruct (Nat.eqb_spec m n) as [->|]; [|reflexivity].
    rewrite Hn; destruct f as [[c s e S t] q d l]; cbn in *; subst S; reflexivity.
  Qed.

  (** [O-React] stamps the fiber first; every other label leaves the state
      as it is. *)
  Definition prep (γ : State) (ℓ : @Calculus.Label C) : State :=
    match ℓ with
    | OReact n _ =>
        match fibers γ n with
        | Some f => match life f with Active _ _ _ => retick γ n f | _ => γ end
        | None => γ
        end
    | _ => γ
    end.

  Theorem kstep_conservative (γ : State) ℓ :
    NoGlobal -> Plain γ -> (forall c, ℓ = OInsert c -> taken γ (xinst (xprog c)) = false) ->
    kstep γ ℓ = step (prep γ ℓ) (klab γ ℓ).
  Proof.
    intros G Pl HT.
    destruct ℓ as [c|n|n|n|n|n|n|n|n|n|n|n i|n]; cbn [kstep klab prep]; try reflexivity.
    - rewrite (HT c eq_refl); reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn.
      + destruct (life f) as [[z|]| | |] eqn:Hl;
          try (cbn [Calculus.step]; rewrite Hn, Hl; reflexivity).
        destruct (fparent f) as [q|].
        * rewrite (fresh_noglobal γ f G (Pl n f Hn)); reflexivity.
        * rewrite all_selected_noglobal by exact G.
          rewrite (recomp_plain γ n f G Hn (Pl n f Hn)); reflexivity.
      + cbn [Calculus.step]; rewrite Hn; reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn.
      + rewrite (fresh_noglobal γ f G (Pl n f Hn)); reflexivity.
      + cbn [Calculus.step]; rewrite Hn; reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn.
      + rewrite (fresh_noglobal γ f G (Pl n f Hn)); reflexivity.
      + cbn [Calculus.step]; rewrite Hn; reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn.
      + rewrite (fresh_noglobal γ f G (Pl n f Hn)); reflexivity.
      + cbn [Calculus.step]; rewrite Hn; reflexivity.
    - destruct (fibers γ n) as [f|] eqn:Hn; [|cbn [Calculus.step]; rewrite Hn; reflexivity].
      destruct (life f) as [| |acc w|] eqn:Hl; [| |reflexivity|];
        cbn [Calculus.step]; rewrite Hn, Hl; reflexivity.
  Qed.

  (** ** Safety: [WF] holds along every extended execution *)

  (** Replacing a fiber's component keeps [WF] when the provided keys stay,
      and the dependencies stay while the fiber is installed: [WF] reads
      nothing else of a component. *)
  Lemma wf_recomp_gen (γ : State) n f x' :
    WF γ -> fibers γ n = Some f ->
    provs Σ (prog' x') = provs Σ (prog' (fcomp f)) ->
    (is_installed Σ (life f) = true -> deps Σ (prog' x') = deps Σ (prog' (fcomp f))) ->
    WF (set_fiber Σ γ n (mkFiber Σ x' (fparent f) (disposed f) (life f))).
  Proof.
    intros W Hn HP HD.
    set (f' := mkFiber Σ x' (fparent f) (disposed f) (life f)).
    assert (Hf : forall m fm, fibers (set_fiber Σ γ n f') m = Some fm ->
                 (m = n /\ fm = f') \/ (m <> n /\ fibers γ m = Some fm)).
    { intros m fm H; exact (fibers_set_fiber_inv Σ γ n f' m fm H). }
    assert (Hback : forall m fm, fibers (set_fiber Σ γ n f') m = Some fm ->
                    exists fm0, fibers γ m = Some fm0 /\ life fm = life fm0 /\
                      fparent fm = fparent fm0 /\
                      fprovs Σ prog' fm = fprovs Σ prog' fm0 /\
                      (is_installed Σ (life fm0) = true -> fdeps Σ prog' fm = fdeps Σ prog' fm0)).
    { intros m fm H; destruct (Hf m fm H) as [[-> ->]|[_ H']].
      - exists f; split; [exact Hn|]; split; [reflexivity|]; split; [reflexivity|].
        split; [exact HP | exact HD].
      - exists fm; split; [exact H'|]; split; [reflexivity|]; split; [reflexivity|].
        split; [reflexivity|]; intros _; reflexivity. }
    assert (Hfwd : forall m fm0, fibers γ m = Some fm0 ->
                   exists fm, fibers (set_fiber Σ γ n f') m = Some fm /\ life fm = life fm0).
    { intros m fm0 H0; unfold set_fiber; cbn; unfold fupd.
      destruct (Nat.eqb_spec m n) as [->|].
      - exists f'; split; [reflexivity|]; rewrite Hn in H0; injection H0 as <-; reflexivity.
      - exists fm0; auto. }
    destruct W as [Wn Wp Ws Wpar Wd Wv Wk Wb Wu Wuu]; split; cbn [Calculus.next Calculus.binds set_fiber with_fibers] in *.
    - intros m fm H; destruct (Hback m fm H) as (fm0 & H0 & _); eauto.
    - exact Wp.
    - intros m fm m' H I; destruct (Hback m fm H) as (fm0 & H0 & El & _); rewrite El in I; eauto.
    - intros m fm q H Hq; destruct (Hback m fm H) as (fm0 & H0 & _ & Ep & _); rewrite Ep in Hq.
      destruct (Wpar m fm0 q H0 Hq) as (fq & Hq0 & Iq & Uq).
      destruct (Hfwd q fq Hq0) as (fq' & Hq' & El).
      exists fq'; rewrite El; auto.
    - intros m m' fm fm' Hne H H'.
      destruct (Hback m fm H) as (fm0 & H0 & _ & _ & Ep & _).
      destruct (Hback m' fm' H') as (fm0' & H0' & _ & _ & Ep' & _).
      rewrite Ep, Ep'; eauto.
    - intros m fm k p H I; destruct (Hback m fm H) as (fm0 & H0 & El & _); rewrite El in I; eauto.
    - intros m fm H I; destruct (Hback m fm H) as (fm0 & H0 & El & _ & _ & Eq).
      rewrite El in I |- *; rewrite (Eq I); eauto.
    - intros k b Hb; destruct (Wb k b Hb) as (fo & Ho & Io & Ko & Uo).
      destruct (Hfwd _ fo Ho) as (fo' & Ho' & El).
      exists fo'; rewrite El; repeat split; auto.
      destruct (Hback _ fo' Ho') as (fo0 & H0 & _ & _ & Ep & _).
      rewrite Ho in H0; injection H0 as <-; rewrite Ep; exact Ko.
    - intros m fm k p H I; destruct (Hback m fm H) as (fm0 & H0 & El & _); rewrite El in I; eauto.
    - intros m fm H; destruct (Hback m fm H) as (fm0 & H0 & El & _).
      pose proof (Wuu m fm0 H0) as U; rewrite El; exact U.
  Qed.

  (** Choosing the selection of an Inactive fiber keeps [WF]: its provided
      keys do not depend on the selection. *)
  Lemma wf_recomp (γ : State) n f :
    WF γ -> fibers γ n = Some f -> is_installed Σ (life f) = false -> WF (recomp γ n f).
  Proof.
    intros W Hn Hi; apply wf_recomp_gen; auto.
    intros I; rewrite Hi in I; discriminate.
  Qed.

  (** Stamping keeps [WF]: neither keys nor dependencies read the tick. *)
  Lemma wf_retick (γ : State) n f :
    WF γ -> fibers γ n = Some f -> WF (retick γ n f).
  Proof.
    intros W Hn; apply wf_recomp_gen; auto; reflexivity.
  Qed.

  Theorem kpreservation (γ γ' : State) ℓ : WF γ -> kstep γ ℓ = Some γ' -> WF γ'.
  Proof.
    intros W H.
    destruct (kstep_core γ γ' ℓ H)
      as [S|[(n & f & _ & Hn & Hl & _ & _ & S)|[(n & S)|(n & i & f & _ & Hn & S)]]].
    - exact (preservation key_eq_dec Σ prog' γ γ' _ W S).
    - apply (preservation key_eq_dec Σ prog' (recomp γ n f) γ' (LBegin n)); [|exact S].
      apply wf_recomp; auto; rewrite Hl; reflexivity.
    - exact (preservation key_eq_dec Σ prog' γ γ' _ W S).
    - apply (preservation key_eq_dec Σ prog' (retick γ n f) γ' (OReact n i)); [|exact S].
      apply wf_retick; auto.
  Qed.

  (** Every extended execution stays well formed, so the core ordering
      theorems hold at every state it reaches. *)
  Theorem kwf_reachable (γ : State) : KReachable γ -> WF γ.
  Proof.
    intros [ls H].
    assert (G : forall γ0, WF γ0 -> krun γ0 ls = Some γ -> WF γ).
    { clear H; induction ls as [|ℓ ls IH]; cbn; intros γ0 W0 H0.
      - injection H0 as <-; exact W0.
      - destruct (kstep γ0 ℓ) as [γ1|] eqn:Hs; [|discriminate].
        exact (IH γ1 (kpreservation γ0 γ1 ℓ W0 Hs) H0). }
    exact (G _ (wf_init key_eq_dec Σ prog') H).
  Qed.
End Scoped.
