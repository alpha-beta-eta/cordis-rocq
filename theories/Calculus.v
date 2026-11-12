(** * The dynamic composition calculus, v1 (R2)

    See docs/RULES.md. Every rule is a case of one function
    [step : State -> Label -> option State]; [None] means the rule does not
    apply. v1 uses one service Σ for every key; several services are combined
    into one beforehand. *)

From Stdlib Require Import List PeanoNat Bool.
From Cordis Require Import Prelude Service.
Import ListNotations.

Section Calculus.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type}.

  (** ** Programs and components *)
  Inductive Prog : Type :=
  | PDone
  | PFail
  | POp (k : K) (a : Op Σ) (κ : Out Σ -> Prog)
  | PProvide (k : K) (s : St Σ) (P : Prog)
  | PSpawn (c : C) (P : Prog).

  (** [reacts]: the handlers the component runs, each as a child fiber,
      when an event reaches it while it is Active (rule [O-React]). *)
  Record Component : Type := mkComponent {
    deps : list K;
    provs : list K;
    body : Prog;
    reacts : list C
  }.

  Context (prog : C -> Component).

  (** ** State *)
  Inductive Err : Type := EUser | EOp | EUnresolved | EConflict.

  Inductive Undo : Type :=
  | UOp (k : K) (pid : nat) (tok : nat) (g : St Σ -> St Σ)
  | UProv (k : K) (pid : nat)
  | USpawn (m : nat).

  (** A view lists, in the order of [deps], the pid each dependency
      resolves to. *)
  Definition View : Type := list (K * nat).

  Inductive Life : Type :=
  | Inactive (z : option Err)
  | Loading (P : Prog) (acc : list Undo) (w : View)
  | Active (acc : list Undo) (w : View)
  | Unloading (acc : list Undo) (w : View) (z : option Err).

  Record Fiber : Type := mkFiber {
    comp : C;
    parent : option nat;     (* None: inserted by the orchestrator *)
    disposed : bool;
    life : Life
  }.

  Record Binding : Type := mkBinding {
    pid : nat;
    owner : nat;
    bst : St Σ
  }.

  (** Every name and pid ever drawn is below [next].

      [oplog] and [inilog] are ghost records that no rule reads: the
      operation performed under each token, and the initial state of each
      provision (by pid). They let the metatheory speak of what an
      accumulator's items did. *)
  Record State : Type := mkState {
    next : nat;
    fibers : nat -> option Fiber;
    binds : K -> option Binding;
    oplog : nat -> option (Op Σ);
    inilog : nat -> option (St Σ)
  }.

  Definition init : State :=
    mkState 0 (fun _ => None) (fun _ => None) (fun _ => None) (fun _ => None).

  (** ** Helpers *)
  Definition keqb (x y : K) : bool := if K_eq_dec x y then true else false.
  Definition kmem (k : K) (ks : list K) : bool := existsb (keqb k) ks.
  Definition overlaps (ks1 ks2 : list K) : bool := existsb (fun k => kmem k ks2) ks1.

  Definition fupd (F : nat -> option Fiber) (n : nat) (o : option Fiber) :=
    fun m => if Nat.eqb m n then o else F m.
  Definition bupd (B : K -> option Binding) (k : K) (o : option Binding) :=
    fun k' => if keqb k' k then o else B k'.

  Definition names (γ : State) : list nat := seq 0 (next γ).

  Definition is_active (l : Life) : bool :=
    match l with Active _ _ => true | _ => false end.
  Definition is_installed (l : Life) : bool :=
    match l with Inactive _ => false | _ => true end.
  Definition view_of (l : Life) : View :=
    match l with
    | Loading _ _ w | Active _ w | Unloading _ w _ => w
    | Inactive _ => []
    end.

  Definition acc_of (l : Life) : list Undo :=
    match l with
    | Loading _ acc _ | Active acc _ | Unloading acc _ _ => acc
    | Inactive _ => []
    end.

  Definition view_eq_dec : forall w1 w2 : View, {w1 = w2} + {w1 <> w2}.
  Proof.
    apply list_eq_dec; intros [k1 p1] [k2 p2].
    destruct (K_eq_dec k1 k2), (Nat.eq_dec p1 p2);
      [left; congruence | right; congruence | right; congruence | right; congruence].
  Defined.

  Fixpoint lookup_view (k : K) (w : View) : option nat :=
    match w with
    | [] => None
    | (k', p) :: w' => if keqb k k' then Some p else lookup_view k w'
    end.

  (** ** Derived notions *)

  (** A key is visible when it is bound and its owner is Active. *)
  Definition visible (γ : State) (k : K) : option nat :=
    match binds γ k with
    | Some b =>
        match fibers γ (owner b) with
        | Some f => if is_active (life f) then Some (pid b) else None
        | None => None
        end
    | None => None
    end.

  Fixpoint resolve (γ : State) (ks : list K) : option View :=
    match ks with
    | [] => Some []
    | k :: ks' =>
        match visible γ k, resolve γ ks' with
        | Some p, Some w => Some ((k, p) :: w)
        | _, _ => None
        end
    end.

  (** [None] is ⊥: the fiber ought not to be running. *)
  Definition target (γ : State) (n : nat) : option View :=
    match fibers γ n with
    | Some f => if disposed f then None else resolve γ (deps (prog (comp f)))
    | None => None
    end.

  Definition target_is (γ : State) (n : nat) (w : View) : bool :=
    match target γ n with
    | Some w' => if view_eq_dec w w' then true else false
    | None => false
    end.

  Definition resolves (γ : State) (m p : nat) : bool :=
    match fibers γ m with
    | Some f =>
        is_installed (life f) && existsb (fun kp => Nat.eqb (snd kp) p) (view_of (life f))
    | None => false
    end.

  (** Some installed fiber other than [n] resolves a key to [p]. *)
  Definition relied (γ : State) (n p : nat) : bool :=
    existsb (fun m => negb (Nat.eqb m n) && resolves γ m p) (names γ).

  Definition has_child (γ : State) (n : nat) : bool :=
    existsb (fun m =>
      match fibers γ m with
      | Some f => match parent f with Some q => Nat.eqb q n | None => false end
      | None => false
      end) (names γ).

  (** Component [c] would provide a key some present fiber may provide. *)
  Definition conflict (γ : State) (c : C) : bool :=
    existsb (fun m =>
      match fibers γ m with
      | Some f => overlaps (provs (prog c)) (provs (prog (comp f)))
      | None => false
      end) (names γ).

  (** ** State updates *)
  Definition with_fibers (γ : State) (F : nat -> option Fiber) : State :=
    mkState (next γ) F (binds γ) (oplog γ) (inilog γ).
  Definition with_binds (γ : State) (B : K -> option Binding) : State :=
    mkState (next γ) (fibers γ) B (oplog γ) (inilog γ).
  Definition bump (γ : State) : State :=
    mkState (S (next γ)) (fibers γ) (binds γ) (oplog γ) (inilog γ).
  Definition log_op (γ : State) (t : nat) (a : Op Σ) : State :=
    mkState (next γ) (fibers γ) (binds γ)
      (fun t' => if Nat.eqb t' t then Some a else oplog γ t') (inilog γ).
  Definition log_ini (γ : State) (p : nat) (s : St Σ) : State :=
    mkState (next γ) (fibers γ) (binds γ) (oplog γ)
      (fun p' => if Nat.eqb p' p then Some s else inilog γ p').

  Definition set_fiber (γ : State) (n : nat) (f : Fiber) : State :=
    with_fibers γ (fupd (fibers γ) n (Some f)).

  Definition set_life (γ : State) (n : nat) (f : Fiber) (l : Life) : State :=
    set_fiber γ n (mkFiber (comp f) (parent f) (disposed f) l).

  (** ** Labels *)
  Inductive Label : Type :=
  | OInsert (c : C)
  | ODispose (n : nat)
  | OReset (n : nat)
  | LBegin (n : nat)
  | LStep (n : nat)
  | LDivert (n : nat)
  | LLeave (n : nat)
  | LUndo (n : nat)
  | LRetireChild (n : nat)
  | LUnloaded (n : nat)
  | LRemove (n : nat)
  | OReact (n i : nat)
  | ORestart (n : nat).   (* forced reload: Cordis restart *)

  (** ** One step of a Loading fiber *)
  Definition load_step (γ : State) (n : nat) (f : Fiber)
      (P : Prog) (acc : list Undo) (w : View) : State :=
    let fail z := set_life γ n f (Unloading acc w (Some z)) in
    match P with
    | PDone => set_life γ n f (Active acc w)
    | PFail => fail EUser
    | POp k a κ =>
        let rp :=
          if kmem k (deps (prog (comp f))) then lookup_view k w
          else match binds γ k with
               | Some b => if Nat.eqb (owner b) n then Some (pid b) else None
               | None => None
               end in
        match rp, binds γ k with
        | Some p, Some b =>
            if Nat.eqb (pid b) p then
              match run a (next γ) (bst b) with
              | Some (s', g, o) =>
                  let γ1 := bump (log_op (with_binds γ
                              (bupd (binds γ) k (Some (mkBinding (pid b) (owner b) s'))))
                              (next γ) a) in
                  set_life γ1 n f (Loading (κ o) (UOp k p (next γ) g :: acc) w)
              | None => set_life (bump γ) n f (Unloading acc w (Some EOp))
              end
            else fail EUnresolved
        | _, _ => fail EUnresolved
        end
    | PProvide k s P' =>
        if kmem k (provs (prog (comp f))) then
          match binds γ k with
          | None =>
              let p := next γ in
              let γ1 := bump (log_ini (with_binds γ (bupd (binds γ) k (Some (mkBinding p n s)))) p s) in
              set_life γ1 n f (Loading P' (UProv k p :: acc) w)
          | Some _ => fail EConflict
          end
        else fail EConflict
    | PSpawn c P' =>
        if conflict γ c then fail EConflict
        else
          let m := next γ in
          let γ1 := bump (with_fibers γ
                      (fupd (fibers γ) m (Some (mkFiber c (Some n) false (Inactive None))))) in
          set_life γ1 n f (Loading P' (USpawn m :: acc) w)
    end.

  (** ** One undo item of an Unloading fiber *)
  Definition undo_step (γ : State) (n : nat) (f : Fiber)
      (u : Undo) (acc : list Undo) (w : View) (z : option Err) : option State :=
    let continue γ' := Some (set_life γ' n f (Unloading acc w z)) in
    match u with
    | UOp k p _ g =>
        match binds γ k with
        | Some b =>
            if Nat.eqb (pid b) p then
              continue (with_binds γ (bupd (binds γ) k
                          (Some (mkBinding (pid b) (owner b) (g (bst b))))))
            else continue γ
        | None => continue γ
        end
    | UProv k p =>
        if relied γ n p then None
        else
          match binds γ k with
          | Some b => if Nat.eqb (pid b) p
                      then continue (with_binds γ (bupd (binds γ) k None))
                      else continue γ
          | None => continue γ
          end
    | USpawn m =>
        match fibers γ m with
        | None => continue γ
        | Some _ => None
        end
    end.

  (** ** The step function *)
  Definition step (γ : State) (ℓ : Label) : option State :=
    match ℓ with
    | OInsert c =>
        if conflict γ c then None
        else Some (bump (with_fibers γ
                (fupd (fibers γ) (next γ) (Some (mkFiber c None false (Inactive None))))))
    | ODispose n =>
        match fibers γ n with
        | Some f => Some (set_fiber γ n (mkFiber (comp f) (parent f) true (life f)))
        | None => None
        end
    | OReset n =>
        match fibers γ n with
        | Some f =>
            match life f with
            | Inactive (Some _) => Some (set_life γ n f (Inactive None))
            | _ => None
            end
        | None => None
        end
    | LBegin n =>
        match fibers γ n with
        | Some f =>
            match life f, target γ n with
            | Inactive None, Some w =>
                Some (set_life γ n f (Loading (body (prog (comp f))) [] w))
            | _, _ => None
            end
        | None => None
        end
    | LStep n =>
        match fibers γ n with
        | Some f =>
            match life f with
            | Loading P acc w =>
                if target_is γ n w then Some (load_step γ n f P acc w) else None
            | _ => None
            end
        | None => None
        end
    | LDivert n =>
        match fibers γ n with
        | Some f =>
            match life f with
            | Loading _ acc w =>
                if target_is γ n w then None
                else Some (set_life γ n f (Unloading acc w None))
            | _ => None
            end
        | None => None
        end
    | LLeave n =>
        match fibers γ n with
        | Some f =>
            match life f with
            | Active acc w =>
                if target_is γ n w then None
                else Some (set_life γ n f (Unloading acc w None))
            | _ => None
            end
        | None => None
        end
    | LUndo n =>
        match fibers γ n with
        | Some f =>
            match life f with
            | Unloading (u :: acc) w z => undo_step γ n f u acc w z
            | _ => None
            end
        | None => None
        end
    | LRetireChild n =>
        match fibers γ n with
        | Some f =>
            match life f with
            | Unloading (USpawn m :: _) _ _ =>
                match fibers γ m with
                | Some g =>
                    if disposed g then None
                    else Some (set_fiber γ m (mkFiber (comp g) (parent g) true (life g)))
                | None => None
                end
            | _ => None
            end
        | None => None
        end
    | LUnloaded n =>
        match fibers γ n with
        | Some f =>
            match life f with
            | Unloading [] _ z => Some (set_life γ n f (Inactive z))
            | _ => None
            end
        | None => None
        end
    | LRemove n =>
        match fibers γ n with
        | Some f =>
            match life f with
            | Inactive _ =>
                if disposed f && negb (has_child γ n)
                then Some (with_fibers γ (fupd (fibers γ) n None))
                else None
            | _ => None
            end
        | None => None
        end
    | OReact n i =>
        match fibers γ n with
        | Some f =>
            match life f with
            | Active acc w =>
                match nth_error (reacts (prog (comp f))) i with
                | Some c =>
                    if disposed f || conflict γ c then None
                    else
                      let m := next γ in
                      let γ1 := bump (with_fibers γ
                                  (fupd (fibers γ) m (Some (mkFiber c (Some n) false (Inactive None))))) in
                      Some (set_life γ1 n f (Active (USpawn m :: acc) w))
                | None => None
                end
            | _ => None
            end
        | None => None
        end
    | ORestart n =>
        match fibers γ n with
        | Some f =>
            if disposed f then None
            else match life f with
                 | Loading _ acc w | Active acc w => Some (set_life γ n f (Unloading acc w None))
                 | _ => None
                 end
        | None => None
        end
    end.

  (** [ORestart] forces the unload a [LDivert] or [LLeave] would do. *)
  Lemma restart_shape (γ γ' : State) n :
    step γ (ORestart n) = Some γ' ->
    exists f acc w, fibers γ n = Some f /\ disposed f = false /\
      (exists P, life f = Loading P acc w \/ life f = Active acc w) /\
      γ' = set_life γ n f (Unloading acc w None).
  Proof.
    cbn [step]; destruct (fibers γ n) as [f|]; [|discriminate].
    destruct (disposed f) eqn:Hd; [discriminate|].
    destruct (life f) as [|P acc w|acc w|] eqn:Hl; try discriminate; intros [= <-].
    - exists f, acc, w; repeat split; auto; exists P; auto.
    - exists f, acc, w; repeat split; auto; exists PDone; auto.
  Qed.

  (** ** Executions: a start state and a list of labels *)
  Fixpoint run_labels (γ : State) (ls : list Label) : option State :=
    match ls with
    | [] => Some γ
    | ℓ :: ls' =>
        match step γ ℓ with
        | Some γ' => run_labels γ' ls'
        | None => None
        end
    end.

  (** Is a lifecycle rule enabled at [n]? Used to state progress later. *)
  Definition lifecycle_labels (n : nat) : list Label :=
    [LBegin n; LStep n; LDivert n; LLeave n; LUndo n;
     LRetireChild n; LUnloaded n; LRemove n].

  (** Quiescence: no lifecycle rule applies anywhere. *)
  Definition quiet (γ : State) : Prop :=
    forall n ℓ, In ℓ (lifecycle_labels n) -> step γ ℓ = None.
End Calculus.

Arguments PDone {K Σ C}.
Arguments PFail {K Σ C}.
Arguments POp {K Σ C} k a κ.
Arguments PProvide {K Σ C} k s P.
Arguments PSpawn {K Σ C} c P.
Arguments mkComponent {K Σ C} deps provs body reacts.
Arguments OInsert {C} c.
Arguments ODispose {C} n.
Arguments OReset {C} n.
Arguments ORestart {C} n.
Arguments LBegin {C} n.
Arguments LStep {C} n.
Arguments LDivert {C} n.
Arguments LLeave {C} n.
Arguments LUndo {C} n.
Arguments LRetireChild {C} n.
Arguments LUnloaded {C} n.
Arguments LRemove {C} n.
Arguments OReact {C} n i.
