(** * Worked examples for hygienic keys

    Names are numbers: [svc] (0) is an exported service name, [state] (1)
    a private one. Each example runs a schedule with [krun] and checks the
    result by computation.

    - Two instances of a plugin that privately provides [state] and spawns
      a child reading it: both load, each child sees its own parent's
      [state] (in the core the second insertion would be rejected).
    - Two exporters of [svc] with the same priority: a tie, so a
      dependent of [svc] waits; nobody fails.
    - A third exporter with a higher priority: the dependent binds to it.
    - A dependent bound to the only exporter reloads when a
      higher-priority exporter becomes Active. *)

From Stdlib Require Import List PeanoNat.
From Cordis Require Import Prelude Service Calculus Services.Registry.
From CordisKeys Require Import Scoped.
Import ListNotations.

Definition ΣR : Service := Registry nat nat Nat.eq_dec.
Definition svc : nat := 0.
Definition state : nat := 1.
Definition empty_reg : St ΣR := fun _ => None.

Definition provide (x : nat) (P : @Prog nat ΣR nat) : @Prog nat ΣR nat :=
  PProvide (Σ := ΣR) x empty_reg P.
Definition register (x : nat) : @Prog nat ΣR nat :=
  POp (Σ := ΣR) x (Register nat nat 7 42) (fun _ => PDone).

Definition exporter (p i : nat) : @XComponent nat ΣR nat :=
  @mkX nat ΣR nat [] [] [svc] (fun _ => p) (provide svc PDone) [] i.

Definition consumer (i : nat) : @XComponent nat ΣR nat :=
  @mkX nat ΣR nat [@Global nat svc] [] [] (fun _ => 0) (register svc) [] i.

Definition plugin (i : nat) : @XComponent nat ΣR nat :=
  @mkX nat ΣR nat [] [state] [] (fun _ => 0) (provide state (PSpawn (Σ := ΣR) 5 PDone)) [] i.

Definition kid (i : nat) : @XComponent nat ΣR nat :=
  @mkX nat ΣR nat [@Local nat state] [] [] (fun _ => 0) (register state) [] i.

Definition reactor (i : nat) : @XComponent nat ΣR nat :=
  @mkX nat ΣR nat [] [] [] (fun _ => 0) PDone [7] i.

Definition handler (i : nat) : @XComponent nat ΣR nat :=
  @mkX nat ΣR nat [] [state] [] (fun _ => 0) (provide state PDone) [] i.

Definition user (i : nat) : @XComponent nat ΣR nat :=
  @mkX nat ΣR nat [@Global nat svc] [] [] (fun _ => 0) (PSpawn (Σ := ΣR) 9 PDone) [] i.

Definition subuser (i : nat) : @XComponent nat ΣR nat :=
  @mkX nat ΣR nat [@Global nat svc] [] [] (fun _ => 0) (register svc) [] i.

(** Every component's instance id is its own number. 0, 1: exporters of
    [svc] with priority 10; 2: with priority 20; 3: a dependent of [svc];
    4 and 10: two instances of a plugin; 5: its child; 6: a component whose
    reaction handler 7 privately provides [state]; 8: a dependent of [svc]
    that spawns 9, which depends on [svc] too. *)
Definition xprogEx (c : nat) : @XComponent nat ΣR nat :=
  match c with
  | 0 | 1 => exporter 10 c
  | 2 => exporter 20 c
  | 3 => consumer c
  | 5 => kid c
  | 6 => reactor c
  | 7 => handler c
  | 8 => user c
  | 9 => subuser c
  | _ => plugin c
  end.

Local Notation XState := (@State (Key (N := nat)) ΣR (XC (N := nat) (C := nat))).

Definition S0 : XState := @init _ ΣR _.
Definition kstepEx := kstep Nat.eq_dec ΣR xprogEx.
Definition krunEx := krun Nat.eq_dec ΣR xprogEx.

(** Lifecycle tag: 0 Inactive, 1 Loading, 2 Active, 3 Unloading. *)
Definition tag (γ : XState) (n : nat) : option nat :=
  match fibers ΣR γ n with
  | Some f =>
      Some match life ΣR f with
           | Inactive _ _ => 0 | Loading _ _ _ _ => 1
           | Active _ _ _ => 2 | Unloading _ _ _ _ => 3
           end
  | None => None
  end.

Definition tags (γ : option XState) (ns : list nat) : option (list (option nat)) :=
  match γ with Some γ => Some (map (tag γ) ns) | None => None end.

(** The tool 7 in the registry at key [k]. *)
Definition tool (γ : option XState) (k : Key) : option (option nat) :=
  match γ with
  | Some γ => match binds ΣR γ k with Some b => Some (bst ΣR b 7) | None => None end
  | None => None
  end.

(** ** Two instances of one plugin *)

(** The same instance cannot be inserted twice. *)
Example duplicate_rejected :
  match krunEx S0 [OInsert 4] with Some γ => kstepEx γ (OInsert 4) | None => None end = None.
Proof. reflexivity. Qed.

Definition twice :=
  krunEx S0 [OInsert 4; OInsert 10;
             LBegin 0; LStep 0; LStep 0; LStep 0;     (* provide, spawn 3, done *)
             LBegin 1; LStep 1; LStep 1; LStep 1;     (* provide, spawn 5, done *)
             LBegin 3; LStep 3; LStep 3;
             LBegin 5; LStep 5; LStep 5].

Example twice_active : tags twice [0; 1; 3; 5] = Some [Some 2; Some 2; Some 2; Some 2].
Proof. reflexivity. Qed.

(** Each child registered in its own parent's [state]. *)
Example twice_separate :
  (tool twice ([Rt 4], state), tool twice ([Rt 10], state)) = (Some (Some 42), Some (Some 42)).
Proof. reflexivity. Qed.

(** ** A tie on [svc]: the dependent waits *)
Definition tie :=
  krunEx S0 [OInsert 0; OInsert 1; OInsert 3;
             LBegin 0; LStep 0; LStep 0;
             LBegin 1; LStep 1; LStep 1].

Example tie_waits : match tie with Some γ => kstepEx γ (LBegin 2) | None => None end = None.
Proof. reflexivity. Qed.

Example tie_reported : match tie with Some γ => tied Nat.eq_dec ΣR xprogEx γ svc | None => false end = true.
Proof. reflexivity. Qed.

(** ** A higher-priority exporter resolves the tie *)
Definition resolved :=
  match tie with
  | Some γ => krunEx γ [OInsert 2; LBegin 5; LStep 5; LStep 5; LBegin 2; LStep 2; LStep 2]
  | None => None
  end.

Example resolved_active : tags resolved [0; 1; 5; 2] = Some [Some 2; Some 2; Some 2; Some 2].
Proof. reflexivity. Qed.

Example resolved_binds :
  (tool resolved ([Rt 2], svc), tool resolved ([Rt 0], svc)) = (Some (Some 42), Some None).
Proof. reflexivity. Qed.

(** ** Rebinding: a better candidate appears *)
Definition single :=
  krunEx S0 [OInsert 0; OInsert 3;
             LBegin 0; LStep 0; LStep 0;
             LBegin 1; LStep 1; LStep 1;
             OInsert 2; LBegin 4; LStep 4; LStep 4].

Example single_bound : tool single ([Rt 0], svc) = Some (Some 42).
Proof. reflexivity. Qed.

(** The dependent's core target has not changed, but its selection has:
    it leaves, and on its next begin binds to fiber 4. *)
Example single_leaves :
  tags (match single with Some γ => kstepEx γ (LLeave 1) | None => None end) [0; 1; 4]
  = Some [Some 2; Some 3; Some 2].
Proof. reflexivity. Qed.

Definition rebound :=
  match single with
  | Some γ => krunEx γ [LLeave 1; LUndo 1; LUnloaded 1; LBegin 1; LStep 1; LStep 1]
  | None => None
  end.

Example rebound_binds : tool rebound ([Rt 2], svc) = Some (Some 42).
Proof. reflexivity. Qed.

(** ** One handler fired twice: each firing has its own scope *)
Definition fired :=
  krunEx S0 [OInsert 6; LBegin 0; LStep 0;
             OReact 0 0; OReact 0 0;
             LBegin 1; LStep 1; LStep 1;
             LBegin 2; LStep 2; LStep 2].

Example fired_active : tags fired [0; 1; 2] = Some [Some 2; Some 2; Some 2].
Proof. reflexivity. Qed.

(** ** A child inherits its parent's selection *)
Definition inherited :=
  krunEx S0 [OInsert 0; LBegin 0; LStep 0; LStep 0;
             OInsert 8; LBegin 2; LStep 2; LStep 2;      (* spawn 3, done *)
             LBegin 3; LStep 3; LStep 3].

Example inherited_active : tags inherited [0; 2; 3] = Some [Some 2; Some 2; Some 2].
Proof. reflexivity. Qed.

Example inherited_binds : tool inherited ([Rt 0], svc) = Some (Some 42).
Proof. reflexivity. Qed.
