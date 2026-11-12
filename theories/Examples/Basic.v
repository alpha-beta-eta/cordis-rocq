(** * A worked example: a registry provider and a consumer

    Component 0 provides the key [tools] with an empty registry.
    Component 1 declares [tools] and registers tool 7 ↦ 42 on it.
    Each example below runs a schedule with [run_labels] and checks the
    result by computation. *)

From Stdlib Require Import List PeanoNat.
From Cordis Require Import Prelude Service Calculus Services.Registry.
Import ListNotations.

Definition ΣR : Service := Registry nat nat Nat.eq_dec.
Definition tools : nat := 0.
Definition empty_reg : St ΣR := fun _ => None.

Definition provider : @Component nat ΣR nat :=
  mkComponent [] [tools] (PProvide (Σ := ΣR) tools empty_reg PDone) [].

Definition consumer : @Component nat ΣR nat :=
  mkComponent [tools] [] (POp (Σ := ΣR) tools (Register nat nat 7 42) (fun _ => PDone)) [].

Definition progEx (c : nat) : @Component nat ΣR nat :=
  match c with 0 => provider | _ => consumer end.

Definition S0 : @State nat ΣR nat := @init nat ΣR nat.
Definition stepEx := step Nat.eq_dec ΣR progEx.
Definition runEx := run_labels Nat.eq_dec ΣR progEx.

(** Lifecycle tag: 0 Inactive, 1 Loading, 2 Active, 3 Unloading. *)
Definition tag (γ : @State nat ΣR nat) (n : nat) : option nat :=
  match fibers ΣR γ n with
  | Some f =>
      Some match life ΣR f with
           | Inactive _ _ => 0 | Loading _ _ _ _ => 1
           | Active _ _ _ => 2 | Unloading _ _ _ _ => 3
           end
  | None => None
  end.

(** The tool registered under name [x], if the registry is bound. *)
Definition tool (γ : @State nat ΣR nat) (x : nat) : option (option nat) :=
  match binds ΣR γ tools with
  | Some b => Some (bst ΣR b x)
  | None => None
  end.

Definition obs (γ : option (@State nat ΣR nat)) :=
  match γ with
  | Some γ => Some (tag γ 0, tag γ 1, tool γ 7)
  | None => None
  end.

(** ** Loading: the consumer cannot begin before the provider is Active. *)
Definition inserted := runEx S0 [OInsert 0; OInsert 1].

Example consumer_waits :
  match inserted with Some γ => stepEx γ (LBegin 1) | None => None end = None.
Proof. reflexivity. Qed.

Definition loaded :=
  runEx S0 [OInsert 0; OInsert 1;
            LBegin 0; LStep 0; LStep 0;
            LBegin 1; LStep 1; LStep 1].

Example loaded_obs :
  obs loaded = Some (Some 2, Some 2, Some (Some 42)).
Proof. reflexivity. Qed.

(** ** Unloading the provider: the consumer leaves first, and the provider's
    withdrawal of [tools] waits until the consumer has unloaded. *)
Definition leaving :=
  match loaded with
  | Some γ => runEx γ [ODispose 0; LLeave 0; LLeave 1]
  | None => None
  end.

Example leaving_obs : obs leaving = Some (Some 3, Some 3, Some (Some 42)).
Proof. reflexivity. Qed.

(** The guard: the provider cannot withdraw [tools] yet. *)
Example provider_blocked :
  match leaving with Some γ => stepEx γ (LUndo 0) | None => None end = None.
Proof. reflexivity. Qed.

Definition unloaded :=
  match leaving with
  | Some γ => runEx γ [LUndo 1; LUnloaded 1; LUndo 0; LUnloaded 0; LRemove 0]
  | None => None
  end.

(** The consumer's registration is undone, the binding is gone, the
    provider is removed, and the consumer is Inactive. *)
Example unloaded_obs : obs unloaded = Some (None, Some 0, None).
Proof. reflexivity. Qed.

(** ** Re-providing: inserting a fresh provider lets the consumer load again,
    against a new provision. Names, pids and tokens share one counter, so
    after names 0, 1, pid 2 and token 3 the new provider is named 4. *)
Definition reloaded :=
  match unloaded with
  | Some γ => runEx γ [OInsert 0; LBegin 4; LStep 4; LStep 4;
                       LBegin 1; LStep 1; LStep 1]
  | None => None
  end.

Example reloaded_obs :
  match reloaded with
  | Some γ => Some (tag γ 1, tag γ 4, tool γ 7)
  | None => None
  end = Some (Some 2, Some 2, Some (Some 42)).
Proof. reflexivity. Qed.

(** ** Divert: the provider is disposed while the consumer is loading. *)
Definition diverted :=
  runEx S0 [OInsert 0; OInsert 1;
            LBegin 0; LStep 0; LStep 0;
            LBegin 1; ODispose 0; LLeave 0;
            LDivert 1; LUnloaded 1;
            LUndo 0; LUnloaded 0; LRemove 0].

Example diverted_obs : obs diverted = Some (None, Some 0, None).
Proof. reflexivity. Qed.

(** ** Conflicts: a second provider of [tools] cannot be inserted. *)
Example second_provider_rejected :
  match inserted with Some γ => stepEx γ (OInsert 0) | None => None end = None.
Proof. reflexivity. Qed.
