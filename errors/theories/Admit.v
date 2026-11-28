(** * Insert-time conflicts checked at provide time (errors/DESIGN.md, section 4.2)

    The core refuses [O-Insert] of a component whose provisions meet those
    of a fiber still in the table, retired or not (the paper's O-Insert,
    DESIGN.md difference c). Cordis cannot: provisions are declared inside
    [apply], so the conflict surfaces when the second [provide] throws, and
    the fiber is FAILED for good (cordis [reflect.ts:225], [fiber.ts:436]).

    [astep] is the core with Cordis's choice: [O-Insert] admits any
    component, and the core's own [PProvide] check (the key is already
    bound) fails the load with [EConflict]. This is the [fail] variant of
    section 4.2; the [wait] variant is future work.

    The file contains no theorem about [astep] in general, only the
    counterexample of cordiverse/cordis#358, computed on the example of
    [Examples/Basic.v] (component 0 provides [tools], component 1 uses it):

    - after the provider is disposed, while the consumer still holds it, the
      core refuses to insert a new provider ([core_refuses]);
    - under [astep] the same orchestration inputs give two different quiet
      outcomes, depending only on the order of lifecycle steps: if the new
      provider loads before the old one is removed, it fails with
      [EConflict] and the consumer stays Inactive with [tools] unbound
      ([early_obs], [early_stuck]); if it loads after, everything is Active
      ([late_obs]).

    Nothing in the core imports this file. *)

From Stdlib Require Import List PeanoNat.
From Cordis Require Import Prelude Service Calculus Services.Registry Examples.Basic.
Import ListNotations.

Section Admit.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  Definition astep (γ : @State K Σ C) (ℓ : @Label C) : option (@State K Σ C) :=
    match ℓ with
    | OInsert c =>
        Some (bump Σ (with_fibers Σ γ
                (fupd Σ (fibers Σ γ) (next Σ γ) (Some (mkFiber Σ c None false (Inactive Σ None))))))
    | _ => step K_eq_dec Σ prog γ ℓ
    end.

  Fixpoint arun_labels (γ : @State K Σ C) (ls : list (@Label C)) : option (@State K Σ C) :=
    match ls with
    | [] => Some γ
    | ℓ :: ls' => match astep γ ℓ with Some γ' => arun_labels γ' ls' | None => None end
    end.

  (** Where the core admits an insertion, [astep] does the same. *)
  Lemma astep_conservative (γ γ' : @State K Σ C) ℓ :
    step K_eq_dec Σ prog γ ℓ = Some γ' -> astep γ ℓ = Some γ'.
  Proof.
    destruct ℓ; cbn [astep]; intros H; try exact H.
    cbn [step] in H; destruct (conflict K_eq_dec Σ prog γ c); [discriminate | exact H].
  Qed.
End Admit.

(** ** cordiverse/cordis#358 *)

Definition arunEx := arun_labels Nat.eq_dec ΣR progEx.
Definition astepEx := astep Nat.eq_dec ΣR progEx.

(** The old provider (fiber 0) is disposed and Unloading; the consumer
    (fiber 1) is Unloading too and still holds [tools], so fiber 0 cannot
    withdraw it yet ([Basic.provider_blocked]). *)
Example core_refuses :
  match leaving with Some γ => stepEx γ (OInsert 0) | None => None end = None.
Proof. reflexivity. Qed.

(** The new provider gets the name 4. *)
Definition reinserted :=
  match leaving with Some γ => astepEx γ (OInsert 0) | None => None end.

(** The error mark of a fiber, when it is Inactive. *)
Definition err (γ : @State nat ΣR nat) (n : nat) : option (option Err) :=
  match fibers ΣR γ n with
  | Some f => match life ΣR f with Inactive _ z => Some z | _ => None end
  | None => None
  end.

(** Old provider, consumer, new provider; the new provider's error mark;
    whether [tools] is bound. *)
Definition aobs (γ : option (@State nat ΣR nat)) :=
  match γ with
  | Some γ => Some (tag γ 0, tag γ 1, tag γ 4, err γ 4, tool γ 7)
  | None => None
  end.

(** The old fiber drains: the consumer undoes its registration and goes
    Inactive, then the provider withdraws [tools] and is removed. *)
Definition drain : list (@Label nat) :=
  [LUndo 1; LUnloaded 1; LUndo 0; LUnloaded 0; LRemove 0].

(** Schedule 1: the new provider loads at once. Its [provide] meets the old
    binding and fails. *)
Definition early :=
  match reinserted with
  | Some γ => arunEx γ ([LBegin 4; LStep 4; LUnloaded 4] ++ drain)
  | None => None
  end.

Example early_obs :
  aobs early = Some (None, Some 0, Some 0, Some (Some EConflict), None).
Proof. reflexivity. Qed.

(** Nothing can move it: the consumer has no provider to resolve, the new
    provider is failed and does not begin again. *)
Example early_stuck :
  match early with
  | Some γ => (astepEx γ (LBegin 1), astepEx γ (LBegin 4))
  | None => (Some S0, Some S0)
  end = (None, None).
Proof. reflexivity. Qed.

(** Schedule 2: the same inputs, the old fiber drains first. *)
Definition late :=
  match reinserted with
  | Some γ => arunEx γ (drain ++ [LBegin 4; LStep 4; LStep 4; LBegin 1; LStep 1; LStep 1])
  | None => None
  end.

Example late_obs :
  aobs late = Some (None, Some 2, Some 2, None, Some (Some 42)).
Proof. reflexivity. Qed.
