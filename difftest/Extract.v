(** * The calculus as an executable reference for differential testing

    The step function of [Calculus.v] instantiated with natural-number keys,
    the name-keyed registry of [Services/Registry.v] (names and values are
    natural numbers) as the one service, and components named by natural
    numbers. The component table [prog] stays a parameter: the replay driver
    builds it from the test case.

    Nothing here is proved; the definitions only fix the instance and
    collect what the driver needs. The extracted code is the calculus's own
    [step]; the driver (calc/replay.ml) only chooses labels and compares
    states. *)

From Stdlib Require Import List PeanoNat.
From Cordis Require Import Prelude Service Calculus Services.Registry.
Import ListNotations.

Definition ΣR : Service := Registry nat nat Nat.eq_dec.

Definition DComp := @Component nat ΣR nat.
Definition DProg := @Prog nat ΣR nat.
Definition DState := @State nat ΣR nat.
Definition DLabel := @Label nat.

Definition dinit : DState := @init nat ΣR nat.

Definition dstep (prog : nat -> DComp) (γ : DState) (ℓ : DLabel) : option DState :=
  step Nat.eq_dec ΣR prog γ ℓ.

(** The lifecycle labels enabled at [γ]: empty exactly when [γ] is quiet. *)
Definition denabled (prog : nat -> DComp) (γ : DState) : list DLabel :=
  filter (fun ℓ => match dstep prog γ ℓ with Some _ => true | None => false end)
         (flat_map (@lifecycle_labels nat) (names ΣR γ)).

(** Program constructors at this instance, so the driver needs no casts. *)
Definition dop (k : nat) (x v : nat) (P : DProg) : DProg :=
  POp (Σ := ΣR) k (Register nat nat x v) (fun _ => P).
Definition dprovide (k : nat) (entries : list (nat * nat)) (P : DProg) : DProg :=
  PProvide (Σ := ΣR) k (fold_right (A := St ΣR) (fun '(x, v) s => upd nat nat Nat.eq_dec s x (Some v))
                         (fun _ => None) entries) P.
Definition dspawn (c : nat) (P : DProg) : DProg := PSpawn (Σ := ΣR) c P.
Definition ddone : DProg := PDone (Σ := ΣR).
Definition dfail : DProg := PFail (Σ := ΣR).
Definition dcomp (deps provs : list nat) (body : DProg) : DComp :=
  mkComponent deps provs body [].

(** The name an [UOp] item registered, read from the ghost operation log. *)
Definition dop_name (γ : DState) (tok : nat) : option nat :=
  match oplog ΣR γ tok with
  | Some a => match (a : ROp nat nat) with Register _ _ x _ => Some x | Lookup _ _ _ => None end
  | None => None
  end.

(** Readers, so the driver never looks inside the service's types. *)

(** The binding of [k]: its owner, and the value registered under each of [xs]. *)
Definition dbinding (γ : DState) (k : nat) (xs : list nat) : option (nat * list (option nat)) :=
  match binds ΣR γ k with
  | Some b => Some (owner ΣR b, map (fun x => (bst ΣR b : St ΣR) x) xs)
  | None => None
  end.

(** The next instruction of a program: 0 done, 1 fail, 2 op [k; x; v] (or
    [k] for a lookup), 3 provide [k], 4 spawn [c]. *)
Definition dinstr (P : DProg) : nat * list nat :=
  match P with
  | PDone => (0, [])
  | PFail => (1, [])
  | POp k a _ =>
      match (a : ROp nat nat) with
      | Register _ _ x v => (2, [k; x; v])
      | Lookup _ _ _ => (2, [k])
      end
  | PProvide k _ _ => (3, [k])
  | PSpawn c _ => (4, [c])
  end.

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extraction Language OCaml.
Set Extraction Output Directory "difftest/calc".
Extraction "calculus.ml"
  dinit dstep denabled dop dprovide dspawn ddone dfail dcomp dop_name dbinding dinstr
  fibers binds next life comp parent disposed pid owner bst.
