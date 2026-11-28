(** * The calculus and its error-handling variants, extracted for the visualizer

    The instance of [Examples/Basic.v]: natural-number keys, the registry of
    [Services/Registry.v] (names and values are natural numbers) as the one
    service, components named by natural numbers. The component table stays
    a parameter: the driver (viz/calc/trace.ml) builds it from a scenario
    file.

    Four step functions, all the calculus's own:
    - [xstep]: the core ([Calculus.v]);
    - [xastep]: Cordis's admission ([errors/theories/Admit.v]: [O-Insert]
      does not check conflicts);
    - [xqstep]: the admission queue ([errors/theories/Queue.v]);
    - [xvstep]: failures scoped to their view ([errors/theories/ViewFail.v]).

    The rest only reads states, so the driver never looks inside the
    service's types. Nothing here is proved.

    Build from the repository root (after the core and errors/ are built):
      coqc -Q theories Cordis -Q errors/theories CordisErr viz/Extract.v *)

From Stdlib Require Import List PeanoNat.
From Cordis Require Import Prelude Service Calculus Services.Registry Examples.Basic.
From CordisErr Require Import Admit Queue ViewFail.
Import ListNotations.

Definition XComp := @Component nat ΣR nat.
Definition XProg := @Prog nat ΣR nat.
Definition XState := @State nat ΣR nat.
Definition XLabel := @Label nat.
Definition XQState := @QState nat ΣR nat.
Definition XQLabel := @QLabel nat.
Definition XVState := @VState nat ΣR nat.
Definition XVLabel := @VLabel nat.

Definition xinit : XState := @init nat ΣR nat.
Definition xqinit : XQState := qinit ΣR.
Definition xvinit : XVState := vinit ΣR.

Definition xstep (prog : nat -> XComp) (γ : XState) (ℓ : XLabel) : option XState :=
  step Nat.eq_dec ΣR prog γ ℓ.
Definition xastep (prog : nat -> XComp) (γ : XState) (ℓ : XLabel) : option XState :=
  astep Nat.eq_dec ΣR prog γ ℓ.
(** Every component may be inserted by the orchestrator ([rootb] is
    constantly true), as in the computed example of [Queue.v]. *)
Definition xqstep (prog : nat -> XComp) (qs : XQState) (ℓ : XQLabel) : option XQState :=
  qstep Nat.eq_dec ΣR prog (fun _ => true) qs ℓ.
Definition xvstep (prog : nat -> XComp) (vs : XVState) (ℓ : XVLabel) : option XVState :=
  vstep Nat.eq_dec ΣR prog vs ℓ.

(** Program constructors at this instance. *)
Definition xop (k : nat) (x v : nat) (P : XProg) : XProg :=
  POp (Σ := ΣR) k (Register nat nat x v) (fun _ => P).
Definition xlookup (k : nat) (x : nat) (P : XProg) : XProg :=
  POp (Σ := ΣR) k (Lookup nat nat x) (fun _ => P).
Definition xprovide (k : nat) (entries : list (nat * nat)) (P : XProg) : XProg :=
  PProvide (Σ := ΣR) k (fold_right (A := St ΣR) (fun '(x, v) s => upd nat nat Nat.eq_dec s x (Some v))
                         (fun _ => None) entries) P.
Definition xspawn (c : nat) (P : XProg) : XProg := PSpawn (Σ := ΣR) c P.
Definition xdone : XProg := PDone (Σ := ΣR).
Definition xfail : XProg := PFail (Σ := ΣR).
Definition xcomp (deps provs : list nat) (body : XProg) : XComp :=
  mkComponent deps provs body [].

(** ** Readers *)

(** The extended states' core state, queue and recorded views. *)
Definition xq_core (qs : XQState) : XState := core ΣR qs.
Definition xq_queue (qs : XQState) : list (nat * nat) := queue ΣR qs.
Definition xv_core (vs : XVState) : XState := vcore ΣR vs.
Definition xv_fview (vs : XVState) (n : nat) : option (@View nat) := fview ΣR vs n.

(** One instruction: 0 done, 1 fail, 2 register [k; x; v], 3 provide [k],
    4 spawn [c], 5 lookup [k; x]. *)
Definition xinstr (P : XProg) : nat * list nat :=
  match P with
  | PDone => (0, [])
  | PFail => (1, [])
  | POp k a _ =>
      match (a : ROp nat nat) with
      | Register _ _ x v => (2, [k; x; v])
      | Lookup _ _ x => (5, [k; x])
      end
  | PProvide k _ _ => (3, [k])
  | PSpawn c _ => (4, [c])
  end.

(** The rest of a program, instruction by instruction, at most [fuel] of
    them. A registration's outcome is always [None]; a lookup's outcome
    depends on the state, so the listing stops after it. *)
Fixpoint xlisting (fuel : nat) (P : XProg) : list (nat * list nat) :=
  match fuel with
  | 0 => []
  | S fuel' =>
      match P with
      | PDone | PFail => [xinstr P]
      | POp _ a κ =>
          match (a : ROp nat nat) with
          | Register _ _ _ _ => xinstr P :: xlisting fuel' (κ None)
          | Lookup _ _ _ => [xinstr P]
          end
      | PProvide _ _ P' | PSpawn _ P' => xinstr P :: xlisting fuel' P'
      end
  end.

(** The initial entries of a provision, at the names [xs]. *)
Definition xprov_entries (P : XProg) (xs : list nat) : list (option nat) :=
  match P with
  | PProvide _ s _ => map (fun x => (s : St ΣR) x) xs
  | _ => []
  end.

(** The name an [UOp] item registered, from the ghost operation log. *)
Definition xop_name (γ : XState) (tok : nat) : option nat :=
  match oplog ΣR γ tok with
  | Some a => match (a : ROp nat nat) with Register _ _ x _ => Some x | Lookup _ _ _ => None end
  | None => None
  end.

(** The binding of [k]: pid, owner, and the value registered under each of [xs]. *)
Definition xbinding (γ : XState) (k : nat) (xs : list nat) : option (nat * nat * list (option nat)) :=
  match binds ΣR γ k with
  | Some b => Some (pid ΣR b, owner ΣR b, map (fun x => (bst ΣR b : St ΣR) x) xs)
  | None => None
  end.

Definition xtarget (prog : nat -> XComp) (γ : XState) (n : nat) : option (@View nat) :=
  target ΣR prog γ n.

(** The guard on unloading holds for [n]: some other installed fiber still
    resolves one of its provisions. *)
Definition xheld (γ : XState) (n : nat) : bool :=
  match fibers ΣR γ n with
  | Some f => held ΣR γ n (acc_of ΣR (life ΣR f))
  | None => false
  end.

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extraction Language OCaml.
Set Extraction Output Directory "viz/calc".
Extraction "calculus.ml"
  xinit xqinit xvinit xstep xastep xqstep xvstep
  xop xlookup xprovide xspawn xdone xfail xcomp
  xq_core xq_queue xv_core xv_fview
  xinstr xlisting xprov_entries xop_name xbinding xtarget xheld
  lifecycle_labels fibers next life comp parent disposed.
