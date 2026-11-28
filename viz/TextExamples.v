(** * The computed examples, as S-expressions

    The examples of [Examples/Basic.v], [errors/theories/Admit.v],
    [errors/theories/Queue.v] and [errors/theories/ViewFail.v], printed with
    [Text.v]. The label lists are the ones of those files (by name where the
    file names them: [Admit.drain], [ViewFail.schedA], [ViewFail.schedB]);
    the step functions are theirs ([step], [astep], [qstep], [vstep]).

    Read one with, e.g., [Eval vm_compute in basic_text.] in an IDE;
    viz/text.sh writes all of them to viz/text/*.sexp. *)

From Stdlib Require Import List PeanoNat String.
From Cordis Require Import Prelude Service Calculus Services.Registry Examples.Basic.
From CordisErr Require Import Admit Queue ViewFail.
From CordisViz Require Import Text.
Import ListNotations.
Open Scope string_scope.

(** ** Printers for the registry instance *)

Definition skey (k : nat) : sexp := Sym (if Nat.eqb k tools then "tools" else "k" ++ nat_str k).

Definition sreg (xs : list nat) (s : St ΣR) : list sexp :=
  flat_map (fun x => match (s : RSt nat nat) x with
                     | Some v => [L [Num x; Num v]]
                     | None => [] end) xs.

Definition sop (a : Op ΣR) : sexp :=
  match (a : ROp nat nat) with
  | Register _ _ x v => L [Sym "register"; Num x; Num v]
  | Lookup _ _ x => L [Sym "lookup"; Num x]
  end.

Definition xs : list nat := [7].

(** ** The four step functions, as printers

    [cname] names the components, [comps] lists them for the comparison. *)
Section Printers.
  Variable prog : nat -> @Component nat ΣR nat.
  Variable cname : nat -> sexp.
  Variable comps : list nat.

  Local Notation St := (@Calculus.State nat ΣR nat).
  Local Notation Lb := (@Calculus.Label nat).

  Definition core_text (title : string) (ls : list Lb) : string :=
    run_text ΣR prog skey cname (sreg xs) sop [tools] St Lb
      (step Nat.eq_dec ΣR prog) (fun γ => γ) (slabel cname) (fun _ => [])
      (fun ℓ => ℓ) (fun _ => []) title S0 ls.
  Definition core_sum (ls : list Lb) :=
    summary ΣR prog skey cname (sreg xs) sop [tools] St Lb
      (step Nat.eq_dec ΣR prog) (fun γ => γ) (slabel cname) (fun _ => [])
      (fun ℓ => ℓ) (fun _ => []) S0 ls.

  (** Cordis's admission: [O-Insert] does not check conflicts. *)
  Definition admit_text (title : string) (ls : list Lb) : string :=
    run_text ΣR prog skey cname (sreg xs) sop [tools] St Lb
      (astep Nat.eq_dec ΣR prog) (fun γ => γ) (slabel cname) (fun _ => [])
      (fun ℓ => ℓ) (fun _ => []) title S0 ls.
  Definition admit_sum (ls : list Lb) :=
    summary ΣR prog skey cname (sreg xs) sop [tools] St Lb
      (astep Nat.eq_dec ΣR prog) (fun γ => γ) (slabel cname) (fun _ => [])
      (fun ℓ => ℓ) (fun _ => []) S0 ls.

  (** The admission queue. *)
  Definition qlabel (ℓ : @QLabel nat) : sexp :=
    match ℓ with
    | QIns c => L [Sym "QIns"; cname c]
    | QCancel t => L [Sym "QCancel"; Num t]
    | QAdmit => L [Sym "QAdmit"]
    | QCore ℓ => slabel cname ℓ
    end.
  (** [(queue (ticket comp) ...)], head first. *)
  Definition qextra (qs : @QState nat ΣR nat) : list sexp :=
    [L (Sym "queue" :: map (fun '(t, c) => L [Num t; cname c]) (queue ΣR qs))].
  Definition queue_text (title : string) (ls : list (@QLabel nat)) : string :=
    run_text ΣR prog skey cname (sreg xs) sop [tools] (@QState nat ΣR nat) (@QLabel nat)
      (qstep Nat.eq_dec ΣR prog (fun _ => true)) (core ΣR) qlabel qextra
      QCore (fun _ => [QAdmit]) title (qinit ΣR) ls.
  Definition queue_sum (ls : list (@QLabel nat)) :=
    summary ΣR prog skey cname (sreg xs) sop [tools] (@QState nat ΣR nat) (@QLabel nat)
      (qstep Nat.eq_dec ΣR prog (fun _ => true)) (core ΣR) qlabel qextra
      QCore (fun _ => [QAdmit]) (qinit ΣR) ls.

  (** Failures scoped to their view: the recorded view of each fiber. *)
  Definition vlabel_s (ℓ : @VLabel nat) : sexp :=
    match ℓ with VCore ℓ => slabel cname ℓ | VClear n => L [Sym "VClear"; Num n] end.
  (** [(fview n pair ...)]: the view [n] last unloaded from. *)
  Definition vextra (vs : @VState nat ΣR nat) : list sexp :=
    flat_map (fun n => match fview ΣR vs n with
                       | Some w => [L (Sym "fview" :: Num n :: sview skey w)]
                       | None => [] end) (names ΣR (vcore ΣR vs)).
  Definition view_text (title : string) (ls : list (@VLabel nat)) : string :=
    run_text ΣR prog skey cname (sreg xs) sop [tools] (@VState nat ΣR nat) (@VLabel nat)
      (vstep Nat.eq_dec ΣR prog) (vcore ΣR) vlabel_s vextra
      VCore (fun vs => map VClear (names ΣR (vcore ΣR vs))) title (vinit ΣR) ls.
  Definition view_sum (ls : list (@VLabel nat)) :=
    summary ΣR prog skey cname (sreg xs) sop [tools] (@VState nat ΣR nat) (@VLabel nat)
      (vstep Nat.eq_dec ΣR prog) (vcore ΣR) vlabel_s vextra
      VCore (fun vs => map VClear (names ΣR (vcore ΣR vs))) (vinit ΣR) ls.

  Definition compare := compare_text ΣR skey cname (sreg xs) [tools] comps Nat.eqb.
End Printers.

(** ** [Examples/Basic.v] *)

Definition cnameEx (c : nat) : sexp := Sym match c with 0 => "provider" | _ => "consumer" end.

(** Loading, unloading under the guard, re-providing; the two refused
    labels are [consumer_waits] and [provider_blocked]. *)
Definition basic_labels : list (@Calculus.Label nat) :=
  [OInsert 0; OInsert 1; LBegin 1;
   LBegin 0; LStep 0; LStep 0;
   LBegin 1; LStep 1; LStep 1;
   ODispose 0; LLeave 0; LLeave 1; LUndo 0;
   LUndo 1; LUnloaded 1; LUndo 0; LUnloaded 0; LRemove 0;
   OInsert 0; LBegin 4; LStep 4; LStep 4;
   LBegin 1; LStep 1; LStep 1].

Definition basic_text := core_text progEx cnameEx "Basic: lifecycle" basic_labels.

Definition divert_labels : list (@Calculus.Label nat) :=
  [OInsert 0; OInsert 1;
   LBegin 0; LStep 0; LStep 0;
   LBegin 1; ODispose 0; LLeave 0;
   LDivert 1; LUnloaded 1;
   LUndo 0; LUnloaded 0; LRemove 0].

Definition divert_text := core_text progEx cnameEx "Basic: divert" divert_labels.

(** The same two inputs, the second before or after the provider loads:
    different names, the same final state up to renaming. *)
Definition together : list (@Calculus.Label nat) :=
  [OInsert 0; OInsert 1; LBegin 0; LStep 0; LStep 0; LBegin 1; LStep 1; LStep 1].
Definition apart : list (@Calculus.Label nat) :=
  [OInsert 0; LBegin 0; LStep 0; LStep 0; OInsert 1; LBegin 2; LStep 2; LStep 2].

Definition interleave_text :=
  compare cnameEx [0; 1] "together" "apart" (core_sum progEx cnameEx together) (core_sum progEx cnameEx apart).

(** ** cordiverse/cordis#358 ([Admit.v], [Queue.v]) *)

(** Load both, dispose the provider while the consumer holds it, insert a
    new provider. *)
Definition c358_prefix : list (@Calculus.Label nat) :=
  [OInsert 0; OInsert 1;
   LBegin 0; LStep 0; LStep 0;
   LBegin 1; LStep 1; LStep 1;
   ODispose 0; LLeave 0; LLeave 1;
   OInsert 0].

(** [Admit.early], then the two probes of [early_stuck]. *)
Definition early_labels := (c358_prefix ++ [LBegin 4; LStep 4; LUnloaded 4] ++ drain ++ [LBegin 1; LBegin 4])%list.
(** [Admit.late]. *)
Definition late_labels := (c358_prefix ++ drain ++ [LBegin 4; LStep 4; LStep 4; LBegin 1; LStep 1; LStep 1])%list.
(** The core: the insertion is refused ([core_refuses]); the orchestrator
    retries after the old fiber is removed. *)
Definition core358_labels := (c358_prefix ++ drain ++ [OInsert 0; LBegin 4; LStep 4; LStep 4; LBegin 1; LStep 1; LStep 1])%list.
(** [Queue.q_requested], the refused [QAdmit] of [q358_blocked], then [Queue.q_done]. *)
Definition queue358_labels : list (@QLabel nat) :=
  [QIns 0; QAdmit; QIns 1; QAdmit;
   QCore (LBegin 0); QCore (LStep 0); QCore (LStep 0);
   QCore (LBegin 1); QCore (LStep 1); QCore (LStep 1);
   QCore (ODispose 0); QCore (LLeave 0); QCore (LLeave 1);
   QIns 0; QAdmit;
   QCore (LUndo 1); QCore (LUnloaded 1); QCore (LUndo 0);
   QCore (LUnloaded 0); QCore (LRemove 0);
   QAdmit; QCore (LBegin 4); QCore (LStep 4); QCore (LStep 4);
   QCore (LBegin 1); QCore (LStep 1); QCore (LStep 1)].

Definition early_text := admit_text progEx cnameEx "#358 early (astep)" early_labels.
Definition late_text := admit_text progEx cnameEx "#358 late (astep)" late_labels.
Definition core358_text := core_text progEx cnameEx "#358 core (step)" core358_labels.
Definition queue358_text := queue_text progEx cnameEx "#358 queue (qstep)" queue358_labels.

Definition early_late_text :=
  compare cnameEx [0; 1] "early (astep)" "late (astep)" (admit_sum progEx cnameEx early_labels) (admit_sum progEx cnameEx late_labels).
Definition early_queue_text :=
  compare cnameEx [0; 1] "early (astep)" "queue (qstep)" (admit_sum progEx cnameEx early_labels) (queue_sum progEx cnameEx queue358_labels).

(** ** A failure that outlives its reason ([ViewFail.v]) *)

Definition cnameVF (c : nat) : sexp :=
  Sym match c with 0 => "provider7" | 1 => "consumer" | _ => "provider" end.

(** [schedA] with the probe of [core_stuck]. *)
Definition schedA_probe := (schedA ++ [LBegin 1])%list.
(** The schedule of [view_agrees]. *)
Definition schedA_view : list (@VLabel nat) :=
  (map VCore schedA ++ [VClear 1; VCore (LBegin 1); VCore (LStep 1); VCore (LStep 1)])%list.

Definition vfA_text := core_text progVF cnameVF "ViewFail A (step)" schedA_probe.
Definition vfB_text := core_text progVF cnameVF "ViewFail B (step)" schedB.
Definition vfA_view_text := view_text progVF cnameVF "ViewFail A (vstep)" schedA_view.

Definition vf_core_text :=
  compare cnameVF [0; 1; 2] "A (step)" "B (step)" (core_sum progVF cnameVF schedA_probe) (core_sum progVF cnameVF schedB).
Definition vf_view_text :=
  compare cnameVF [0; 1; 2] "A (vstep)" "B (vstep)" (view_sum progVF cnameVF schedA_view) (view_sum progVF cnameVF (map VCore schedB)).
