(** * Executions as S-expressions

    Everything here is a Rocq function returning an S-expression or its
    printed form, so a picture of an execution is just
    [Eval vm_compute in ...]: no extraction, no driver. The output is a
    sequence of S-expressions that Racket's [read] takes as it is (symbols,
    numbers, strings, [#t] / [#f]), so it can be processed further (diffed,
    checked, turned into a page).

    The rendering is generic over the calculus's parameters (keys, service,
    components) and over the step function (the core [step], or a variant
    with a core part: [astep], [qstep], [vstep]). The caller gives printers
    for keys, components, service states and operations, and the keys and
    components to show.

    A state is a set of items: one [(fiber ...)] per fiber, one
    [(bind ...)] per bound key, plus the variant's own items ([(queue ...)],
    [(fview ...)]). Each item carries all the facts of its fiber or binding,
    so a step is the items it removed and the items it added:

      (run "title")
      (init item ... (enabled label ...))
      (step i label (del item ...) (add item ...) (enabled label ...))
      (step i label refused)                      [step] returned [None]
      (final item ... (quiet #t))

    The state after a step is the state before it, minus [del], plus [add].
    Two runs side by side:

      (compare "a" "b")
      (labels a label ...)   (labels b label ...)
      (final a sig ...)      (final b sig ...)
      (differ (comp c) ... (key k) ...)
      (same #f)

    where the final states are taken up to renaming: [(comp c life ...)]
    lists the fibers of component [c] in name order, [(key k ...)] gives the
    binding with the owner's component instead of its name. Names and pids
    come from one counter, so they differ between schedules.

    Nothing here is proved, and nothing in theories/ or errors/ imports it. *)

From Stdlib Require Import List PeanoNat Bool String Ascii.
From Cordis Require Import Prelude Service Calculus.
Import ListNotations.
Open Scope string_scope.

(** ** S-expressions *)

Inductive sexp : Type :=
| Sym (s : string)
| Num (n : nat)
| Str (s : string)
| Bool (b : bool)
| L (l : list sexp).

Definition nl : string := String (ascii_of_nat 10) EmptyString.
Definition dq : string := String (ascii_of_nat 34) EmptyString.

Fixpoint digits (fuel n : nat) (acc : string) : string :=
  match fuel with
  | 0 => acc
  | S f =>
      let acc' := String (ascii_of_nat (48 + Nat.modulo n 10)) acc in
      match Nat.div n 10 with 0 => acc' | q => digits f q acc' end
  end.

Definition nat_str (n : nat) : string := digits (S n) n "".

(** Display width: UTF-8 continuation bytes take no column. *)
Fixpoint width (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String a s' =>
      let k := nat_of_ascii a in
      (if Nat.leb 128 k && Nat.ltb k 192 then 0 else 1) + width s'
  end.

Fixpoint spaces (n : nat) : string :=
  match n with 0 => "" | S n' => " " ++ spaces n' end.

(** Strings are quoted; the examples' strings contain no quote or backslash. *)
Fixpoint flat (e : sexp) : string :=
  match e with
  | Sym s => s
  | Num n => nat_str n
  | Str s => dq ++ s ++ dq
  | Bool b => if b then "#t" else "#f"
  | L l =>
      "(" ++ (fix go (l : list sexp) : string :=
                match l with
                | [] => ""
                | [x] => flat x
                | x :: r => flat x ++ " " ++ go r
                end) l ++ ")"
  end.

(** Pretty printing: a list that does not fit in [cols] columns keeps its
    leading atoms on the first line and puts every other element on a line
    of its own, indented by two. *)
Definition cols : nat := 120.

Definition is_atom (e : sexp) : bool := match e with L _ => false | _ => true end.

(** A list that does not fit keeps its leading atoms on its first line and
    puts every other element on a line of its own, indented by two. *)
Fixpoint pp (ind : nat) (e : sexp) : string :=
  let f := flat e in
  if Nat.leb (ind + width f) cols then f
  else match e with
       | L l =>
           "(" ++ (fix go (first lead : bool) (l : list sexp) : string :=
                     match l with
                     | [] => ""
                     | x :: r =>
                         if first then pp (ind + 1) x ++ go false (is_atom x) r
                         else if lead && is_atom x then " " ++ flat x ++ go false true r
                         else nl ++ spaces (ind + 2) ++ pp (ind + 2) x ++ go false false r
                     end) true true l ++ ")"
       | _ => f
       end.

(** At the top level a step also keeps its label on the first line:
    [(step 3 (LStep 0)]. *)
Definition pp_top (e : sexp) : string :=
  match e with
  | L (Sym "step" :: i :: lb :: rest) =>
      let f := flat e in
      if Nat.leb (width f) cols then f
      else "(step " ++ flat i ++ " " ++ flat lb ++
           String.concat "" (map (fun x => nl ++ "  " ++ pp 2 x) rest) ++ ")"
  | _ => pp 0 e
  end.

Definition print (es : list sexp) : string := String.concat nl (map pp_top es).

Definition sexp_eqb (a b : sexp) : bool := String.eqb (flat a) (flat b).
Definition mem (x : sexp) (l : list sexp) : bool := existsb (sexp_eqb x) l.

Section Text.
  Context {K : Type} (K_eq_dec : forall x y : K, {x = y} + {x <> y}).
  Context (Σ : Service) {C : Type} (prog : C -> @Component K Σ C).

  (** Printers and what to show. [sst] gives a service state as a list of
      entries. *)
  Variable skey : K -> sexp.
  Variable scomp : C -> sexp.
  Variable sst : St Σ -> list sexp.
  Variable sop : Op Σ -> sexp.
  Variable keys : list K.
  Variable comps : list C.
  Variable C_eqb : C -> C -> bool.

  Local Notation State := (@State K Σ C).
  Local Notation Label := (@Label C).
  Local Notation View := (@View K).

  (** ** One state *)

  (** A view as its pairs; the target ⊥ as [none]. *)
  Definition sview (w : View) : list sexp := map (fun '(k, p) => L [skey k; Num p]) w.
  Definition starget (o : option View) : sexp :=
    L (Sym "target" :: match o with Some w => sview w | None => [Sym "none"] end).

  Definition serr (z : Err) : sexp :=
    Sym match z with EUser => "EUser" | EOp => "EOp" | EUnresolved => "EUnresolved" | EConflict => "EConflict" end.

  Definition sundo (γ : State) (u : @Undo K Σ) : sexp :=
    match u with
    | UOp _ k p tok _ =>
        L [Sym "op"; skey k; Num p; match oplog Σ γ tok with Some a => sop a | None => Sym "?" end]
    | UProv _ k p => L [Sym "prov"; skey k; Num p]
    | USpawn _ m => L [Sym "spawn"; Num m]
    end.

  Definition sinstr (P : @Prog K Σ C) : sexp :=
    match P with
    | PDone => Sym "done"
    | PFail => Sym "fail"
    | POp k a _ => L [Sym "op"; skey k; sop a]
    | PProvide k _ _ => L [Sym "provide"; skey k]
    | PSpawn c _ => L [Sym "spawn"; scomp c]
    end.

  Definition opt (b : bool) (e : sexp) : list sexp := if b then [e] else [].

  (** [(fiber n comp (life Tag [err]) [(parent p)] [disposed] [held]
       [(view ..)] (target ..) [(next instr)] [(acc item ..)])]; the
      accumulator lists its head, the next item to undo, first. *)
  Definition sfiber (γ : State) (n : nat) (f : @Fiber K Σ C) : sexp :=
    let par := match parent Σ f with Some p => [L [Sym "parent"; Num p]] | None => [] end in
    let dsp := opt (disposed Σ f) (Sym "disposed") in
    let tg := starget (target Σ prog γ n) in
    let acc a := L (Sym "acc" :: map (sundo γ) a) in
    let lf t z := L (Sym "life" :: Sym t :: match z with Some z => [serr z] | None => [] end) in
    L ([Sym "fiber"; Num n; scomp (comp Σ f)] ++
       match life Σ f with
       | Inactive _ z => [lf "Inactive" z] ++ par ++ dsp ++ [tg]
       | Loading _ P a w =>
           [lf "Loading" None] ++ par ++ dsp ++ [L (Sym "view" :: sview w); tg; L [Sym "next"; sinstr P]; acc a]
       | Active _ a w => [lf "Active" None] ++ par ++ dsp ++ [L (Sym "view" :: sview w); tg; acc a]
       | Unloading _ a w z =>
           [lf "Unloading" z] ++ par ++ dsp ++ opt (held Σ γ n a) (Sym "held") ++
           [L (Sym "view" :: sview w); tg; acc a]
       end)%list.

  Definition sbind (γ : State) (k : K) : list sexp :=
    match binds Σ γ k with
    | Some b => [L [Sym "bind"; skey k; L [Sym "pid"; Num (pid Σ b)]; L [Sym "owner"; Num (owner Σ b)];
                    L (Sym "entries" :: sst (bst Σ b))]]
    | None => []
    end.

  (** A state as its items, fibers in name order. *)
  Definition sstate (γ : State) : list sexp :=
    (flat_map (fun n => match fibers Σ γ n with Some f => [sfiber γ n f] | None => [] end) (names Σ γ)
     ++ flat_map (sbind γ) keys)%list.

  Definition slabel (ℓ : Label) : sexp :=
    match ℓ with
    | OInsert c => L [Sym "OInsert"; scomp c]
    | ODispose n => L [Sym "ODispose"; Num n]
    | OReset n => L [Sym "OReset"; Num n]
    | ORestart n => L [Sym "ORestart"; Num n]
    | OReact n i => L [Sym "OReact"; Num n; Num i]
    | LBegin n => L [Sym "LBegin"; Num n]
    | LStep n => L [Sym "LStep"; Num n]
    | LDivert n => L [Sym "LDivert"; Num n]
    | LLeave n => L [Sym "LLeave"; Num n]
    | LUndo n => L [Sym "LUndo"; Num n]
    | LRetireChild n => L [Sym "LRetireChild"; Num n]
    | LUnloaded n => L [Sym "LUnloaded"; Num n]
    | LRemove n => L [Sym "LRemove"; Num n]
    end.

  (** ** Executions, for any step function over a state with a core part

      [X] is the state of the variant; [core] reads its core part, [extra]
      gives the items only the variant has, [lift] embeds core labels and
      [more] lists the variant's own lifecycle labels at a state. *)
  Section Run.
    Variables (X Lb : Type) (stepf : X -> Lb -> option X) (core : X -> State).
    Variables (show : Lb -> sexp) (extra : X -> list sexp).
    Variables (lift : Label -> Lb) (more : X -> list Lb).

    Definition items (s : X) : list sexp := (sstate (core s) ++ extra s)%list.

    Definition enabled (s : X) : list Lb :=
      filter (fun l => match stepf s l with Some _ => true | None => false end)
             (map lift (flat_map (@lifecycle_labels C) (names Σ (core s))) ++ more s)%list.

    Definition senabled (s : X) : sexp := L (Sym "enabled" :: map show (enabled s)).

    Definition is_quiet (s : X) : bool := match enabled s with [] => true | _ => false end.

    (** The steps, the label column used by [compare], and the final state. *)
    Fixpoint go (i : nat) (s : X) (ls : list Lb) : list sexp * list sexp * X :=
      match ls with
      | [] => ([], [], s)
      | l :: ls' =>
          match stepf s l with
          | None =>
              let '(t, c, f) := go (S i) s ls' in
              (L [Sym "step"; Num i; show l; Sym "refused"] :: t, L [Sym "refused"; show l] :: c, f)
          | Some s' =>
              let '(t, c, f) := go (S i) s' ls' in
              let old := items s in
              let new := items s' in
              (L [Sym "step"; Num i; show l;
                  L (Sym "del" :: filter (fun x => negb (mem x new)) old);
                  L (Sym "add" :: filter (fun x => negb (mem x old)) new);
                  senabled s'] :: t,
               show l :: c, f)
          end
      end.

    Definition run_sexps (title : string) (s0 : X) (ls : list Lb) : list sexp :=
      let '(t, _, f) := go 1 s0 ls in
      ([L [Sym "run"; Str title]; L (Sym "init" :: items s0 ++ [senabled s0])] ++ t ++
       [L (Sym "final" :: items f ++ [L [Sym "quiet"; Bool (is_quiet f)]])])%list.

    Definition run_text (title : string) (s0 : X) (ls : list Lb) : string :=
      print (run_sexps title s0 ls).

    (** What [compare] needs of a run: its label column, its final core state
        and whether that state is quiet. *)
    Definition summary (s0 : X) (ls : list Lb) : list sexp * State * bool :=
      let '(_, c, f) := go 1 s0 ls in (c, core f, is_quiet f).
  End Run.

  (** ** Two runs side by side *)

  Definition slife (f : @Fiber K Σ C) : sexp :=
    L ((match life Σ f with
        | Inactive _ z => Sym "Inactive" :: match z with Some z => [serr z] | None => [] end
        | Loading _ _ _ _ => [Sym "Loading"]
        | Active _ _ _ => [Sym "Active"]
        | Unloading _ _ _ z => Sym "Unloading" :: match z with Some z => [serr z] | None => [] end
        end) ++ opt (disposed Σ f) (Sym "disposed"))%list.

  Definition of_comp (γ : State) (c : C) : list (@Fiber K Σ C) :=
    flat_map (fun n => match fibers Σ γ n with
                       | Some f => if C_eqb (comp Σ f) c then [f] else []
                       | None => [] end) (names Σ γ).

  Definition signature (γ : State) : list sexp :=
    (map (fun c => L (Sym "comp" :: scomp c :: map slife (of_comp γ c))) comps ++
     map (fun k => L (Sym "key" :: skey k ::
           match binds Σ γ k with
           | Some b =>
               [L [Sym "by"; match fibers Σ γ (owner Σ b) with
                             | Some f => scomp (comp Σ f) | None => Num (owner Σ b) end];
                L (Sym "entries" :: sst (bst Σ b))]
           | None => [Sym "unbound"]
           end)) keys)%list.

  Definition head2 (e : sexp) : sexp :=
    match e with L (a :: b :: _) => L [a; b] | _ => e end.

  Definition compare_sexps (na nb : string)
      (A : list sexp * State * bool) (B : list sexp * State * bool) : list sexp :=
    let '(ca, fa, qa) := A in
    let '(cb, fb, qb) := B in
    let sa := (signature fa ++ [L [Sym "quiet"; Bool qa]])%list in
    let sb := (signature fb ++ [L [Sym "quiet"; Bool qb]])%list in
    let differ := map (fun '(x, _) => head2 x) (filter (fun '(x, y) => negb (sexp_eqb x y)) (combine sa sb)) in
    [L [Sym "compare"; Str na; Str nb];
     L (Sym "labels" :: Sym "a" :: ca); L (Sym "labels" :: Sym "b" :: cb);
     L (Sym "final" :: Sym "a" :: sa); L (Sym "final" :: Sym "b" :: sb);
     L (Sym "differ" :: differ);
     L [Sym "same"; Bool (match differ with [] => true | _ => false end)]].

  Definition compare_text (na nb : string) A B : string := print (compare_sexps na nb A B).
End Text.
