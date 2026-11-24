(** * Worked examples for the extensions

    Two small systems on the name-keyed registry, run by computation as in
    [Examples/Basic.v]. Each also discharges the obligations its extension's
    theorems ask of the component table, so those hypotheses can hold
    together.

    1. Optional dependencies. Plugin B optionally uses the service [llm]
       that plugin A provides. With [llm] present B registers tool 7 ↦ 1
       and writes to [llm]; without it, tool 7 ↦ 0. Whether A or B starts
       first, the run ends in the same state, with B on the [llm] variant:
       when A arrives late, B reloads.

    2. Intersection lifetime. A plugin attaches a restriction to agent 3's
       context (an entry in the agent's registry). When the agent ends, its
       unload is held until the restriction has gone; when the plugin ends,
       the restriction goes first and the agent keeps running. *)

From Stdlib Require Import List PeanoNat Bool Lia.
From Cordis Require Import Prelude Service Calculus Preservation Recovery Progress Termination
  Confluence Services.Registry.
From Cordis Require Import Ext.Optional Ext.OptProgress Ext.Intersect Ext.IntersectLive.
Import ListNotations.

Definition ΣR : Service := Registry nat nat Nat.eq_dec.
Definition empty_reg : St ΣR := fun _ => None.

Definition reg_at {C : Type} (γ : @State nat ΣR C) (k x : nat) : option (option nat) :=
  match binds ΣR γ k with Some b => Some (bst ΣR b x) | None => None end.

Definition tag {C : Type} (γ : @State nat ΣR C) (n : nat) : option nat :=
  match fibers ΣR γ n with
  | Some f => Some match life ΣR f with
                   | Inactive _ _ => 0 | Loading _ _ _ _ => 1
                   | Active _ _ _ => 2 | Unloading _ _ _ _ => 3
                   end
  | None => None
  end.

(** ** 1. Optional dependencies *)
Module OptEx.
  Definition llm : nat := 0.
  Definition tools : nat := 1.

  (** [true] is A, [false] is B. *)
  Definition bodyB (T : nat -> bool) : @Prog nat ΣR bool :=
    PProvide (Σ := ΣR) tools empty_reg
      (if T llm
       then POp (Σ := ΣR) llm (Register nat nat 5 5) (fun _ => POp (Σ := ΣR) tools (Register nat nat 7 1) (fun _ => PDone))
       else POp (Σ := ΣR) tools (Register nat nat 7 0) (fun _ => PDone)).

  Definition xprogO (c : bool) : @XComponent nat ΣR bool :=
    if c then mkX ΣR [] [] [llm] (fun _ => PProvide (Σ := ΣR) llm empty_reg PDone) []
    else mkX ΣR [] [llm] [tools] bodyB [].

  Definition xrunO := xrun Nat.eq_dec ΣR xprogO.
  Definition xstepO := xstep Nat.eq_dec ΣR xprogO.
  Definition S0 : @State nat ΣR (bool * list nat) := @init nat ΣR (bool * list nat).

  (** Tags of A and B, tool 7, the entry B wrote to [llm], and B's presence. *)
  Definition obs (o : option (@State nat ΣR (bool * list nat))) :=
    match o with
    | Some γ => Some (tag γ 0, tag γ 1, reg_at γ tools 7, reg_at γ llm 5,
                      option_map (fun f => snd (Calculus.comp ΣR f)) (fibers ΣR γ 1))
    | None => None
    end.

  (** No lifecycle label applies to A or B. *)
  Definition stuck (o : option (@State nat ΣR (bool * list nat))) : bool :=
    match o with
    | Some γ => negb (existsb (fun ℓ => match xstepO γ ℓ with Some _ => true | None => false end)
                              (lifecycle_labels 0 ++ lifecycle_labels 1))
    | None => false
    end.

  (** A first: B begins with [llm] present. *)
  Definition a_first :=
    xrunO S0 [OInsert true; OInsert false;
              LBegin 0; LStep 0; LStep 0;
              LBegin 1; LStep 1; LStep 1; LStep 1; LStep 1].

  Example a_first_obs : obs a_first = Some (Some 2, Some 2, Some (Some 1), Some (Some 5), Some [llm]).
  Proof. reflexivity. Qed.
  Example a_first_stuck : stuck a_first = true.
  Proof. reflexivity. Qed.

  (** B first: it loads the variant without [llm]. *)
  Definition b_first_early :=
    xrunO S0 [OInsert true; OInsert false;
              LBegin 1; LStep 1; LStep 1; LStep 1;
              LBegin 0; LStep 0; LStep 0].

  Example b_first_early_obs :
    obs b_first_early = Some (Some 2, Some 2, Some (Some 0), Some None, Some []).
  Proof. reflexivity. Qed.

  (** [llm] has appeared: B's core target has not changed, but B must
      reload; X-Leave applies, as the core's L-Leave would not. *)
  Example b_must_reload :
    match b_first_early with
    | Some γ => (match xstepO γ (LLeave 1) with Some _ => true | None => false end,
                 match step Nat.eq_dec ΣR (prog' Nat.eq_dec ΣR xprogO) γ (LLeave 1) with
                 | Some _ => true | None => false end)
    | None => (false, false)
    end = (true, false).
  Proof. reflexivity. Qed.

  (** B reloads: its registration is undone, its provision withdrawn, and it
      begins again on the [llm] variant. *)
  Definition b_first :=
    match b_first_early with
    | Some γ => xrunO γ [LLeave 1; LUndo 1; LUndo 1; LUnloaded 1;
                         LBegin 1; LStep 1; LStep 1; LStep 1; LStep 1]
    | None => None
    end.

  Example b_first_obs : obs b_first = Some (Some 2, Some 2, Some (Some 1), Some (Some 5), Some [llm]).
  Proof. reflexivity. Qed.
  Example b_first_stuck : stuck b_first = true.
  Proof. reflexivity. Qed.

  (** The two schedules end in the same observable state. *)
  Example schedules_agree : obs a_first = obs b_first.
  Proof. reflexivity. Qed.

  (** *** The obligations *)
  Definition rk (c : bool) : nat := if c then 0 else 1.

  Lemma no_spawn c T c' : ~ SpawnIn ΣR c' (xbody ΣR (xprogO c) T).
  Proof.
    destruct c; cbn; [intros H; inversion H; subst; inversion H1|].
    unfold bodyB; intros H; inversion H; subst.
    destruct (T llm); inversion H1; subst;
      repeat match goal with
             | Hs : SpawnIn _ _ (_ _) |- _ => inversion Hs; subst; clear Hs
             end.
  Qed.

  Lemma rank_ok c c' : XAbove ΣR xprogO c c' -> rk c < rk c'.
  Proof.
    intros [(k & Hp & Hd)|[(T & Hs)|Hr]].
    - destruct c, c'; cbn in Hp, Hd |- *; try lia;
        destruct Hp as [<-|[]]; unfold llm, tools in *; cbn in Hd; intuition discriminate.
    - exfalso; exact (no_spawn c T c' Hs).
    - destruct c; cbn in Hr; destruct Hr.
  Qed.

  Lemma rank_bnd c : rk c <= 1.
  Proof. destruct c; cbn; lia. Qed.

  Lemma bounded c T : Bounded ΣR 4 (xbody ΣR (xprogO c) T).
  Proof.
    destruct c; cbn; [repeat constructor|].
    unfold bodyB; destruct (T llm); repeat constructor.
  Qed.

  Lemma total c T k : In k (xprovs ΣR (xprogO c)) -> AllDoneProv ΣR k (xbody ΣR (xprogO c) T).
  Proof.
    destruct c; cbn; intros [<-|[]]; [apply adp_here|]; unfold bodyB; apply adp_here.
  Qed.

  Lemma no_opt_child c c' : XSpawns ΣR xprogO c c' -> xopt ΣR (xprogO c') = [].
  Proof.
    intros [(T & Hs)|Hr]; [exfalso; exact (no_spawn c T c' Hs)|].
    destruct c; cbn in Hr; destruct Hr.
  Qed.
End OptEx.

(** ** 2. Intersection lifetime *)
Module AgentEx.
  Inductive Comp : Type := Agent (a : nat) | Plug | Restrict (a : nat).

  (** Agent [a]'s context is the key [a]. *)
  Definition iprogI (c : Comp) : @IComponent nat ΣR Comp nat :=
    match c with
    | Agent a => mkI ΣR [] [a] (PProvide (Σ := ΣR) a empty_reg PDone) []
    | Plug => mkI ΣR [] [] PDone [fun a => Restrict a]
    | Restrict a => mkI ΣR [a] [] (POp (Σ := ΣR) a (Register nat nat 0 1) (fun _ => PDone)) []
    end.

  Definition irunA := irun Nat.eq_dec ΣR iprogI.
  Definition istepA := istep Nat.eq_dec ΣR iprogI.
  Definition S0 : @State nat ΣR Comp := @init nat ΣR Comp.

  Definition obs (o : option (@State nat ΣR Comp)) :=
    match o with
    | Some γ => Some (tag γ 0, tag γ 1, tag γ 3, reg_at γ 3 0)
    | None => None
    end.

  (** Agent 3 (fiber 0) and the plugin (fiber 1) load; an event about agent 3
      runs the plugin's handler at payload 3, giving the restriction fiber 3. *)
  Definition attached :=
    irunA S0 [ICore (OInsert (Agent 3)); ICore (OInsert Plug);
              ICore (LBegin 0); ICore (LStep 0); ICore (LStep 0);
              ICore (LBegin 1); ICore (LStep 1);
              IReact 1 0 3;
              ICore (LBegin 3); ICore (LStep 3); ICore (LStep 3)].

  Example attached_obs : obs attached = Some (Some 2, Some 2, Some 2, Some (Some 1)).
  Proof. reflexivity. Qed.

  (** *** The agent ends *)
  Definition agent_leaving :=
    match attached with
    | Some γ => irunA γ [ICore (ODispose 0); ICore (LLeave 0)]
    | None => None
    end.

  (** The agent's unload is held: it undoes nothing while the restriction
      still resolves its context. *)
  Example agent_held :
    match agent_leaving with Some γ => istepA γ (ICore (LUndo 0)) | None => None end = None.
  Proof. reflexivity. Qed.

  (** The restriction's target is gone, so it leaves and is undone first. *)
  Definition effect_gone :=
    match agent_leaving with
    | Some γ => irunA γ [ICore (LLeave 3); ICore (LUndo 3); ICore (LUnloaded 3)]
    | None => None
    end.

  Example effect_gone_obs : obs effect_gone = Some (Some 3, Some 2, Some 0, Some None).
  Proof. reflexivity. Qed.

  (** Only now does the agent's context go. *)
  Definition agent_gone :=
    match effect_gone with
    | Some γ => irunA γ [ICore (LUndo 0); ICore (LUnloaded 0); ICore (LRemove 0)]
    | None => None
    end.

  Example agent_gone_obs : obs agent_gone = Some (None, Some 2, Some 0, None).
  Proof. reflexivity. Qed.

  (** *** The plugin ends instead *)
  Definition plugin_gone :=
    match attached with
    | Some γ => irunA γ [ICore (ODispose 1); ICore (LLeave 1); ICore (LRetireChild 1);
                         ICore (LLeave 3); ICore (LUndo 3); ICore (LUnloaded 3); ICore (LRemove 3);
                         ICore (LUndo 1); ICore (LUnloaded 1); ICore (LRemove 1)]
    | None => None
    end.

  (** The restriction is undone and removed with the plugin; the agent keeps
      running, its context intact. *)
  Example plugin_gone_obs : obs plugin_gone = Some (Some 2, None, None, Some None).
  Proof. reflexivity. Qed.

  (** *** The obligations *)
  Definition rk (c : Comp) : nat := match c with Restrict _ => 1 | _ => 0 end.

  Lemma rank_ok c c' : IAbove ΣR iprogI c c' -> rk c < rk c'.
  Proof.
    intros [(k & Hp & Hd)|[Hs|(h & e & Hh & ->)]].
    - destruct c, c'; cbn in Hp, Hd |- *; try lia; tauto.
    - exfalso; destruct c; cbn in Hs; inversion Hs; subst;
        repeat match goal with Hs : SpawnIn _ _ _ |- _ => inversion Hs; subst; clear Hs end.
    - destruct c; cbn in Hh; try contradiction.
      destruct Hh as [<-|[]]; cbn; lia.
  Qed.

  Lemma rank_bnd c : rk c <= 1.
  Proof. destruct c; cbn; lia. Qed.

  Lemma bounded c : Bounded ΣR 1 (ibody ΣR (iprogI c)).
  Proof. destruct c; cbn; repeat constructor. Qed.
End AgentEx.
