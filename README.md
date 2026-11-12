# cordis-rocq

A Rocq formalization of *A Programming Paradigm for Spatiotemporal Composability*
(Shi, Zhang, Cui), Chapters 3–4, redesigned around the plugin runtime Cordis and
its use in dsh (DeepSeek Harness). The aim is to verify the lifecycle properties
of dsh plugins; plugins' business logic is out of scope.

- [docs/DESIGN.md](docs/DESIGN.md): principles, differences from the paper and
  from Cordis (with proposals for Cordis), roadmap.
- [docs/RULES.md](docs/RULES.md): the calculus and its proved properties.
- [docs/EMIT-AUDIT.md](docs/EMIT-AUDIT.md): how dsh dispatches events, checked
  against the confluence theorem's assumptions.
- [docs/PLUGIN-AUDIT.md](docs/PLUGIN-AUDIT.md): the six most downloaded third-party
  dsh plugins, checked against the component obligations, and what the model lacks.

Build (Rocq 9.1):

```sh
sh build.sh
```

## Layout

| File | Contents |
|---|---|
| `Prelude.v` | composition, monoids |
| `Twisted.v`, `EffectFun.v`, `Independence.v` | §3.1 (map below) |
| `Service.v` | service specifications: well-behaved operations, revert-independence, commutation, omission |
| `Observe.v` | observational equivalence: indistinguishability is the coarsest admissible equivalence (§3.3.2) |
| `Services/Registry.v`, `Services/EventBus.v` | a name-keyed registry; an ordered event bus with tokens |
| `Services/RegistryConf.v`, `Services/Listeners.v` | the registry under the confluence hypotheses; listener registration up to order |
| `Calculus.v` | the lifecycle calculus: programs, fibers, bindings, the step function |
| `Examples/Basic.v` | computed runs |
| `Preservation.v` … `Termination.v` | well-formedness, ordering, recovery, progress, termination |
| `Confluence.v` | confluence of control states (no spawn) |
| `ServiceSeq.v` | replaying operations on one service: removal, permutation |
| `StateInv.v`, `Episode.v` | confluence parts 1–2: the single-run invariant; ideal traces |
| `StateConf.v`, `SpawnConf.v` | confluence parts 3–4: service states without spawn; systems with spawn |
| `Dynamic.v` | confluence part 5: orchestration interleaved with lifecycle steps; static assembly |
| `Runtime.v` | runtime effects: a reaction is a child fiber; disposing it is exact |
| `Compose.v` | bundled service hypotheses, the generic confluence theorem, sums of services |
| `Bridge.v` | §3 to §4: §3.1 read up to ≃ and partially; programs as effect functions (⟦·⟧); key commutativity (Def 39) implies the calculus's hypotheses |
| `Examples/Composed.v` | a registry and listeners side by side |
| `Derived.v` | derived forms: isolation as a key renaming of the table; the availability check |

## Metatheory map

| Property | Rocq |
|---|---|
| Well-formedness is preserved | `Preservation.v`: `preservation`, `wf_reachable` |
| Steps keep dependency order; resolution stays coherent | `Ordering.v`: `begin_requires_deps`, `provider_outlives`, `withdraw_waits`, `parent_waits_child`, `step_coherent` |
| Recovery is exact (unloading undoes a fiber's effects) | `Recovery.v`: `recovery_exact`, `recovery_from_init` |
| Disposing a runtime effect is exact, whatever other fibers did | `Runtime.v`: `effect_exact`, `effect_exact_inactive` |
| Isolation keeps every component-level hypothesis | `Derived.v`: `scoped_bounded`, `scoped_total`, `scoped_rank`, `scoped_ind` |
| Progress (quiet states are settled) | `Progress.v`: `quiet_settled`, `progress`, `progress_reachable` |
| Termination of lifecycle runs | `Termination.v`: `termination`, `no_infinite_run`, `termination_reachable` |
| Confluence, control states, no spawn | `Confluence.v`: `control_confluence`, `exists_quiet` |
| Confluence, service states, no spawn | `StateConf.v`: `state_confluence` |
| Confluence with spawn, up to renaming | `SpawnConf.v`: `spawn_confluence` (conclusion `Agree`) |
| Final states with corresponding roots agree, however reached | `SpawnConf.v`: `final_agree` (conclusion `AgreeL`) |
| Confluence under interleaved orchestration; agreement with static assembly (Thm 73) | `Dynamic.v`: `dynamic_confluence`, `dynamic_agree`, `static_assembly` |
| Confluence from bundled hypotheses; sums | `Compose.v`: `service_confluence`, `sum_hyps` |
| Independence asked only of operations two fibers may perform at one key (Thms 40, 42) | `Recovery.v`: `CoPair`, `Hind`; `ServiceSeq.v`: `replay_shuffle_ex`, `replay_blocks` |
| Operations at distinct keys are independent (Thm 40) | `Bridge.v`: `distinct_keys` |
| Key commutativity (Def 39) implies the calculus's independence hypotheses | `Bridge.v`: `paper_revert_indep`, `paper_commute`, `paper_confhyps`, `paper_hind` |
| A program denotes a witnessed effect function on the store (Def 41, up to ≃) | `Bridge.v`: `denote`, `denote_witnessed` |
| ⟦·⟧ commutes with the steps: an op or provision step is one stage of `denote`; its undo applies that stage's inverse | `Bridge.v`: `op_stage`, `op_undo`, `prov_stage`, `prov_undo` |
| A fiber loading by itself to Active reaches the store `denote` gives; its new undo items compose to `denote`'s inverse | `Bridge.v`: `lone_denote` |
| Dispatch on the ordered bus admits no equivalence under which registrations commute | `Observe.v`: `bus_no_commute` |

## Service coverage

| Service | Rocq |
|---|---|
| Registry: registrations, and lookups that cannot meet a registration of the same name, meet every confluence hypothesis | `Services/RegistryConf.v`: `registry_hyps` |
| Listener registration, up to order | `Services/Listeners.v`: `listeners_hyps`, `listeners_confluence` |
| Ordered event bus: registrations do not commute; unregister-by-callback is not an inverse | `Services/EventBus.v`: `on_not_commute`, `on_by_callback_not_witnessed` |
| Registry and listeners together | `Examples/Composed.v`: `composed_confluence` |

## §3.1 map

| Paper | Rocq |
|---|---|
| Def 1, 𝔗Γ, twisted composition | `Twisted.v`: `Twisted`, `tcomp`, `tunit`, `twisted_monoid` |
| Def 2, ∂Γ | `Twisted.v`: `Dctx` |
| Def 3, Thm 4, Thm 5 | `Twisted.v`: `track`, `track_fst`, `track_hom` |
| Def 6, Thm 7 | `Twisted.v`: `recover`, `recover_track_at` (pointwise), `recover_track` (g ∘ f = id) |
| Eq (11), soundness invariant | `Twisted.v`: `tracks`, `tracks_tcomps`, `recover_tracks`, `recover_tracks_init`, `reverts_along_global`, `sound`, `track_sound` |
| Def 8, 𝔈Γ, 𝔈*Γ, ⌜f, g⌝ | `EffectFun.v`: `Eff`, `Witnessed`, `induced`, `induced_witnessed` |
| Def 9, ⋄ | `EffectFun.v`: `diamond`, `diamond_unfold` |
| Thm 10 | `EffectFun.v`: `eff_monoid`, `induced_hom` |
| Thm 11 | `EffectFun.v`: `witnessed_submonoid`, `induced_witnessed`; up to ≃ and partially: `Bridge.v`: `pdiamond_witnessed` |
| Def 37, Lemma 38 (core): 𝔈*Γ read up to ≃, in `Maybe` | `Bridge.v`: `PWitnessed`, `pdiamond_witnessed`, `pbind_witnessed`, `pdiamonds_witnessed`; Def 8 recovered: `witnessed_total_iff`, `pdiamond_total` |
| Def 12, Thm 13 | `EffectFun.v`: `effect`, `effect_diamond`, `effect_eta`, `effect_hom` |
| Thm 14 | `EffectFun.v`: `effect_fwd_fst`, `effect_inv_fst` |
| Thm 15 | `EffectFun.v`: `effect_revert`, `effect_revert_sound`, `effect_witnessed_iff` |
| Notes' Comment (sequence of effects) | `EffectFun.v`: `diamonds`, `effect_diamonds`, `sequence_recovery` |
| Thm 16 | `EffectFun.v`: `lifo_apply_sound`, `lifo_revert` |
| Def 17, 𝔐(e) | `Independence.v`: `Generated`, `Gen`, `M`, `Gen_induced` |
| Lemma 18 | `Independence.v`: `generated_commute`, `M_diamond_gen` (notes), `M_diamond` (paper) |
| Def 19 | `Independence.v`: `Independent`, `PairwiseIndependent`, `induced_independent` |
| Thm 20 | `Independence.v`: `omit_state`, `omit_inverse` |
| Cor 21 | `Independence.v`: `any_order_recovers` |

## Axioms

The calculus and its metatheory use no axioms (`Print Assumptions` reports them
closed under the global context). In §3.1, `Twisted.recover_track` and
`EffectFun.sequence_recovery` use functional extensionality.
