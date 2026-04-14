# World Layer Documentation

This document explains the **World layer** (`EpArch/WorldCtx.lean`) as the semantic substrate used to convert world-side assumptions into **conditional obligation theorems**.

Its job is narrow:

- define what the World layer is
- explain what the `W_*` bundles mean
- show what these bundles buy, and what they do **not** buy
- prevent overclaiming about world-conditioned results

---

## What the World Layer Is

The World layer is **not** a concrete model of reality.

It is a **parametric semantic interface** used to state theorems of the form:

```
W_* → obligation
```

Instead of asserting mechanism-style claims directly as unconditional axioms, the architecture makes the world-side assumptions explicit and bundles them.

So instead of:

```lean
axiom lies_scale : export_cost < defense_cost
```

the World layer supports:

```lean
theorem lies_scale_of_W : W_lies_scale → export_cost < defense_cost
```

This makes assumptions **explicit and nameable**, lets readers inspect exactly which world-side assumptions are doing work, and converts "take it or leave it" claims into conditional, auditable theorem statements.

---

## Why the Layer Is Parametric

`WorldCtx` is a semantic signature, not a fixed world model. Theorems stated over `(C : WorldCtx)` range over any instantiation satisfying the signature and the relevant bundles.

This separation buys two things:

**Generality** — theorems are not tied to one stub world.

**Clean assumption discipline** — the repo separates what is assumed about worlds from what is proved about the architecture under those assumptions.

The World layer is best understood as the place where the repo says: *"If the world has this structure, then these epistemic pressures or obligations follow."*

---

## Core Primitives

These are the fields of `WorldCtx`. All theorem signatures take `(C : WorldCtx)` and access primitives as `C.Truth`, `C.Claim`, etc.

| Primitive | Type | Role |
|-----------|------|------|
| `World` | `Type` | Possible states of affairs |
| `Claim` | `Type` | Propositions / truth-evaluable items |
| `Truth` | `World → Claim → Prop` | World-relative truth predicate |
| `Utter` | `Agent → Claim → Prop` | Speech-act / utterance relation |
| `Obs` | `Type` | Observations / epistemically accessible outputs |
| `obs` | `World → Obs` | Observation function |
| `VerifyWithin` | `World → Claim → Nat → Prop` | Bounded verification predicate |
| `effectiveTime` | `World → Nat` | Available verification capacity |

`Truth` says what is true in a world; `obs` says what is accessible to an observer; `VerifyWithin` says what can be checked within bounded effort; `effectiveTime` gives the resource side of that boundedness.

---

## Derived Concepts

Several useful world-layer notions are defined from the core interface.

| Concept | Definition | Meaning |
|---------|------------|---------|
| `Lie w a P` | `Utter a P ∧ ¬Truth w P` | Agent utters a falsehood |
| `can_lie a` | `∃ w P, Lie w a P` | Agent can lie somewhere |
| `PartialObs w0 w1` | `obs w0 = obs w1` | Two worlds are observationally indistinguishable |
| `NotDeterminedByObs P` | `∃ w0 w1, PartialObs w0 w1 ∧ (Truth w0 P ↔ ¬Truth w1 P)` | Observation underdetermines truth |
| `RequiresSteps w P k` | `∀ t < k, ¬VerifyWithin w P t` | Verifying P needs at least k steps |

These are the minimum derived notions needed to state obligation theorems cleanly.

---

## World Assumption Bundles

The `W_*` structures package assumptions that later theorems depend on. They are *conditions on a WorldCtx*, not universal facts: some instantiations satisfy them (`WitnessCtx` in `WorldWitness.lean`) and some do not (`TrivialCtx`, where `Truth w P = True` always, provably has no lies). The heading "assumptions" is correct — they characterize which worlds are epistemically non-trivial.

Each bundle independently forces its own structural conclusion — no bundle needs the others to do its work:

- **`W_lies_possible` alone** → `w_lies_forces_revocation_need`: revocation primitives are necessary.
- **`W_bounded_verification` alone** → `w_bounded_forces_incompleteness`: trust-bridge primitives are necessary.
- **`W_partial_observability` alone** → `w_partial_obs_forces_redeemability`: redeemability primitives are necessary.

The "all three" requirement only appears at the top-level convergence theorem `world_assumptions_force_bank_primitives`, which needs all three because `containsBankPrimitives` requires *all six* architectural features and three of those six are each individually grounded by one bundle. Remove any one bundle and the corresponding feature loses its forcing argument — the theorem would have a gap. The assumptions are not discharged by the conditional — they are its antecedents. They are discharged only in `kernel_world_forces_bank_primitives`, which instantiates the concrete `WitnessCtx` witness and closes the statement with zero free hypotheses.

**World-assumption-free path (stronger):** The W_* bundles are the *motivating* source for the revocation, trust-bridge, and redeemability dimensions, but they are no longer the only — or the strongest — forcing mechanism. `Feasibility.lean` now contains `grounded_world_and_structure_force_bank_primitives` and `bundled_structure_forces_bank_primitives`, which take `Represents*` structural witnesses directly and require **no `WorldCtx` at all**. The universe boundary is real: W_* bundles are `Prop`-valued and cannot auto-manufacture the `Type`-valued fields that `Represents*` structures carry. Callers that can supply concrete structural witnesses get a strictly stronger theorem — it holds for any world, not just `WorldCtx`-parameterized ones.

### `W_lies_possible`
```lean
structure WorldCtx.W_lies_possible (C : WorldCtx) where
  some_false : ∃ w P, ¬C.Truth w P
  unrestricted_utterance : ∀ a P, C.Utter a P
```
**Buys:** Lying is structurally possible; also grounds `w_lies_forces_revocation_need` in `Feasibility.lean`, which derives `MonotonicLifecycle` absorption → `monotonic_no_exit` → Bank revocation primitives are necessary.
**Assumes:** False propositions exist; agents can utter arbitrary claims.

This is an existence/capability bundle. It says nothing about frequency, effectiveness, or strategic success.

### `W_bounded_verification`
```lean
structure WorldCtx.W_bounded_verification (C : WorldCtx) where
  verification_has_cost : ∃ P k, k > 0 ∧ ∀ w, C.RequiresSteps w P k
```
**Buys:** Some verification tasks have non-trivial cost; also grounds `w_bounded_forces_incompleteness` in `Feasibility.lean`, which derives `BoundedVerification` incompleteness → Bank trust-bridge primitives are necessary.
**Assumes:** At least some propositions require more than zero effort to verify.

This gives the architecture a formal handle on bounded audit.

### `W_partial_observability`
```lean
structure WorldCtx.W_partial_observability (C : WorldCtx) where
  obs_underdetermines : ∃ P, C.NotDeterminedByObs P
```
**Buys:** Observation does not settle all truth; also grounds `w_partial_obs_forces_redeemability` in `Feasibility.lean`, which derives the obs-stable closed endorsement gap → Bank redeemability primitives are necessary.
**Assumes:** There exist observationally equivalent worlds differing in truth value.

This is the clean world-layer form of "what can be seen is not everything that matters."

---

## Obligation Theorems

### `lie_possible_of_W`
```lean
theorem WorldCtx.lie_possible_of_W (C : WorldCtx) (W : WorldCtx.W_lies_possible C) :
    ∃ w a P, C.Lie w a P
```
**What it buys:** Lying is structurally possible.
**What it does not buy:** Prevalence, scaling, strategic success, or social consequences.

### `all_agents_can_lie_of_W`
```lean
theorem WorldCtx.all_agents_can_lie_of_W (C : WorldCtx) (W : WorldCtx.W_lies_possible C)
    (a : C.Agent) : C.can_lie a
```
**What it buys:** Lying is an agent-general capability under the bundle.
**What it does not buy:** That agents will exercise this capability.

### `bounded_audit_fails`
```lean
theorem WorldCtx.bounded_audit_fails (C : WorldCtx) (w : C.World) (P : C.Claim)
    (k t : Nat) : C.RequiresSteps w P k → t < k → ¬C.VerifyWithin w P t
```
**What it buys:** Time/resource limits matter formally.
**What it does not buy:** A fixed empirical cost model for real verification tasks.

### `kernel_redundant_without_lies`
```lean
theorem WorldCtx.kernel_redundant_without_lies (C : WorldCtx)
    (h : ∀ w P, C.Truth w P) : ¬∃ w a P, C.Lie w a P
```
**What it buys:** If all propositions are universally true in all worlds, no lie is constructible — the kernel discriminator is a no-op and EpArch's accept/reject pass never fires. This is the contrapositive justification for why mechanisms like the kernel exist: they are only non-trivial in worlds where `W_lies_possible` holds.
**What it does not buy:** A proof that `W_lies_possible` holds in any concrete world. That is established by `WitnessCtx` in `WorldWitness.lean`.

---

## Adversarial Obligation Theorems (`Adversarial/Obligations.lean`)

`Adversarial/Obligations.lean` converts the adversarial axioms from `Adversarial/Base.lean` into conditional obligation theorems using the same `W_*` / `_of_W` pattern.

| Original Axiom | Obligation Theorem | World Bundle |
|----------------|-------------------|--------------|
| `spoofed_V_blocks_path` | `spoofed_V_blocks_path_of_W` | `W_spoofedV` |
| `ddos_causes_verification_collapse` | `ddos_causes_verification_collapse_of_W` | `W_ddos` |
| `collapse_causes_centralization` | `collapse_causes_centralization_of_W` | `W_collapse_centralization` |
| `lies_scale` | `lies_scale_of_W` | `W_lies_scale` |
| `rolex_ddos_structural_equivalence` | `rolex_ddos_structural_equivalence_of_W` | `W_rolex_ddos` |

The `ddos_to_centralization_of_W` theorem composes the DDoS and centralization results into the full argument chain: "DDoS vectors → verification collapse → trust centralization."

```lean
theorem ddos_to_centralization_of_W (W : W_ddos_full)
    (a : Agent) (s : DDoSState a) (c : CollapsedState a) (t : CentralizedState a) :
    some_vector_overwhelmed s → is_centralized t
```

---

## Reading Discipline

The `W_*` bundles are exposed explicitly because the project formalizes inference load openly — not because the assumptions are dubious. In the intended application class (bounded epistemic agents in adversarial environments), they are **minimal structural pressures**, not speculative metaphysical commitments.

`W_lies_possible`, `W_bounded_verification`, and `W_partial_observability` encode three background conditions that are close to unavoidable in any realistic bounded setting: non-omniscience, non-zero verification cost, and the structural possibility of false utterance. Making them explicit does not make the framework fragile. It makes the inference load **visible and auditable**.

The `_of_W` theorems are conditional in the **logical** sense — they factor out the world-side assumptions so readers can see exactly which pressures drive which obligations. This is distinct from saying the assumptions may be false. Richer world assumptions can be added or substituted; doing so refines or extends the analysis without invalidating the framework.

The one overclaim to avoid: existence/capability results (`lie_possible_of_W`, `all_agents_can_lie_of_W`) establish *that* a property holds structurally, not *how often* or *how effectively* it is exercised. Scaling and prevalence claims are separate.

---

## Naming Convention

| Pattern | Meaning |
|---------|---------|
| `W_X` | Minimal assumption bundle for the `X_of_W` theorem |
| `X_of_W` | Conditional theorem version of axiom `X` |

---

## Relationship to Other Modules

```
Basic.lean
    ↓
WorldCtx.lean
    ↓                                          ↓
Adversarial/Obligations.lean             Feasibility.lean
(W-bundles → obligations)           (W-bundles → containsBankPrimitives)
       ↑
Adversarial/Base.lean (attack patterns)
```

`WorldCtx.lean` provides the semantic interface for truth, observation, and bounded verification. `Adversarial/Base.lean` imports `Basic`, `Header`, `Bank`, and `Commitments`; `Adversarial/Obligations.lean` imports `WorldCtx` plus `Adversarial/Base`. `Feasibility.lean` imports `WorldCtx` directly and uses all three W_* bundles as antecedents in `world_assumptions_force_bank_primitives`, closing the loop from world assumptions to architectural convergence.

---

`EpArch.Claim` (defined in `Basic.lean`) is the canonical claim type across the codebase. `WorldCtx.Claim` is a type parameter instantiated to `EpArch.Claim`. New world-side claims should follow the `W_*` / `_of_W` pattern.

