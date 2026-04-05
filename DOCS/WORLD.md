# World Layer Documentation

This document describes the World layer (`EpArch/World.lean` and `EpArch/WorldCtx.lean`) which provides the substrate for converting mechanism axioms into conditional obligation theorems.

## Canonical Type Vocabulary

> **IMPORTANT:** `EpArch.Claim` (defined in `Basic.lean`) is the **canonical claim type** used across the entire codebase.

| Type | Location | Status | Usage |
|------|----------|--------|-------|
| `EpArch.Claim` | `Basic.lean` | **Canonical** | The single claim type for all modules |
| `WorldCtx.Claim` | `WorldCtx.lean` | Type parameter | Instantiated to `EpArch.Claim` |

**Rule:** Other modules must NOT define new claim/proposition types. When modules use type parameters like `{PropLike : Type u}`, they should be instantiated with `EpArch.Claim`.

This ensures:
- One vocabulary across Bank, Health, StepSemantics, AdversarialObligations, and Agent modules
- No parallel type universes that complicate composition
- Clear paper-facing exports without type confusion

---

## Philosophy

**World assumptions are NOT asserted as true.** They parameterize obligation theorems.

Instead of:
```lean
axiom lies_scale : export_cost < defense_cost
```

We get:
```lean
theorem lies_scale_of_W : W_lies_scale → export_cost < defense_cost
```

This transformation:
- Makes assumptions **explicit** and **nameable**
- Allows users to **swap assumption bundles**
- Transforms "take it or leave it" claims into "if you accept X, then Y follows"

---

## Core Primitives

These are the fields of `WorldCtx`, the canonical parametric signature. All theorem signatures take `(C : WorldCtx)` and access primitives as `C.Truth`, `C.Claim`, etc. The deprecated `PropLike` alias in `World.lean` is equal to `EpArch.Claim`; it exists only for backward compatibility and should not be used in new code.

| Primitive | Type | Description |
|-----------|------|-------------|
| `World` | `Type` | Possible states of affairs |
| `Claim` | `Type` | Propositions / things that can be true or false |
| `Truth` | `World → Claim → Prop` | World-relative truth predicate |
| `Utter` | `Agent → Claim → Prop` | Agent utterance (speech act) |
| `Obs` | `Type` | Observations (epistemically accessible) |
| `obs` | `World → Obs` | Observation function |
| `VerifyWithin` | `World → Claim → Nat → Prop` | Bounded verification |
| `effectiveTime` | `World → Nat` | Available verification capacity |

---

## Derived Concepts

| Concept | Definition | Meaning |
|---------|------------|---------|
| `Lie w a P` | `Utter a P ∧ ¬Truth w P` | Agent utters falsehood |
| `can_lie a` | `∃ w P, Lie w a P` | Agent can lie somewhere |
| `PartialObs w0 w1` | `obs w0 = obs w1` | Observationally equivalent worlds |
| `NotDeterminedByObs P` | `∃ w0 w1, PartialObs w0 w1 ∧ (Truth w0 P ↔ ¬Truth w1 P)` | Truth underdetermined by observation |
| `RequiresSteps w P k` | `∀ t < k, ¬VerifyWithin w P t` | P needs at least k steps |

---

## World Assumption Bundles

These structures bundle assumptions for obligation theorems:

### `W_lies_possible`
```lean
structure WorldCtx.W_lies_possible (C : WorldCtx) where
  some_false : ∃ w P, ¬C.Truth w P
  unrestricted_utterance : ∀ a P, C.Utter a P
```
**Buys:** Lying is structurally possible
**Assumes:** False propositions exist; agents can utter anything

### `W_bounded_verification`
```lean
structure WorldCtx.W_bounded_verification (C : WorldCtx) where
  verification_has_cost : ∃ P k, k > 0 ∧ ∀ w, C.RequiresSteps w P k
```
**Buys:** Verification has non-trivial cost
**Assumes:** Some propositions require multiple steps to verify

### `W_partial_observability`
```lean
structure WorldCtx.W_partial_observability (C : WorldCtx) where
  obs_underdetermines : ∃ P, C.NotDeterminedByObs P
```
**Buys:** Observation doesn't determine all truth
**Assumes:** Observationally equivalent worlds can differ in truth values

---

## Obligation Theorems (Phase 1)

### `lie_possible_of_W`
```lean
theorem WorldCtx.lie_possible_of_W (C : WorldCtx) (W : WorldCtx.W_lies_possible C) :
    ∃ w a P, C.Lie w a P
```
**Paper claim:** "Agents can lie"
**What it buys:** Lying is structurally possible (existence)
**What it doesn't buy:** Prevalence, effectiveness, or scaling

### `all_agents_can_lie_of_W`
```lean
theorem WorldCtx.all_agents_can_lie_of_W (C : WorldCtx) (W : WorldCtx.W_lies_possible C)
    (a : C.Agent) : C.can_lie a
```
**Paper claim:** "Any agent can lie"
**What it buys:** Universal capability (all agents)
**What it doesn't buy:** Will they? How often?

### `bounded_audit_fails`
```lean
theorem WorldCtx.bounded_audit_fails (C : WorldCtx) (w : C.World) (P : C.Claim)
    (k t : Nat) : C.RequiresSteps w P k → t < k → ¬C.VerifyWithin w P t
```
**Paper claim:** "Verification is bounded"
**What it buys:** Time constraints matter
**What it doesn't buy:** What k is for any specific P

---

## Naming Convention

| Pattern | Meaning |
|---------|---------|
| `X` | Existing axiom name (mechanism claim) |
| `X_of_W` | Conditional theorem version |
| `W_X` | Minimal assumption bundle for `X_of_W` |

---

## Claim Budget

### ✅ What We CAN Claim

- "Under W_lies_possible, lying is structurally possible"
- "Bounded verification implies time constraints matter"
- "These assumptions are explicit and auditable"

### ❌ What We CANNOT Claim

- "Agents WILL lie" (existence ≠ prevalence)
- "Verification costs are THIS high" (parameterized, not instantiated)
- "These world assumptions are true" (they're parameters, not assertions)

### ⚠️ Overclaim Traps

| Trap | Why Wrong | Correct Framing |
|------|-----------|-----------------|
| "We proved agents lie" | Conditional on assumptions | "Under W_lies_possible, lies are structurally possible" |
| "Verification is infeasible" | Only if time < required | "If t < k and RequiresSteps w P k, verification fails" |
| "World model is realistic" | It's minimal, not complete | "World layer provides sufficient structure for obligation theorems" |

---

## Relationship to Existing Modules

```
Basic.lean (Agent, Claim, Bubble, etc.)
    ↓
WorldCtx.lean (WorldCtx structure: World, Truth, Utter, etc.)
    ↓                          ↓
World.lean (re-exports)    AdversarialObligations.lean (W-bundles → obligations)
                               ↑
                           AdversarialBase.lean (attack patterns)
                               ↑
                           Basic.lean + Header.lean + Bank.lean + Commitments.lean
```

The World layer sits between Basic (pure types) and Adversarial (attack modeling), providing the semantic substrate for truth, utterance, and verification. Note: `AdversarialBase.lean` imports `Basic`, `Header`, `Bank`, and `Commitments` (not `World.lean`). `AdversarialObligations.lean` imports `WorldCtx` (not `World.lean`) plus `AdversarialBase`.

---

## Adversarial Obligation Theorems (AdversarialObligations.lean)

The `AdversarialObligations.lean` module converts the adversarial axioms from `AdversarialBase.lean` into conditional obligation theorems:

| Original Axiom | Obligation Theorem | World Bundle |
|----------------|-------------------|--------------|
| `spoofed_V_blocks_path` | `spoofed_V_blocks_path_of_W` | `W_spoofedV` |
| `ddos_causes_verification_collapse` | `ddos_causes_verification_collapse_of_W` | `W_ddos` |
| `collapse_causes_centralization` | `collapse_causes_centralization_of_W` | `W_collapse_centralization` |
| `lies_scale` | `lies_scale_of_W` | `W_lies_scale` |
| `rolex_ddos_structural_equivalence` | `rolex_ddos_structural_equivalence_of_W` | `W_rolex_ddos` |

### Composed Chain

The `ddos_to_centralization_of_W` theorem composes the DDoS and centralization theorems:

```lean
theorem ddos_to_centralization_of_W (W : W_ddos_full)
    (a : Agent) (s : DDoSState a) (c : CollapsedState a) (t : CentralizedState a) :
    some_vector_overwhelmed s → is_centralized t
```

This captures the full paper claim: "DDoS vectors → verification collapse → trust centralization"

