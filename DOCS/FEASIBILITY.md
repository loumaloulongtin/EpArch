# Feasibility / Non-Vacuity Documentation

This document describes the feasibility theorems that establish EpArch's
constraint bundles are consistent and, crucially, that **success forces Bank primitives**.

---

## Overview

EpArch makes 8 structural commitments. Natural objections:
1. "Are these constraints even consistent? Maybe they're vacuous."
2. "Does a system satisfying these properties actually exist?"
3. "Are Bank primitives merely sufficient, or actually necessary?"

The feasibility theorems answer:
- **Yes**, the constraint bundles are jointly satisfiable.
- **Yes**, a working system meeting the constraint+success bundle exists.
- **Forced**: Bank primitives are necessary, not optional — via both the structural path
  (no `WorldCtx`) and the world-grounded path (W_* bundles as antecedents).

---

## Headline Theorems

### `bundled_structure_forces_bank_primitives`

**File:** `EpArch/WorldBridges.lean`  
**Tier:** A (proved theorem)  
**Role:** Headline convergence — structural path, any world

```lean
theorem bundled_structure_forces_bank_primitives
    (W : WorkingSystem)
    (O : SystemOperationalBundle W)
    (B : WorldBridgeBundle W)
    (h_sat : SatisfiesAllProperties W) :
    containsBankPrimitives W
```

Any working system carrying `SystemOperationalBundle` (scope, headers, bank, authorization, and storage witnesses)
and `WorldBridgeBundle` (revocation, trust, redeemability witnesses), satisfying all
operational properties, necessarily contains Bank primitives. **No `WorldCtx` required.**
The W_* bundles are the natural *source* for the bundle witnesses but are not formal
preconditions here — the structural witnesses alone suffice. This is the cleanest
citable form of the main convergence result.

### `existence_under_constraints_structural`

**File:** `EpArch/Feasibility.lean`  
**Tier:** A  
**Role:** Non-vacuity existence proof (structural path)

```lean
theorem existence_under_constraints_structural :
    ∃ W : WorkingSystem,
      StructurallyForced W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W
```

There exists a working system that satisfies all operational properties and contains
Bank primitives, with forcing witnessed by `StructurallyForced`. Witnessed by
`ConcreteWorkingSystem` via `concrete_structurally_forced` + `concrete_satisfies_all_properties`.

### `kernel_world_forces_bank_primitives`

**File:** `EpArch/WorldBridges.lean`  
**Tier:** A  
**Role:** Zero-hypothesis corollary — strongest closed form

```lean
theorem kernel_world_forces_bank_primitives :
    containsBankPrimitives EpArch.ConcreteInstance.ConcreteWorkingSystem
```

No free hypotheses. Proof path: (1) `WitnessCtx` witnesses all three W_* bundles;
(2) `concrete_structurally_forced` + `structurally_forced_is_world_aware` gives
`WorldAwareSystem WitnessCtx`; (3) `world_assumptions_force_bank_primitives` closes.

---

## World-to-Structural Bridge Theorems

These theorems connect the W_* world-assumption bundles (`WorldCtx.lean`) to the
structural forcing machinery (`Minimality.lean`, `Convergence.lean`). Each W_* bundle
independently forces its corresponding structural conclusion.

### `w_bounded_forces_incompleteness`

**File:** `EpArch/WorldBridges.lean`

```lean
theorem w_bounded_forces_incompleteness (C : WorldCtx)
    (W : C.W_bounded_verification) :
    ∃ (P : C.Claim) (k : Nat) (M : BoundedVerification),
      k > 0 ∧ (∀ w, C.RequiresSteps w P k) ∧
      M.Claim = C.Claim ∧ ¬∀ c : M.Claim, M.verify_cost c ≤ M.budget
```

Any world satisfying `W_bounded_verification` constructs a `BoundedVerification`
instance that triggers `verification_only_import_incomplete`, grounding the trust-bridge
forcing argument in the world's own hard claim.

**Recall direction (Minimality.lean §9).** The same bounded-budget impossibility applies
at *withdrawal* time: an agent recalling a banked deposit must re-verify that its
provenance chain (V) is still intact. For any fixed recall budget, deposits with V-chain
depth exceeding the budget cannot be re-verified. `RecallBudget` is the parallel
structure to `BoundedVerification`; `recall_only_withdrawal_incomplete` closes via the
same `Nat.not_le_of_gt` path. Bounded recall forces *some* recall-admissibility filter;
τ-expiry is a sufficient clock-based implementation (setting `tau_window = budget` keeps
deposits within the recall budget), but priority eviction or provenance compression via
`Step.update` are equally valid responses. The recall impossibility embeds into
`BoundedVerification` via `recallBudget_to_bounded`, confirming both directions share the
same formal structure. `RecallBudget` is not a ninth `Pressure` constructor: it is a
Minimality-layer consequence of the trust/bounded-audit dimension.

### `w_lies_forces_revocation_need`

**File:** `EpArch/WorldBridges.lean`

```lean
theorem w_lies_forces_revocation_need (C : WorldCtx)
    (W : C.W_lies_possible) :
    ∃ w P, ¬C.Truth w P ∧ (∀ a, C.Utter a P) ∧
      ∀ (step : C.Claim → C.Claim),
        (∀ w' P', ¬C.Truth w' P' → step P' = P') →
        ∀ n, iter step n P = P
```

Any world satisfying `W_lies_possible` contains a false claim that is permanently
trapped under every revocation-free lifecycle, grounding the revocation forcing argument
via `monotonic_no_exit`.

### `w_partial_obs_forces_redeemability`

**File:** `EpArch/WorldBridges.lean`

```lean
theorem w_partial_obs_forces_redeemability (C : WorldCtx)
    (W : C.W_partial_observability) :
    ∃ P w0,
      ∀ (endorsed : C.World → C.Claim → Prop),
        (∀ P' w0' w1', C.PartialObs w0' w1' → endorsed w0' P' → endorsed w1' P') →
        (∀ w P', endorsed w P' → C.Truth w P') →
        ¬endorsed w0 P
```

Any world satisfying `W_partial_observability` has a claim that cannot be endorsed by
any obs-stable, closed endorsement system, grounding the redeemability forcing argument.

### `world_assumptions_force_bank_primitives`

**File:** `EpArch/WorldBridges.lean`

```lean
theorem world_assumptions_force_bank_primitives (C : WorldCtx)
    (Wl : C.W_lies_possible)
    (Wv : C.W_bounded_verification)
    (Wo : C.W_partial_observability)
    (W : WorkingSystem)
    (h_wa : WorldAwareSystem C W)
    (h_sat : SatisfiesAllProperties W) :
    containsBankPrimitives W
```

A working system that satisfies `WorldAwareSystem` (eight feature implications — three behind W_* guards,
five unconditional: scope, headers, bank, authorization, storage)
and `SatisfiesAllProperties` necessarily contains Bank primitives when all three W_* bundles
hold. All three bundles are consumed: removing any one leaves the corresponding feature
forcing argument without a world-level justification.

### `structurally_forced_is_world_aware`

**File:** `EpArch/WorldBridges.lean`

```lean
theorem structurally_forced_is_world_aware (C : WorldCtx) (W : WorkingSystem)
    (h_sf : StructurallyForced W) : WorldAwareSystem C W
```

Every `StructurallyForced` system satisfies `WorldAwareSystem` for any `WorldCtx`.
Proof by weakening: `StructurallyForced` asserts the eight implications *unconditionally*;
`WorldAwareSystem` only requires three of them *behind W_* guards*. Ignoring the guards
gives `WorldAwareSystem` as a strict weakening.

---

## Structural Convergence Theorems

### `convergence_structural`

**File:** `EpArch/Convergence.lean`

```lean
theorem convergence_structural :
    ∀ W : WorkingSystem,
      StructurallyForced W → SatisfiesAllProperties W → containsBankPrimitives W
```

The structural convergence theorem — no `WorldCtx`, no W_* bundles. The preferred
citation when the structural path needs to be made explicit.

### `existence_under_constraints_embedding`

**File:** `EpArch/Feasibility.lean`

```lean
theorem existence_under_constraints_embedding :
    ∃ W : WorkingSystem,
      ForcingEmbedding W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W
```

Strongest non-vacuity form. All design judgment is localised in
`concrete_forcing_embedding`; the rest (`embedding_to_structurally_forced →
convergence_structural → containsBankPrimitives`) is mechanical.

### `grounded_world_and_structure_force_bank_primitives`

**File:** `EpArch/WorldBridges.lean`

Full explicit form: takes individual `Represents*` structural witnesses (one per dimension)
plus explicit bridge hypotheses, without bundling them into `SystemOperationalBundle` /
`WorldBridgeBundle`. This is the proof target that `bundled_structure_forces_bank_primitives`
unpacks into. Prefer the bundled form for citations; use the explicit form when auditing
the per-dimension obligations.

### `WorldSystemCompat` / `world_deriving_bridge`

**File:** `EpArch/WorldBridges.lean`

```lean
structure WorldSystemCompat (C : WorldCtx) (W : WorkingSystem) where
  lifecycle        : C.W_lies_possible → RepresentsMonotonicLifecycle W
  n_rev            : Nat
  lifecycle_escape : ∀ (wl : C.W_lies_possible), ...
  verification     : C.W_bounded_verification → RepresentsBoundedVerification W
  trust_all        : ∀ (wv : C.W_bounded_verification), ...
  endorsement      : C.W_partial_observability → RepresentsClosedEndorsement W
  endorsement_witness : ∀ (wo : C.W_partial_observability), ...

theorem world_deriving_bridge
    (C : WorldCtx) (W : WorkingSystem)
    (compat : WorldSystemCompat C W)
    (wl : C.W_lies_possible) (wv : C.W_bounded_verification) (wo : C.W_partial_observability) :
    WorldBridgeBundle W
```

`WorldSystemCompat C W` is the formal certificate that system `W` genuinely operates
under the `WorldCtx` conditions: it records, for each of the three world-adjacent
dimensions, a function from the relevant `W_*` bundle to the corresponding `Represents*`
witness for `W`, plus the bridge hypothesis. It is the adapter layer between
`WorldCtx` world pressure and `WorkingSystem` structural evidence without refactoring
either.

`world_deriving_bridge` assembles a `WorldBridgeBundle W` from a `WorldSystemCompat C W`
certificate plus the three `W_*` witnesses. Any system genuinely operating under the
EpArch world conditions satisfies `WorldBridgeBundle` without supplying the seven
bridge-bundle fields as independent explicit parameters. This closes the construction
gap noted in the `WorldBridgeBundle` design comment in `Scenarios.lean`.

This does not eliminate the universe boundary: `W_*` bundles are `Prop`-valued; the
`Represents*` fields (`State : Type`, `Claim : Type`) are `Type`-valued. The gap is
not closed by deriving `Type` from `Prop` — `WorldSystemCompat` provides the
`Type`-valued witnesses explicitly. The derivation removes the redundancy of spelling
them out separately from the world witnesses when the system genuinely instantiates all
three world pressures.

---

## Non-Vacuity Theorems

| Theorem | Statement | Role |
|---------|-----------|------|
| `world_bundles_feasible` | `∃ C : WorldCtx, Nonempty C.W_lies_possible ∧ Nonempty C.W_bounded_verification ∧ Nonempty C.W_partial_observability` | W_* bundles jointly satisfiable; witnessed by `WitnessCtx` |
| `commitments_feasible` | All 8 commitments simultaneously satisfiable | Re-exports `EpArch.Concrete.Commitments.all_commitments_satisfiable` |
| `realizer_exists` | `Nonempty EpArch.Realizer` | A Realizer exists; witnessed by `ConcreteRealizer` |

---

## Supporting Modules

### `EpArch/Concrete/Realizer.lean`

Defines `Realizer` (8-commitment conjunction) and `SuccessfulSystem` (working system +
`StructurallyForced` + `SatisfiesAllProperties`). `ConcreteRealizer` and
`ConcreteSuccessfulSystem` provide the concrete instances.

### `EpArch/WorldWitness.lean`

Defines `WitnessCtx` — a concrete `WorldCtx` instantiation — and proves
`holds_W_lies_possible`, `holds_W_bounded_verification`, `holds_W_partial_observability`
(the three non-vacuity witnesses). Used by `kernel_world_forces_bank_primitives` to
discharge the W_* antecedents.

### `EpArch/Concrete/`

Split from the former `ConcreteLedgerModel.lean` into eight focused modules:
- `Concrete/Types.lean` — concrete types (CProp, CDeposit, CBubble, …)
- `Concrete/Commitments.lean` — C1–C8 commitment witnesses + `all_commitments_satisfiable`
- `Concrete/WorkingSystem.lean` — behavioral equivalence, grounding, `ConcreteWorkingSystem`
- `Concrete/DeficientSystems.lean` — eight deficient-system bridge-impossibility witnesses
- `Concrete/NonVacuity.lean` — advanced non-vacuity: traces, legibility, convergence
- `Concrete/Realizer.lean` — `Realizer` and `SuccessfulSystem` type packaging
- `Concrete/VerificationDepth.lean` — `DepthClaim` constructive witness, `bounded_verify`
- `Concrete/WorkedTraces.lean` — worked trace examples for theorem transport

Provides `ConcreteWorkingSystem` with `concrete_structurally_forced` and
`concrete_satisfies_all_properties`.

These theorems do not establish uniqueness (many realizations can exist),
optimality (no optimality claim is made), or realism (the concrete witnesses
are formal constructions, not empirical models).

---

## Strength and Axiom Impact

**Tier A** — All theorems are fully proved by composing existing witnesses from
`WorldWitness`, `EpArch/Concrete/`, `Minimality`, and `Convergence`.
No `axiom` declarations are introduced.

**Semantic role:** Non-vacuity + forced-primitives — not world realism.

---

## Relationship to Other Modules

```
WorldWitness.WitnessCtx ─────────────┐
  holds_W_lies_possible               │
  holds_W_bounded_verification        │
  holds_W_partial_observability       │
                                      ▼
                    world_bundles_feasible (∃ C : WorldCtx, ...)
                                      │
ConcreteInstance ─────────────────────┼──────────────────────────────────────┐
  .ConcreteWorkingSystem              │                                      │
  .concrete_structurally_forced       ▼                                      │
  .concrete_satisfies_all  structurally_forced_is_world_aware                │
  .concrete_forcing_embedding         │                                      │
                                      ▼                                      │
                    world_assumptions_force_bank_primitives ◀────────────────┘
                          (W_* bundles + WorldAwareSystem)
                                      │
                                      ▼
                    kernel_world_forces_bank_primitives (no free hypotheses)

concrete_forcing_embedding
  │
  ▼
  embedding_to_structurally_forced
  │
  ▼
  concrete_structurally_forced
  │
  ▼
  convergence_structural
  │
  ├──▶  existence_under_constraints_structural
  │       (StructurallyForced ∧ SatisfiesAllProperties ∧ containsBankPrimitives)
  │
  └──▶  existence_under_constraints_embedding
          (ForcingEmbedding ∧ SatisfiesAllProperties ∧ containsBankPrimitives)

SystemOperationalBundle + WorldBridgeBundle
  │
  ▼
  grounded_world_and_structure_force_bank_primitives
  │
  ▼
  bundled_structure_forces_bank_primitives (headline; no WorldCtx)
```


