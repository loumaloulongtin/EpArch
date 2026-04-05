# Feasibility / Non-Vacuity Documentation

This document describes the feasibility theorems that establish the paper's
constraint bundles are consistent and, crucially, that **success forces Bank primitives**.

---

## Overview

The paper makes 8 structural commitments (§1.1). Natural objections:
1. "Are these constraints even consistent? Maybe they're vacuous."
2. "Does a system satisfying these properties actually exist?"
3. "Are Bank primitives merely sufficient, or actually necessary?"

The feasibility theorems answer:
- **Yes**, the constraint bundles are jointly satisfiable.
- **Yes**, a working system meeting the success bundle exists.
- **Forced**: Success implies Bank primitives (via Minimality).

---

## Headline Theorem

### `existence_under_constraints`

**File:** `EpArch/Feasibility.lean`  
**Tier:** A (proved theorem)  
**Paper Role:** Appendix existence claim + forced-primitives

```lean
theorem existence_under_constraints :
    ∃ W : WorkingSystem,
      WellFormed W ∧ SatisfiesAllProperties W ∧ containsBankPrimitives W
```

**Meaning:** There exists a working system that:
1. Is well-formed (satisfies structural requirements)
2. Satisfies all operational properties (the success bundle)
3. Contains Bank primitives (forced by minimality)

This is the single citable theorem for the paper's appendix.

---

## Supporting Theorems

### `goals_force_bank_primitives`

**File:** `EpArch/Feasibility.lean`  
**Tier:** A

```lean
theorem goals_force_bank_primitives :
    ∀ W : WorkingSystem, WellFormed W → SatisfiesAllProperties W → containsBankPrimitives W
```

Any successful system MUST contain Bank primitives. This is the minimality
direction (re-export of `convergence_under_constraints'`).

### `success_feasible`

**File:** `EpArch/Feasibility.lean`  
**Tier:** A

```lean
theorem success_feasible :
    ∃ W : WorkingSystem, WellFormed W ∧ SatisfiesAllProperties W
```

The success bundle (WellFormed + SatisfiesAllProperties) is non-empty.
Witnessed by `ConcreteWorkingSystem`.

### `world_bundles_feasible`

**File:** `EpArch/Feasibility.lean`  
**Tier:** A

World constraint bundles (W_lies_possible, W_bounded_verification,
W_partial_observability) are jointly satisfiable. Witnessed by `WitnessCtx`.

### `commitments_feasible`

**File:** `EpArch/Feasibility.lean`  
**Tier:** A

All 8 paper commitments are simultaneously satisfiable. Re-export of
`ConcreteLedgerModel.all_commitments_satisfiable`.

### `joint_feasible` (Legacy)

**File:** `EpArch/Feasibility.lean`  
**Tier:** A

Legacy theorem combining `constraints_feasible` and `objectives_feasible`.
Use `existence_under_constraints` for new citations.

---

## Supporting Modules

### `EpArch/Realizer.lean`

Defines the `Realizer` structure and `SuccessfulSystem` structure:

```lean
structure Realizer where
  commitments : <8 commitment conjunction>

structure SuccessfulSystem where
  W  : WorkingSystem
  wf : WellFormed W
  sat : SatisfiesAllProperties W
```

The `ConcreteRealizer` witnesses Realizer via `ConcreteLedgerModel`.
The `ConcreteSuccessfulSystem` witnesses SuccessfulSystem via `ConcreteInstance`.

### `EpArch/WorldWitness.lean`

Defines `WitnessCtx` — a concrete `WorldCtx` instantiation with:
- `World := Bool` (two worlds)
- `Claim := Bool` (two claims)
- `Truth w P := (w = P)` (truth = world-claim match)
- `Obs := Unit` (maximal underdetermination)

Proves `all_bundles_satisfiable`: the W_* bundles are jointly satisfiable.

### `EpArch/ConcreteLedgerModel.lean`

Proves `all_commitments_satisfiable` (8 commitment witnesses) and
provides `ConcreteInstance` namespace with:
- `ConcreteWorkingSystem` — concrete working system
- `concrete_wellformed` — proof it's well-formed
- `concrete_satisfies_all_properties` — proof it satisfies all properties

---

## Claim Budget

### Buys (strong)

- ✅ "The constraint+objective package is consistent (nonempty)"
- ✅ "There exists at least one working system meeting the success bundle"
- ✅ "Success forces Bank primitives (minimality)"
- ✅ "World-bundles are satisfiable (at least one witness)"

### Does NOT Buy (do not overclaim)

- ❌ "The real world literally is this model"
- ❌ "Uniqueness" (many realizations can exist)
- ❌ "Abduction/inference from observed O to existence of S"

---

## Strength Tier

**Tier A** — Proved theorem

All theorems are fully proved by composing existing witnesses. No new axioms.

**Semantic Role:** Non-vacuity + forced-primitives — not "world realism."

---

## Paper Citation

For the appendix existence claim, cite:

> "There exists a working system satisfying all operational properties,
> and any such system must contain Bank primitives."
> Proof: `EpArch.Feasibility.existence_under_constraints`

---

## Relationship to Other Modules

```
WorldWitness.WitnessCtx ──────────┐
  (concrete WorldCtx)             │
                                  ▼
               world_bundles_feasible (∃ C : WorldCtx, ...)
                                  │
ConcreteInstance ─────────────────┼──────────────────────────────┐
  .ConcreteWorkingSystem          │                              │
  .concrete_wellformed            ▼                              ▼
  .concrete_satisfies_all     success_feasible         goals_force_bank_primitives
                                  │                              │
                                  └──────────────┬───────────────┘
                                                 ▼
                               existence_under_constraints (HEADLINE)
```

---

## Axiom Impact

**None.** These theorems introduce no new axioms. They compose existing
witnesses from `WorldWitness`, `ConcreteLedgerModel`, and `Minimality`.

Paper-facing axiom count remains **36**.
