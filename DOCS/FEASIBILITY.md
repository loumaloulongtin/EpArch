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
Proof: `ConcreteWorkingSystem` satisfies both.

### `world_bundles_feasible`

**File:** `EpArch/Feasibility.lean`  
**Tier:** A

World constraint bundles (`W_lies_possible`, `W_bounded_verification`,
`W_partial_observability`) are jointly satisfiable. Proof: `WitnessCtx` in `WorldWitness.lean`.

### `commitments_feasible`

**File:** `EpArch/Feasibility.lean`  
**Tier:** A

All 8 paper commitments are simultaneously satisfiable. Re-export of
`ConcreteLedgerModel.all_commitments_satisfiable`.

### `joint_feasible`

**File:** `EpArch/Feasibility.lean`  
**Tier:** A

Combines `constraints_feasible` and `objectives_feasible`.
For new citations, prefer `existence_under_constraints`.

---

## Supporting Modules

### `EpArch/Realizer.lean`

Defines `Realizer` (8-commitment conjunction) and `SuccessfulSystem` (working system + well-formedness + satisfaction). `ConcreteRealizer` and `ConcreteSuccessfulSystem` provide the concrete instances that back the feasibility proofs.

### `EpArch/WorldWitness.lean`

Defines `WitnessCtx` — a concrete `WorldCtx` instantiation used to prove `all_bundles_satisfiable`: the three `W_*` world-assumption bundles are jointly satisfiable.

### `EpArch/ConcreteLedgerModel.lean`

Proves `all_commitments_satisfiable` (all 8 commitment witnesses) and provides `ConcreteWorkingSystem` with its well-formedness and property-satisfaction proofs.

---

## Claim Budget

These are strong formal results — existence and forcing claims, not realism claims.

- **Non-vacuity:** The constraint + objective package is consistent and non-empty.
- **Existence:** There is at least one working system meeting the success bundle.
- **Forcing:** Success forces Bank primitives — this is not optional.
- **World consistency:** The world-assumption bundles are jointly satisfiable.

What these theorems do not establish:

- Uniqueness (many realizations can exist)
- Optimality (no optimality claim is made)
- Realism (the concrete witnesses are formal constructions, not empirical models)

---

## Strength and Axiom Impact

**Tier A** — All theorems are fully proved by composing existing witnesses from `WorldWitness`, `ConcreteLedgerModel`, and `Minimality`. No new axioms are introduced. Paper-facing axiom count remains **35**.

**Semantic role:** Non-vacuity + forced-primitives — not world realism.

---

## Paper Citation

For the appendix existence claim:

> `EpArch.Feasibility.existence_under_constraints`

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


