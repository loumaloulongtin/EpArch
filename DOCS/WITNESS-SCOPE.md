# Witness Scope: What `ConcreteLedgerModel.lean` Establishes

This document specifies what is **directly witnessed by `ConcreteLedgerModel.lean`**, what is **proved elsewhere in the repo**, and what is **out of scope**.

Its job is narrow:

- prevent overclaiming about the **concrete witness file**
- without understating stronger results established **elsewhere** in the formalization

---

## What "Witnessed by `ConcreteLedgerModel.lean`" Means

A property is **witnessed here** if `ConcreteLedgerModel.lean` contains a proof that a **concrete instantiation** satisfies it.

That buys three things:

1. **Satisfiability** — the relevant package is not contradictory
2. **Realizability** — at least one concrete system satisfies it
3. **Non-vacuity** — the architecture is not empty theater

What it does **not** buy by itself:

- uniqueness
- empirical truth
- completeness — handled in `EpArch/Header.lean`
- safe-extension / no-hidden-degrees-of-freedom — handled in `EpArch/RevisionSafety.lean`
- existence-under-constraints packaging — handled in `EpArch/Feasibility.lean`

---

## Directly Witnessed in `ConcreteLedgerModel.lean`

These are concrete-instance results, not merely abstract theorems.

| Property | Theorem |
|----------|---------|
| Bubbles exist | `concrete_has_bubbles` |
| Trust bridges exist | `concrete_has_trust_bridges` |
| Headers exist (SEV structure) | `concrete_has_headers` |
| Revocation mechanism exists | `concrete_has_revocation` |
| Bank primitive exists | `concrete_has_bank` |
| Redeemability exists | `concrete_has_redeemability` |
| All operational properties satisfied | `concrete_satisfies_all_properties` |
| Well-formedness holds | `concrete_wellformed` |
| Revision traces exist | `concrete_revision_trace_exists'` |
| Self-correction is supported | `concrete_model_supports_self_correction7` |
| SEV factorization exists | `concrete_has_factorization8` |
| Repair path exists | `concrete_has_repair_path8` |
| Withdrawal requires three gates | `concrete_withdrawal_requires_gates` |
| Export requires provenance discipline | `concrete_export_needs_provenance` |
| Headerless states are undiagnosable | `concrete_headerless_undiagnosable` |

---

## Not Witnessed Here, But Established Elsewhere in the Repo

These are real results, but **this file is not where they live**.

| Result | Where established | Notes |
|--------|-------------------|-------|
| World-bundle feasibility | `EpArch.WorldWitness`, `EpArch.Feasibility.world_bundles_feasible` | Witnessed at the world-bundle layer |
| Existence-under-constraints | `EpArch.Feasibility.existence_under_constraints` (original), `existence_under_constraints_structural` (via `StructurallyForced`), `existence_under_constraints_embedding` (via `ForcingEmbedding`) | Packages non-vacuity + success + forced primitives; three forms available |
| Forced-primitives / minimality | `EpArch.Minimality`, `EpArch.Feasibility.goals_force_bank_primitives` | "Success forces Bank primitives" is not a witness-only claim |
| Field-completeness / no hidden DOF | `EpArch.Header` (`observational_completeness_full`) | Type/completeness result, not a concrete witness |
| Safe compatible extension | `EpArch.RevisionSafety` | Repo-level preservation theorem |
| LTS refinement / operational grounding | `EpArch.StepSemantics`, `EpArch.Theorems` | Proved abstractly, not by inspecting one concrete model |
| World assumption bundles (`W_*`) | Premise layer | Assumed, not witnessed |
| Invariants (`C1`–`C8`) | Protocol / spec layer | Requirements, not instantiated here |
| Abstract health-goal necessity | `EpArch.Health`, `EpArch.Mechanisms` | Derived from definitions, not from one concrete model |

---

## Explicitly Out of Scope

Not claimed anywhere in the formalization.

| Property | Reason |
|----------|--------|
| Cryptographic security | Not a cryptographic proof |
| Implementation correctness | Spec ≠ implementation |
| Physical realizability | Formal model only |
| Empirical correspondence | Model ≠ world |
| Optimality | No optimality claim |
| Uniqueness of realization | Multiple realizations may exist |

---

## What the Concrete Witness Buys

At minimum, the concrete witness supports:

```lean
∃ W : WorkingSystem,
  WellFormed W ∧
  SatisfiesAllProperties W
```

At repo level this is packaged more strongly as:

```lean
∃ W : WorkingSystem,
  WellFormed W ∧
  SatisfiesAllProperties W ∧
  containsBankPrimitives W
```

via `EpArch.Feasibility.existence_under_constraints`.

The architecture is **not vacuous**: there is at least one concrete successful instance, and the repo separately proves that success forces Bank primitives.

---

## What This Does Not Mean by Itself

| Non-implication | Why |
|-----------------|-----|
| "All premises are concretely witnessed here" | Some results live in other modules |
| "Completeness is established by the witness file alone" | Completeness is in `Header.lean` |
| "Safe extension is established by the witness file alone" | Preservation is in `RevisionSafety.lean` |
| "The real world literally instantiates this model" | Formal witness ≠ empirical claim |
| "This realization is unique" | Only existence is shown |

---

## Practical Reading Rule

Use this file when the question is:

> "What does the concrete model itself witness?"

Do **not** use this file alone to answer:

> "What stronger repo-wide claims are established about completeness, forced primitives, or safe extension?"

For those, consult:

- `EpArch/Header.lean`
- `EpArch/RevisionSafety.lean`
- `EpArch/Feasibility.lean`
- `README.md`

---

## Audit Commands

```powershell
# List concrete witness theorems
Select-String -Path "EpArch/ConcreteLedgerModel.lean" -Pattern "theorem concrete_"

# Check the packaged repo-level existence theorem
Select-String -Path "EpArch/Feasibility.lean" -Pattern "existence_under_constraints"

# Check field-completeness theorem
Select-String -Path "EpArch/Header.lean" -Pattern "observational_completeness_full"

# Check revision-safety entry points
Select-String -Path "EpArch/RevisionSafety.lean" -Pattern "preserve|compatible|revision"
```
