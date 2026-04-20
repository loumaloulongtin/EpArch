# Witness Scope: What `EpArch/Concrete/` Establishes

This document specifies what is **directly witnessed by the `EpArch/Concrete/` modules** (formerly `ConcreteLedgerModel.lean`, now split into eight files), what is **proved elsewhere in the repo**, and what is **out of scope**.

Its job is narrow:

- prevent overclaiming about the **concrete witness file**
- without understating stronger results established **elsewhere** in the formalization

---

## What "Witnessed by `EpArch/Concrete/`" Means

A property is **witnessed here** if one of the `EpArch/Concrete/` modules contains a proof that a **concrete instantiation** satisfies it.

That buys three things:

1. **Satisfiability** — the relevant package is not contradictory
2. **Realizability** — at least one concrete system satisfies it
3. **Non-vacuity** — the architecture is not empty theater

What it does **not** buy by itself:

- uniqueness
- empirical truth
- completeness — handled in `EpArch/Header.lean`
- safe-extension / no-hidden-degrees-of-freedom — handled in `EpArch/Semantics/RevisionSafety.lean`
- existence-under-constraints packaging — handled in `EpArch/Feasibility.lean`

---

## Directly Witnessed in `EpArch/Concrete/`

These are concrete-instance results, not merely abstract theorems.
They are split across eight modules: `Concrete/Types.lean`, `Concrete/Commitments.lean`,
`Concrete/WorkingSystem.lean`, `Concrete/DeficientSystems.lean`, `Concrete/NonVacuity.lean`,
`Concrete/Realizer.lean`, `Concrete/VerificationDepth.lean`, `Concrete/WorkedTraces.lean`.

| Property | Theorem |
|----------|---------|
| Bubbles exist | `concrete_has_bubbles` |
| Trust bridges exist | `concrete_has_trust_bridges` |
| Headers exist (SEV structure) | `concrete_has_headers` |
| Revocation mechanism exists | `concrete_has_revocation` |
| Bank primitive exists | `concrete_has_bank` |
| Redeemability exists | `concrete_has_redeemability` |
| All operational properties satisfied | `concrete_satisfies_all_properties` |
| Structural forcing holds | `concrete_structurally_forced` |
| Revision traces exist | `concrete_revision_trace_exists'` |
| Self-correction is supported | `concrete_model_supports_self_correction7` |
| SEV factorization exists | `concrete_has_factorization8` |
| Repair path exists | `concrete_has_repair_path8` |
| Withdrawal requires two gates (concrete model: three checks) | `concrete_withdrawal_requires_gates` |
| Export (concrete): requires revalidation or bridge auth | `concrete_export_requires_auth` |
| Headerless states are undiagnosable | `concrete_headerless_undiagnosable` |

---

## Not Witnessed Here, But Established Elsewhere in the Repo

These are real results, but **this file is not where they live**.

| Result | Where established | Notes |
|--------|-------------------|-------|
| World-bundle feasibility | `EpArch.WorldWitness`, `EpArch.Feasibility.world_bundles_feasible` | Witnessed at the world-bundle layer |
| Existence-under-constraints | `existence_under_constraints_structural` (via `StructurallyForced`), `existence_under_constraints_embedding` (via `ForcingEmbedding`), `bundled_structure_forces_bank_primitives` (headline bundled form) | Packages non-vacuity + success + forced primitives; multiple forms available |
| Forced-primitives / minimality | `EpArch.Minimality`, `EpArch.Convergence.convergence_structural`, `bundled_structure_forces_bank_primitives` | "Bank primitives are necessary" is not a witness-only claim |
| Field-completeness / no hidden DOF | `EpArch.Header` (`observational_completeness_full`) | Type/completeness result, not a concrete witness |
| Safe compatible extension | `EpArch.RevisionSafety` | Repo-level preservation theorem |
| LTS refinement / operational grounding | `EpArch.StepSemantics`, `EpArch.Theorems` | Proved abstractly, not by inspecting one concrete model |
| World assumption bundles (`W_*`) | Premise layer | Assumed, not witnessed |
| Invariants (`C1`–`C8`) | Protocol / spec layer | Requirements, not instantiated here |
| Abstract health-goal necessity | `EpArch.Health`, `EpArch.Mechanisms` | Derived from definitions, not from one concrete model |

---

## Adversarial Layer Witnesses (Adversarial/Concrete.lean)

`Adversarial/Concrete.lean` is not in `EpArch/Concrete/` but is the adversarial layer's concrete
witness. It establishes that attack gate conditions fire on concrete type instances.

| Property | Theorem |
|----------|---------|
| τ-expiry blocks concrete withdrawal | `τ_expired_not_withdrawable` |
| V-stripping blocks concrete withdrawal | `V_stripped_not_withdrawable` |
| Header stripping prevents preservation | `E_stripped_diagnosis_lost` |
| DDoS channel collapse produces V = [] | `overwhelmed_channel_collapses_V` |
| DDoS chain blocks concrete withdrawal | `ddos_V_channel_collapse_blocks_withdrawal` |
| `attack_succeeds` is satisfiable | `concrete_attack_succeeds` |
| Export absent reval/bridge is blocked | `missing_export_gate_blocks_import` |

These theorems do not prove the full-stack invariant that a deposit blocked at withdrawal
cannot reach `c_import_deposit`. That requires the caller to check `c_can_withdraw` before
constructing a `CExportRequest`. Enforcing that ordering commits the architecture to one
specific protocol topology (withdrawal-then-export) and would rule out trust-bridge atomic
transfers and delegated export. Invocation order is an agent-layer obligation;
`Adversarial/Concrete.lean` proves the gates are sound, not that an adversary cannot
assemble a request without prior withdrawal.

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
  StructurallyForced W ∧
  SatisfiesAllProperties W
```

At repo level this is packaged more strongly as:

```lean
∃ W : WorkingSystem,
  StructurallyForced W ∧
  SatisfiesAllProperties W ∧
  containsBankPrimitives W
```

via `EpArch.Feasibility.existence_under_constraints_structural`.

The architecture is **not vacuous**: there is at least one concrete successful instance, and the repo separately proves that success forces Bank primitives.

---

## What This Does Not Mean by Itself

| Non-implication | Why |
|-----------------|-----|
| "All premises are concretely witnessed here" | Some results live in other modules |
| "Completeness is established by the witness file alone" | Completeness is in `Header.lean` |
| "Safe extension is established by the witness file alone" | Preservation is in `Semantics/RevisionSafety.lean` |
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
- `EpArch/Semantics/RevisionSafety.lean`
- `EpArch/Feasibility.lean`
- `README.md`

---

## Audit Commands

```powershell
# List concrete witness theorems (now split across Concrete/ modules)
Get-ChildItem -Path "EpArch/Concrete/" -Filter "*.lean" | ForEach-Object {
    Select-String -Path $_.FullName -Pattern "theorem concrete_"
}

# Check the packaged repo-level existence theorem
Select-String -Path "EpArch/Feasibility.lean" -Pattern "existence_under_constraints"

# Check field-completeness theorem
Select-String -Path "EpArch/Header.lean" -Pattern "observational_completeness_full"

# Check revision-safety entry points
Select-String -Path "EpArch/Semantics/RevisionSafety.lean" -Pattern "preserve|compatible|revision"
```
